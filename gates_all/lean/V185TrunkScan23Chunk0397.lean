import V185TrunkScan23Chunk0396

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2347662 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2347662 : Nat := 118140960795 + 2347662 * 2 ^ 59
def prefixEnd_2347662 : Nat := 4983230072969 + 3 ^ 40 * 2347662 * 2
def baseEnd_2347662 : Nat := 1205479020295698995328305

theorem tailTrace_2347662 : CollatzResearch.WordTrace tailWord_2347662 prefixEnd_2347662 1205479020295698995328305 := by
  unfold tailWord_2347662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10703283452603624699193655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57084178413885998395699493 10703283452603624699193655)
  ·
    refine ⟨16054925178905437048790483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10703283452603624699193655 16054925178905437048790483)
    ·
      refine ⟨24082387768358155573185725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16054925178905437048790483 24082387768358155573185725)
      ·
        refine ⟨9030895413134308339944647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24082387768358155573185725 9030895413134308339944647)
        ·
          refine ⟨13546343119701462509916971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9030895413134308339944647 13546343119701462509916971)
          ·
            refine ⟨20319514679552193764875457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13546343119701462509916971 20319514679552193764875457)
            ·
              refine ⟨15239636009664145323656593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20319514679552193764875457 15239636009664145323656593)
              ·
                refine ⟨11429727007248108992742445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15239636009664145323656593 11429727007248108992742445)
                ·
                  refine ⟨4286147627718040872278417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11429727007248108992742445 4286147627718040872278417)
                  ·
                    refine ⟨3214610720788530654208813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4286147627718040872278417 3214610720788530654208813)
                    ·
                      refine ⟨1205479020295698995328305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3214610720788530654208813 1205479020295698995328305)
                      ·
                        rfl

theorem cell23_2347662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2347662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347662 prefixEnd_2347662 := by exact prefixLift 2347662
  have htrace : WordTrace (prefixWord ++ tailWord_2347662) baseStart_2347662 baseEnd_2347662 := by
    simpa [prefixWord, tailWord_2347662, baseEnd_2347662] using wordTrace_append hprefix tailTrace_2347662
  have hstable : (prefixWord ++ tailWord_2347662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347662).length < 2 ^ (prefixWord ++ tailWord_2347662).sum := by decide
  have hdescent : baseEnd_2347662 < baseStart_2347662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347709 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_2347709 : Nat := 118140960795 + 2347709 * 2 ^ 59
def prefixEnd_2347709 : Nat := 4983230072969 + 3 ^ 40 * 2347709 * 2
def baseEnd_2347709 : Nat := 1205503153886460311440589

theorem tailTrace_2347709 : CollatzResearch.WordTrace tailWord_2347709 prefixEnd_2347709 1205503153886460311440589 := by
  unfold tailWord_2347709
  simp only [CollatzResearch.WordTrace]
  refine ⟨85627981851658724620510181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57085321234439149747006787 85627981851658724620510181)
  ·
    refine ⟨16055246597186010866345659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85627981851658724620510181 16055246597186010866345659)
    ·
      refine ⟨24082869895779016299518489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16055246597186010866345659 24082869895779016299518489)
      ·
        refine ⟨18062152421834262224638867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24082869895779016299518489 18062152421834262224638867)
        ·
          refine ⟨27093228632751393336958301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18062152421834262224638867 27093228632751393336958301)
          ·
            refine ⟨10159960737281772501359363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27093228632751393336958301 10159960737281772501359363)
            ·
              refine ⟨15239941105922658752039045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10159960737281772501359363 15239941105922658752039045)
              ·
                refine ⟨2857488957360498516007321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15239941105922658752039045 2857488957360498516007321)
                ·
                  refine ⟨2143116718020373887005491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2857488957360498516007321 2143116718020373887005491)
                  ·
                    refine ⟨3214675077030560830508237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2143116718020373887005491 3214675077030560830508237)
                    ·
                      refine ⟨1205503153886460311440589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3214675077030560830508237 1205503153886460311440589)
                      ·
                        rfl

theorem cell23_2347709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_2347709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347709 prefixEnd_2347709 := by exact prefixLift 2347709
  have htrace : WordTrace (prefixWord ++ tailWord_2347709) baseStart_2347709 baseEnd_2347709 := by
    simpa [prefixWord, tailWord_2347709, baseEnd_2347709] using wordTrace_append hprefix tailTrace_2347709
  have hstable : (prefixWord ++ tailWord_2347709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347709).length < 2 ^ (prefixWord ++ tailWord_2347709).sum := by decide
  have hdescent : baseEnd_2347709 < baseStart_2347709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347749 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 1, 4, 2]
def baseStart_2347749 : Nat := 118140960795 + 2347749 * 2 ^ 59
def prefixEnd_2347749 : Nat := 4983230072969 + 3 ^ 40 * 2347749 * 2
def baseEnd_2347749 : Nat := 1205523693112640154940405

theorem tailTrace_2347749 : CollatzResearch.WordTrace tailWord_2347749 prefixEnd_2347749 1205523693112640154940405 := by
  unfold tailWord_2347749
  simp only [CollatzResearch.WordTrace]
  refine ⟨85629440771513811451966301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57086293847675874301310867 85629440771513811451966301)
  ·
    refine ⟨32111040289317679294487363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85629440771513811451966301 32111040289317679294487363)
    ·
      refine ⟨48166560433976518941731045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32111040289317679294487363 48166560433976518941731045)
      ·
        refine ⟨9031230081370597301574571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48166560433976518941731045 9031230081370597301574571)
        ·
          refine ⟨13546845122055895952361857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9031230081370597301574571 13546845122055895952361857)
          ·
            refine ⟨10160133841541921964271393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13546845122055895952361857 10160133841541921964271393)
            ·
              refine ⟨7620100381156441473203545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10160133841541921964271393 7620100381156441473203545)
              ·
                refine ⟨5715075285867331104902659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7620100381156441473203545 5715075285867331104902659)
                ·
                  refine ⟨8572612928800996657353989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715075285867331104902659 8572612928800996657353989)
                  ·
                    refine ⟨1607364924150186873253873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8572612928800996657353989 1607364924150186873253873)
                    ·
                      refine ⟨1205523693112640154940405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607364924150186873253873 1205523693112640154940405)
                      ·
                        rfl

theorem cell23_2347749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_2347749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347749 prefixEnd_2347749 := by exact prefixLift 2347749
  have htrace : WordTrace (prefixWord ++ tailWord_2347749) baseStart_2347749 baseEnd_2347749 := by
    simpa [prefixWord, tailWord_2347749, baseEnd_2347749] using wordTrace_append hprefix tailTrace_2347749
  have hstable : (prefixWord ++ tailWord_2347749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347749).length < 2 ^ (prefixWord ++ tailWord_2347749).sum := by decide
  have hdescent : baseEnd_2347749 < baseStart_2347749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347762 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2347762 : Nat := 118140960795 + 2347762 * 2 ^ 59
def prefixEnd_2347762 : Nat := 4983230072969 + 3 ^ 40 * 2347762 * 2
def baseEnd_2347762 : Nat := 1205530368361148604077845

theorem tailTrace_2347762 : CollatzResearch.WordTrace tailWord_2347762 prefixEnd_2347762 1205530368361148604077845 := by
  unfold tailWord_2347762
  simp only [CollatzResearch.WordTrace]
  refine ⟨21407478730116678668047385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57086609946977809781459693 21407478730116678668047385)
  ·
    refine ⟨16055609047587509001035539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21407478730116678668047385 16055609047587509001035539)
    ·
      refine ⟨24083413571381263501553309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16055609047587509001035539 24083413571381263501553309)
      ·
        refine ⟨9031280089267973813082491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24083413571381263501553309 9031280089267973813082491)
        ·
          refine ⟨13546920133901960719623737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9031280089267973813082491 13546920133901960719623737)
          ·
            refine ⟨10160190100426470539717803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13546920133901960719623737 10160190100426470539717803)
            ·
              refine ⟨15240285150639705809576705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10160190100426470539717803 15240285150639705809576705)
              ·
                refine ⟨11430213862979779357182529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15240285150639705809576705 11430213862979779357182529)
                ·
                  refine ⟨8572660397234834517886897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11430213862979779357182529 8572660397234834517886897)
                  ·
                    refine ⟨6429495297926125888415173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8572660397234834517886897 6429495297926125888415173)
                    ·
                      refine ⟨1205530368361148604077845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6429495297926125888415173 1205530368361148604077845)
                      ·
                        rfl

theorem cell23_2347762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2347762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347762 prefixEnd_2347762 := by exact prefixLift 2347762
  have htrace : WordTrace (prefixWord ++ tailWord_2347762) baseStart_2347762 baseEnd_2347762 := by
    simpa [prefixWord, tailWord_2347762, baseEnd_2347762] using wordTrace_append hprefix tailTrace_2347762
  have hstable : (prefixWord ++ tailWord_2347762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347762).length < 2 ^ (prefixWord ++ tailWord_2347762).sum := by decide
  have hdescent : baseEnd_2347762 < baseStart_2347762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347766 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_2347766 : Nat := 118140960795 + 2347766 * 2 ^ 59
def prefixEnd_2347766 : Nat := 4983230072969 + 3 ^ 40 * 2347766 * 2
def baseEnd_2347766 : Nat := 1205532422283766588427827

theorem tailTrace_2347766 : CollatzResearch.WordTrace tailWord_2347766 prefixEnd_2347766 1205532422283766588427827 := by
  unfold tailWord_2347766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5351878800778263959708447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57086707208301482236890101 5351878800778263959708447)
  ·
    refine ⟨8027818201167395939562671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5351878800778263959708447 8027818201167395939562671)
    ·
      refine ⟨12041727301751093909344007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8027818201167395939562671 12041727301751093909344007)
      ·
        refine ⟨18062590952626640864016011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12041727301751093909344007 18062590952626640864016011)
        ·
          refine ⟨27093886428939961296024017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18062590952626640864016011 27093886428939961296024017)
          ·
            refine ⟨20320414821704970972018013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27093886428939961296024017 20320414821704970972018013)
            ·
              refine ⟨7620155558139364114506755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20320414821704970972018013 7620155558139364114506755)
              ·
                refine ⟨11430233337209046171760133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7620155558139364114506755 11430233337209046171760133)
                ·
                  refine ⟨2143168750726696157205025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11430233337209046171760133 2143168750726696157205025)
                  ·
                    refine ⟨1607376563045022117903769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2143168750726696157205025 1607376563045022117903769)
                    ·
                      refine ⟨1205532422283766588427827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607376563045022117903769 1205532422283766588427827)
                      ·
                        rfl

theorem cell23_2347766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_2347766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347766 prefixEnd_2347766 := by exact prefixLift 2347766
  have htrace : WordTrace (prefixWord ++ tailWord_2347766) baseStart_2347766 baseEnd_2347766 := by
    simpa [prefixWord, tailWord_2347766, baseEnd_2347766] using wordTrace_append hprefix tailTrace_2347766
  have hstable : (prefixWord ++ tailWord_2347766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347766).length < 2 ^ (prefixWord ++ tailWord_2347766).sum := by decide
  have hdescent : baseEnd_2347766 < baseStart_2347766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347772 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 7]
def baseStart_2347772 : Nat := 118140960795 + 2347772 * 2 ^ 59
def prefixEnd_2347772 : Nat := 4983230072969 + 3 ^ 40 * 2347772 * 2
def baseEnd_2347772 : Nat := 133948389240854840550311

theorem tailTrace_2347772 : CollatzResearch.WordTrace tailWord_2347772 prefixEnd_2347772 133948389240854840550311 := by
  unfold tailWord_2347772
  simp only [CollatzResearch.WordTrace]
  refine ⟨42815139825215243190026785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57086853100286990920035713 42815139825215243190026785)
  ·
    refine ⟨32111354868911432392520089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42815139825215243190026785 32111354868911432392520089)
    ·
      refine ⟨24083516151683574294390067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32111354868911432392520089 24083516151683574294390067)
      ·
        refine ⟨36125274227525361441585101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24083516151683574294390067 36125274227525361441585101)
        ·
          refine ⟨13546977835322010540594413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36125274227525361441585101 13546977835322010540594413)
          ·
            refine ⟨5080116688245753952722905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13546977835322010540594413 5080116688245753952722905)
            ·
              refine ⟨3810087516184315464542179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5080116688245753952722905 3810087516184315464542179)
              ·
                refine ⟨5715131274276473196813269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810087516184315464542179 5715131274276473196813269)
                ·
                  refine ⟨133948389240854840550311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5715131274276473196813269 133948389240854840550311)
                  ·
                    rfl

theorem cell23_2347772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_2347772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347772 prefixEnd_2347772 := by exact prefixLift 2347772
  have htrace : WordTrace (prefixWord ++ tailWord_2347772) baseStart_2347772 baseEnd_2347772 := by
    simpa [prefixWord, tailWord_2347772, baseEnd_2347772] using wordTrace_append hprefix tailTrace_2347772
  have hstable : (prefixWord ++ tailWord_2347772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347772).length < 2 ^ (prefixWord ++ tailWord_2347772).sum := by decide
  have hdescent : baseEnd_2347772 < baseStart_2347772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347785 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 1, 7]
def baseStart_2347785 : Nat := 118140960795 + 2347785 * 2 ^ 59
def prefixEnd_2347785 : Nat := 4983230072969 + 3 ^ 40 * 2347785 * 2
def baseEnd_2347785 : Nat := 401847392805400671363413

theorem tailTrace_2347785 : CollatzResearch.WordTrace tailWord_2347785 prefixEnd_2347785 401847392805400671363413 := by
  unfold tailWord_2347785
  simp only [CollatzResearch.WordTrace]
  refine ⟨85630753799383389600276809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57087169199588926400184539 85630753799383389600276809)
  ·
    refine ⟨64223065349537542200207607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85630753799383389600276809 64223065349537542200207607)
    ·
      refine ⟨96334598024306313300311411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64223065349537542200207607 96334598024306313300311411)
      ·
        refine ⟨144501897036459469950467117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96334598024306313300311411 144501897036459469950467117)
        ·
          refine ⟨54188211388672301231425169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144501897036459469950467117 54188211388672301231425169)
          ·
            refine ⟨40641158541504225923568877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54188211388672301231425169 40641158541504225923568877)
            ·
              refine ⟨15240434453064084721338329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40641158541504225923568877 15240434453064084721338329)
              ·
                refine ⟨11430325839798063541003747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15240434453064084721338329 11430325839798063541003747)
                ·
                  refine ⟨17145488759697095311505621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11430325839798063541003747 17145488759697095311505621)
                  ·
                    refine ⟨401847392805400671363413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17145488759697095311505621 401847392805400671363413)
                    ·
                      rfl

theorem cell23_2347785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_2347785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347785 prefixEnd_2347785 := by exact prefixLift 2347785
  have htrace : WordTrace (prefixWord ++ tailWord_2347785) baseStart_2347785 baseEnd_2347785 := by
    simpa [prefixWord, tailWord_2347785, baseEnd_2347785] using wordTrace_append hprefix tailTrace_2347785
  have hstable : (prefixWord ++ tailWord_2347785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347785).length < 2 ^ (prefixWord ++ tailWord_2347785).sum := by decide
  have hdescent : baseEnd_2347785 < baseStart_2347785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347802 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_2347802 : Nat := 118140960795 + 2347802 * 2 ^ 59
def prefixEnd_2347802 : Nat := 4983230072969 + 3 ^ 40 * 2347802 * 2
def baseEnd_2347802 : Nat := 401850302529109482525887

theorem tailTrace_2347802 : CollatzResearch.WordTrace tailWord_2347802 prefixEnd_2347802 401850302529109482525887 := by
  unfold tailWord_2347802
  simp only [CollatzResearch.WordTrace]
  refine ⟨21407843460080450375911415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57087582560214534335763773 21407843460080450375911415)
  ·
    refine ⟨32111765190120675563867123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21407843460080450375911415 32111765190120675563867123)
    ·
      refine ⟨48167647785181013345800685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32111765190120675563867123 48167647785181013345800685)
      ·
        refine ⟨18062867919442880004675257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48167647785181013345800685 18062867919442880004675257)
        ·
          refine ⟨13547150939582160003506443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18062867919442880004675257 13547150939582160003506443)
          ·
            refine ⟨20320726409373240005259665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13547150939582160003506443 20320726409373240005259665)
            ·
              refine ⟨15240544807029930003944749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20320726409373240005259665 15240544807029930003944749)
              ·
                refine ⟨5715204302636223751479281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15240544807029930003944749 5715204302636223751479281)
                ·
                  refine ⟨4286403226977167813609461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5715204302636223751479281 4286403226977167813609461)
                  ·
                    refine ⟨401850302529109482525887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4286403226977167813609461 401850302529109482525887)
                    ·
                      rfl

theorem cell23_2347802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_2347802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347802 prefixEnd_2347802 := by exact prefixLift 2347802
  have htrace : WordTrace (prefixWord ++ tailWord_2347802) baseStart_2347802 baseEnd_2347802 := by
    simpa [prefixWord, tailWord_2347802, baseEnd_2347802] using wordTrace_append hprefix tailTrace_2347802
  have hstable : (prefixWord ++ tailWord_2347802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347802).length < 2 ^ (prefixWord ++ tailWord_2347802).sum := by decide
  have hdescent : baseEnd_2347802 < baseStart_2347802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347845 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 10]
def baseStart_2347845 : Nat := 118140960795 + 2347845 * 2 ^ 59
def prefixEnd_2347845 : Nat := 4983230072969 + 3 ^ 40 * 2347845 * 2
def baseEnd_2347845 : Nat := 133952554139496864371107

theorem tailTrace_2347845 : CollatzResearch.WordTrace tailWord_2347845 prefixEnd_2347845 133952554139496864371107 := by
  unfold tailWord_2347845
  simp only [CollatzResearch.WordTrace]
  refine ⟨85632942179166019847460989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57088628119444013231640659 85632942179166019847460989)
  ·
    refine ⟨32112353317187257442797871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85632942179166019847460989 32112353317187257442797871)
    ·
      refine ⟨48168529975780886164196807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32112353317187257442797871 48168529975780886164196807)
      ·
        refine ⟨72252794963671329246295211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48168529975780886164196807 72252794963671329246295211)
        ·
          refine ⟨108379192445506993869442817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72252794963671329246295211 108379192445506993869442817)
          ·
            refine ⟨81284394334130245402082113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108379192445506993869442817 81284394334130245402082113)
            ·
              refine ⟨60963295750597684051561585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81284394334130245402082113 60963295750597684051561585)
              ·
                refine ⟨45722471812948263038671189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60963295750597684051561585 45722471812948263038671189)
                ·
                  refine ⟨133952554139496864371107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 45722471812948263038671189 133952554139496864371107)
                  ·
                    rfl

theorem cell23_2347845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_2347845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347845 prefixEnd_2347845 := by exact prefixLift 2347845
  have htrace : WordTrace (prefixWord ++ tailWord_2347845) baseStart_2347845 baseEnd_2347845 := by
    simpa [prefixWord, tailWord_2347845, baseEnd_2347845] using wordTrace_append hprefix tailTrace_2347845
  have hstable : (prefixWord ++ tailWord_2347845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347845).length < 2 ^ (prefixWord ++ tailWord_2347845).sum := by decide
  have hdescent : baseEnd_2347845 < baseStart_2347845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347879 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 6]
def baseStart_2347879 : Nat := 118140960795 + 2347879 * 2 ^ 59
def prefixEnd_2347879 : Nat := 4983230072969 + 3 ^ 40 * 2347879 * 2
def baseEnd_2347879 : Nat := 133954493955302738479423

theorem tailTrace_2347879 : CollatzResearch.WordTrace tailWord_2347879 prefixEnd_2347879 133954493955302738479423 := by
  unfold tailWord_2347879
  simp only [CollatzResearch.WordTrace]
  refine ⟨85634182261042843654198691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57089454840695229102799127 85634182261042843654198691)
  ·
    refine ⟨128451273391564265481298037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85634182261042843654198691 128451273391564265481298037)
    ·
      refine ⟨12042306880459149888871691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128451273391564265481298037 12042306880459149888871691)
      ·
        refine ⟨18063460320688724833307537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12042306880459149888871691 18063460320688724833307537)
        ·
          refine ⟨13547595240516543624980653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18063460320688724833307537 13547595240516543624980653)
          ·
            refine ⟨5080348215193703859367745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13547595240516543624980653 5080348215193703859367745)
            ·
              refine ⟨3810261161395277894525809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5080348215193703859367745 3810261161395277894525809)
              ·
                refine ⟨2857695871046458420894357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3810261161395277894525809 2857695871046458420894357)
                ·
                  refine ⟨133954493955302738479423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2857695871046458420894357 133954493955302738479423)
                  ·
                    rfl

theorem cell23_2347879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 6].length) (baseStart_2347879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347879 prefixEnd_2347879 := by exact prefixLift 2347879
  have htrace : WordTrace (prefixWord ++ tailWord_2347879) baseStart_2347879 baseEnd_2347879 := by
    simpa [prefixWord, tailWord_2347879, baseEnd_2347879] using wordTrace_append hprefix tailTrace_2347879
  have hstable : (prefixWord ++ tailWord_2347879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347879).length < 2 ^ (prefixWord ++ tailWord_2347879).sum := by decide
  have hdescent : baseEnd_2347879 < baseStart_2347879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347899 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 4, 3, 2]
def baseStart_2347899 : Nat := 118140960795 + 2347899 * 2 ^ 59
def prefixEnd_2347899 : Nat := 4983230072969 + 3 ^ 40 * 2347899 * 2
def baseEnd_2347899 : Nat := 1205600715210814568064715

theorem tailTrace_2347899 : CollatzResearch.WordTrace tailWord_2347899 prefixEnd_2347899 1205600715210814568064715 := by
  unfold tailWord_2347899
  simp only [CollatzResearch.WordTrace]
  refine ⟨85634911720970387069926751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57089941147313591379951167 85634911720970387069926751)
  ·
    refine ⟨128452367581455580604890127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85634911720970387069926751 128452367581455580604890127)
    ·
      refine ⟨192678551372183370907335191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128452367581455580604890127 192678551372183370907335191)
      ·
        refine ⟨289017827058275056361002787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192678551372183370907335191 289017827058275056361002787)
        ·
          refine ⟨433526740587412584541504181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289017827058275056361002787 433526740587412584541504181)
          ·
            refine ⟨40643131930069929800766017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 433526740587412584541504181 40643131930069929800766017)
            ·
              refine ⟨30482348947552447350574513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40643131930069929800766017 30482348947552447350574513)
              ·
                refine ⟨22861761710664335512930885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30482348947552447350574513 22861761710664335512930885)
                ·
                  refine ⟨4286580320749562908674541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22861761710664335512930885 4286580320749562908674541)
                  ·
                    refine ⟨1607467620281086090752953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4286580320749562908674541 1607467620281086090752953)
                    ·
                      refine ⟨1205600715210814568064715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607467620281086090752953 1205600715210814568064715)
                      ·
                        rfl

theorem cell23_2347899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 3, 2].length) (baseStart_2347899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347899 prefixEnd_2347899 := by exact prefixLift 2347899
  have htrace : WordTrace (prefixWord ++ tailWord_2347899) baseStart_2347899 baseEnd_2347899 := by
    simpa [prefixWord, tailWord_2347899, baseEnd_2347899] using wordTrace_append hprefix tailTrace_2347899
  have hstable : (prefixWord ++ tailWord_2347899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347899).length < 2 ^ (prefixWord ++ tailWord_2347899).sum := by decide
  have hdescent : baseEnd_2347899 < baseStart_2347899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347916 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 2, 3, 2]
def baseStart_2347916 : Nat := 118140960795 + 2347916 * 2 ^ 59
def prefixEnd_2347916 : Nat := 4983230072969 + 3 ^ 40 * 2347916 * 2
def baseEnd_2347916 : Nat := 1205609444381941001552137

theorem tailTrace_2347916 : CollatzResearch.WordTrace tailWord_2347916 prefixEnd_2347916 1205609444381941001552137 := by
  unfold tailWord_2347916
  simp only [CollatzResearch.WordTrace]
  refine ⟨42817765880954399486647801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57090354507939199315530401 42817765880954399486647801)
  ·
    refine ⟨32113324410715799614985851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42817765880954399486647801 32113324410715799614985851)
    ·
      refine ⟨48169986616073699422478777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32113324410715799614985851 48169986616073699422478777)
      ·
        refine ⟨36127489962055274566859083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48169986616073699422478777 36127489962055274566859083)
        ·
          refine ⟨54191234943082911850288625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36127489962055274566859083 54191234943082911850288625)
          ·
            refine ⟨40643426207312183887716469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54191234943082911850288625 40643426207312183887716469)
            ·
              refine ⟨3810321206935517239473419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40643426207312183887716469 3810321206935517239473419)
              ·
                refine ⟨5715481810403275859210129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810321206935517239473419 5715481810403275859210129)
                ·
                  refine ⟨4286611357802456894407597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5715481810403275859210129 4286611357802456894407597)
                  ·
                    refine ⟨1607479259175921335402849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4286611357802456894407597 1607479259175921335402849)
                    ·
                      refine ⟨1205609444381941001552137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607479259175921335402849 1205609444381941001552137)
                      ·
                        rfl

theorem cell23_2347916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_2347916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347916 prefixEnd_2347916 := by exact prefixLift 2347916
  have htrace : WordTrace (prefixWord ++ tailWord_2347916) baseStart_2347916 baseEnd_2347916 := by
    simpa [prefixWord, tailWord_2347916, baseEnd_2347916] using wordTrace_append hprefix tailTrace_2347916
  have hstable : (prefixWord ++ tailWord_2347916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347916).length < 2 ^ (prefixWord ++ tailWord_2347916).sum := by decide
  have hdescent : baseEnd_2347916 < baseStart_2347916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347959 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 4]
def baseStart_2347959 : Nat := 118140960795 + 2347959 * 2 ^ 59
def prefixEnd_2347959 : Nat := 4983230072969 + 3 ^ 40 * 2347959 * 2
def baseEnd_2347959 : Nat := 1205631524050084333314439

theorem tailTrace_2347959 : CollatzResearch.WordTrace tailWord_2347959 prefixEnd_2347959 1205631524050084333314439 := by
  unfold tailWord_2347959
  simp only [CollatzResearch.WordTrace]
  refine ⟨85637100100753017317110931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57091400067168678211407287 85637100100753017317110931)
  ·
    refine ⟨128455650151129525975666397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85637100100753017317110931 128455650151129525975666397)
    ·
      refine ⟨48170868806673572240874899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128455650151129525975666397 48170868806673572240874899)
      ·
        refine ⟨72256303210010358361312349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48170868806673572240874899 72256303210010358361312349)
        ·
          refine ⟨27096113703753884385492131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72256303210010358361312349 27096113703753884385492131)
          ·
            refine ⟨40644170555630826578238197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27096113703753884385492131 40644170555630826578238197)
            ·
              refine ⟨3810390989590389991709831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40644170555630826578238197 3810390989590389991709831)
              ·
                refine ⟨5715586484385584987564747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810390989590389991709831 5715586484385584987564747)
                ·
                  refine ⟨8573379726578377481347121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715586484385584987564747 8573379726578377481347121)
                  ·
                    refine ⟨6430034794933783111010341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8573379726578377481347121 6430034794933783111010341)
                    ·
                      refine ⟨1205631524050084333314439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6430034794933783111010341 1205631524050084333314439)
                      ·
                        rfl

theorem cell23_2347959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_2347959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347959 prefixEnd_2347959 := by exact prefixLift 2347959
  have htrace : WordTrace (prefixWord ++ tailWord_2347959) baseStart_2347959 baseEnd_2347959 := by
    simpa [prefixWord, tailWord_2347959, baseEnd_2347959] using wordTrace_append hprefix tailTrace_2347959
  have hstable : (prefixWord ++ tailWord_2347959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347959).length < 2 ^ (prefixWord ++ tailWord_2347959).sum := by decide
  have hdescent : baseEnd_2347959 < baseStart_2347959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348032 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_2348032 : Nat := 118140960795 + 2348032 * 2 ^ 59
def prefixEnd_2348032 : Nat := 4983230072969 + 3 ^ 40 * 2348032 * 2
def baseEnd_2348032 : Nat := 1205669008137862547701603

theorem tailTrace_2348032 : CollatzResearch.WordTrace tailWord_2348032 prefixEnd_2348032 1205669008137862547701603 := by
  unfold tailWord_2348032
  simp only [CollatzResearch.WordTrace]
  refine ⟨42819881314744275392259175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57093175086325700523012233 42819881314744275392259175)
  ·
    refine ⟨64229821972116413088388763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42819881314744275392259175 64229821972116413088388763)
    ·
      refine ⟨96344732958174619632583145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64229821972116413088388763 96344732958174619632583145)
      ·
        refine ⟨72258549718630964724437359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96344732958174619632583145 72258549718630964724437359)
        ·
          refine ⟨108387824577946447086656039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72258549718630964724437359 108387824577946447086656039)
          ·
            refine ⟨162581736866919670629984059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108387824577946447086656039 162581736866919670629984059)
            ·
              refine ⟨243872605300379505944976089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162581736866919670629984059 243872605300379505944976089)
              ·
                refine ⟨182904453975284629458732067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243872605300379505944976089 182904453975284629458732067)
                ·
                  refine ⟨274356680962926944188098101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182904453975284629458732067 274356680962926944188098101)
                  ·
                    refine ⟨25720938840274401017634197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 274356680962926944188098101 25720938840274401017634197)
                    ·
                      refine ⟨1205669008137862547701603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25720938840274401017634197 1205669008137862547701603)
                      ·
                        rfl

theorem cell23_2348032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_2348032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348032 prefixEnd_2348032 := by exact prefixLift 2348032
  have htrace : WordTrace (prefixWord ++ tailWord_2348032) baseStart_2348032 baseEnd_2348032 := by
    simpa [prefixWord, tailWord_2348032, baseEnd_2348032] using wordTrace_append hprefix tailTrace_2348032
  have hstable : (prefixWord ++ tailWord_2348032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348032).length < 2 ^ (prefixWord ++ tailWord_2348032).sum := by decide
  have hdescent : baseEnd_2348032 < baseStart_2348032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348039 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2348039 : Nat := 118140960795 + 2348039 * 2 ^ 59
def prefixEnd_2348039 : Nat := 4983230072969 + 3 ^ 40 * 2348039 * 2
def baseEnd_2348039 : Nat := 1205672602502444020314071

theorem tailTrace_2348039 : CollatzResearch.WordTrace tailWord_2348039 prefixEnd_2348039 1205672602502444020314071 := by
  unfold tailWord_2348039
  simp only [CollatzResearch.WordTrace]
  refine ⟨85640017940463190980023171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57093345293642127320015447 85640017940463190980023171)
  ·
    refine ⟨128460026910694786470034757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85640017940463190980023171 128460026910694786470034757)
    ·
      refine ⟨24086255045755272463131517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128460026910694786470034757 24086255045755272463131517)
      ·
        refine ⟨9032345642158227173674319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24086255045755272463131517 9032345642158227173674319)
        ·
          refine ⟨13548518463237340760511479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9032345642158227173674319 13548518463237340760511479)
          ·
            refine ⟨20322777694856011140767219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13548518463237340760511479 20322777694856011140767219)
            ·
              refine ⟨30484166542284016711150829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20322777694856011140767219 30484166542284016711150829)
              ·
                refine ⟨11431562453356506266681561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30484166542284016711150829 11431562453356506266681561)
                ·
                  refine ⟨8573671840017379700011171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11431562453356506266681561 8573671840017379700011171)
                  ·
                    refine ⟨12860507760026069550016757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8573671840017379700011171 12860507760026069550016757)
                    ·
                      refine ⟨1205672602502444020314071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12860507760026069550016757 1205672602502444020314071)
                      ·
                        rfl

theorem cell23_2348039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2348039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348039 prefixEnd_2348039 := by exact prefixLift 2348039
  have htrace : WordTrace (prefixWord ++ tailWord_2348039) baseStart_2348039 baseEnd_2348039 := by
    simpa [prefixWord, tailWord_2348039, baseEnd_2348039] using wordTrace_append hprefix tailTrace_2348039
  have hstable : (prefixWord ++ tailWord_2348039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348039).length < 2 ^ (prefixWord ++ tailWord_2348039).sum := by decide
  have hdescent : baseEnd_2348039 < baseStart_2348039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348040 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 1, 3, 2]
def baseStart_2348040 : Nat := 118140960795 + 2348040 * 2 ^ 59
def prefixEnd_2348040 : Nat := 4983230072969 + 3 ^ 40 * 2348040 * 2
def baseEnd_2348040 : Nat := 1205673115983098516401567

theorem tailTrace_2348040 : CollatzResearch.WordTrace tailWord_2348040 prefixEnd_2348040 1205673115983098516401567 := by
  unfold tailWord_2348040
  simp only [CollatzResearch.WordTrace]
  refine ⟨42820027206729784075404787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57093369608973045433873049 42820027206729784075404787)
  ·
    refine ⟨64230040810094676113107181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42820027206729784075404787 64230040810094676113107181)
    ·
      refine ⟨24086265303785503542415193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64230040810094676113107181 24086265303785503542415193)
      ·
        refine ⟨18064698977839127656811395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24086265303785503542415193 18064698977839127656811395)
        ·
          refine ⟨27097048466758691485217093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18064698977839127656811395 27097048466758691485217093)
          ·
            refine ⟨5080696587517254653478205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27097048466758691485217093 5080696587517254653478205)
            ·
              refine ⟨1905261220318970495054327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5080696587517254653478205 1905261220318970495054327)
              ·
                refine ⟨2857891830478455742581491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905261220318970495054327 2857891830478455742581491)
                ·
                  refine ⟨4286837745717683613872237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2857891830478455742581491 4286837745717683613872237)
                  ·
                    refine ⟨1607564154644131355202089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4286837745717683613872237 1607564154644131355202089)
                    ·
                      refine ⟨1205673115983098516401567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607564154644131355202089 1205673115983098516401567)
                      ·
                        rfl

theorem cell23_2348040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_2348040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348040 prefixEnd_2348040 := by exact prefixLift 2348040
  have htrace : WordTrace (prefixWord ++ tailWord_2348040) baseStart_2348040 baseEnd_2348040 := by
    simpa [prefixWord, tailWord_2348040, baseEnd_2348040] using wordTrace_append hprefix tailTrace_2348040
  have hstable : (prefixWord ++ tailWord_2348040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348040).length < 2 ^ (prefixWord ++ tailWord_2348040).sum := by decide
  have hdescent : baseEnd_2348040 < baseStart_2348040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348066 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_2348066 : Nat := 118140960795 + 2348066 * 2 ^ 59
def prefixEnd_2348066 : Nat := 4983230072969 + 3 ^ 40 * 2348066 * 2
def baseEnd_2348066 : Nat := 1205686466480115414676447

theorem tailTrace_2348066 : CollatzResearch.WordTrace tailWord_2348066 prefixEnd_2348066 1205686466480115414676447 := by
  unfold tailWord_2348066
  simp only [CollatzResearch.WordTrace]
  refine ⟨21410250677841343647814013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57094001807576916394170701 21410250677841343647814013)
  ·
    refine ⟨8028844004190503867930255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21410250677841343647814013 8028844004190503867930255)
    ·
      refine ⟨12043266006285755801895383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8028844004190503867930255 12043266006285755801895383)
      ·
        refine ⟨18064899009428633702843075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12043266006285755801895383 18064899009428633702843075)
        ·
          refine ⟨27097348514142950554264613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18064899009428633702843075 27097348514142950554264613)
          ·
            refine ⟨5080752846401803228924615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27097348514142950554264613 5080752846401803228924615)
            ·
              refine ⟨7621129269602704843386923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5080752846401803228924615 7621129269602704843386923)
              ·
                refine ⟨11431693904404057265080385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7621129269602704843386923 11431693904404057265080385)
                ·
                  refine ⟨8573770428303042948810289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11431693904404057265080385 8573770428303042948810289)
                  ·
                    refine ⟨6430327821227282211607717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8573770428303042948810289 6430327821227282211607717)
                    ·
                      refine ⟨1205686466480115414676447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6430327821227282211607717 1205686466480115414676447)
                      ·
                        rfl

theorem cell23_2348066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_2348066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348066 prefixEnd_2348066 := by exact prefixLift 2348066
  have htrace : WordTrace (prefixWord ++ tailWord_2348066) baseStart_2348066 baseEnd_2348066 := by
    simpa [prefixWord, tailWord_2348066, baseEnd_2348066] using wordTrace_append hprefix tailTrace_2348066
  have hstable : (prefixWord ++ tailWord_2348066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348066).length < 2 ^ (prefixWord ++ tailWord_2348066).sum := by decide
  have hdescent : baseEnd_2348066 < baseStart_2348066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348093 : List Nat := [1, 4, 1, 3, 1, 3, 2, 3, 5]
def baseStart_2348093 : Nat := 118140960795 + 2348093 * 2 ^ 59
def prefixEnd_2348093 : Nat := 4983230072969 + 3 ^ 40 * 2348093 * 2
def baseEnd_2348093 : Nat := 133966703384198534337647

theorem tailTrace_2348093 : CollatzResearch.WordTrace tailWord_2348093 prefixEnd_2348093 133966703384198534337647 := by
  unfold tailWord_2348093
  simp only [CollatzResearch.WordTrace]
  refine ⟨85641987482267558202488933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57094658321511705468325955 85641987482267558202488933)
  ·
    refine ⟨16057872652925167162966675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85641987482267558202488933 16057872652925167162966675)
    ·
      refine ⟨24086808979387750744450013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16057872652925167162966675 24086808979387750744450013)
      ·
        refine ⟨9032553367270406529168755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24086808979387750744450013 9032553367270406529168755)
        ·
          refine ⟨13548830050905609793753133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9032553367270406529168755 13548830050905609793753133)
          ·
            refine ⟨5080811269089603672657425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13548830050905609793753133 5080811269089603672657425)
            ·
              refine ⟨3810608451817202754493069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5080811269089603672657425 3810608451817202754493069)
              ·
                refine ⟨1428978169431451032934901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3810608451817202754493069 1428978169431451032934901)
                ·
                  refine ⟨133966703384198534337647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1428978169431451032934901 133966703384198534337647)
                  ·
                    rfl

theorem cell23_2348093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_2348093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348093 prefixEnd_2348093 := by exact prefixLift 2348093
  have htrace : WordTrace (prefixWord ++ tailWord_2348093) baseStart_2348093 baseEnd_2348093 := by
    simpa [prefixWord, tailWord_2348093, baseEnd_2348093] using wordTrace_append hprefix tailTrace_2348093
  have hstable : (prefixWord ++ tailWord_2348093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348093).length < 2 ^ (prefixWord ++ tailWord_2348093).sum := by decide
  have hdescent : baseEnd_2348093 < baseStart_2348093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348146 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2348146 : Nat := 118140960795 + 2348146 * 2 ^ 59
def prefixEnd_2348146 : Nat := 4983230072969 + 3 ^ 40 * 2348146 * 2
def baseEnd_2348146 : Nat := 1205727544932475101676079

theorem tailTrace_2348146 : CollatzResearch.WordTrace tailWord_2348146 prefixEnd_2348146 1205727544932475101676079 := by
  unfold tailWord_2348146
  simp only [CollatzResearch.WordTrace]
  refine ⟨21410980137768887063542073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57095947034050365502778861 21410980137768887063542073)
  ·
    refine ⟨16058235103326665297656555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21410980137768887063542073 16058235103326665297656555)
    ·
      refine ⟨24087352654989997946484833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16058235103326665297656555 24087352654989997946484833)
      ·
        refine ⟨18065514491242498459863625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24087352654989997946484833 18065514491242498459863625)
        ·
          refine ⟨13549135868431873844897719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18065514491242498459863625 13549135868431873844897719)
          ·
            refine ⟨20323703802647810767346579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13549135868431873844897719 20323703802647810767346579)
            ·
              refine ⟨30485555703971716151019869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20323703802647810767346579 30485555703971716151019869)
              ·
                refine ⟨11432083388989393556632451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30485555703971716151019869 11432083388989393556632451)
                ·
                  refine ⟨17148125083484090334948677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11432083388989393556632451 17148125083484090334948677)
                  ·
                    refine ⟨3215273453153266937802877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17148125083484090334948677 3215273453153266937802877)
                    ·
                      refine ⟨1205727544932475101676079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3215273453153266937802877 1205727544932475101676079)
                      ·
                        rfl

theorem cell23_2348146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2348146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348146 prefixEnd_2348146 := by exact prefixLift 2348146
  have htrace : WordTrace (prefixWord ++ tailWord_2348146) baseStart_2348146 baseEnd_2348146 := by
    simpa [prefixWord, tailWord_2348146, baseEnd_2348146] using wordTrace_append hprefix tailTrace_2348146
  have hstable : (prefixWord ++ tailWord_2348146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348146).length < 2 ^ (prefixWord ++ tailWord_2348146).sum := by decide
  have hdescent : baseEnd_2348146 < baseStart_2348146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348183 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 6]
def baseStart_2348183 : Nat := 118140960795 + 2348183 * 2 ^ 59
def prefixEnd_2348183 : Nat := 4983230072969 + 3 ^ 40 * 2348183 * 2
def baseEnd_2348183 : Nat := 133971838190743495212601

theorem tailTrace_2348183 : CollatzResearch.WordTrace tailWord_2348183 prefixEnd_2348183 133971838190743495212601 := by
  unfold tailWord_2348183
  simp only [CollatzResearch.WordTrace]
  refine ⟨85645270051941503573265203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57096846701294335715510135 85645270051941503573265203)
  ·
    refine ⟨128467905077912255359897805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85645270051941503573265203 128467905077912255359897805)
    ·
      refine ⟨48175464404217095759961677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128467905077912255359897805 48175464404217095759961677)
      ·
        refine ⟨18065799151581410909985629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48175464404217095759961677 18065799151581410909985629)
        ·
          refine ⟨6774674681843029091244611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18065799151581410909985629 6774674681843029091244611)
          ·
            refine ⟨10162012022764543636866917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6774674681843029091244611 10162012022764543636866917)
            ·
              refine ⟨1905377254268351931912547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10162012022764543636866917 1905377254268351931912547)
              ·
                refine ⟨2858065881402527897868821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905377254268351931912547 2858065881402527897868821)
                ·
                  refine ⟨133971838190743495212601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2858065881402527897868821 133971838190743495212601)
                  ·
                    rfl

theorem cell23_2348183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 6].length) (baseStart_2348183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348183 prefixEnd_2348183 := by exact prefixLift 2348183
  have htrace : WordTrace (prefixWord ++ tailWord_2348183) baseStart_2348183 baseEnd_2348183 := by
    simpa [prefixWord, tailWord_2348183, baseEnd_2348183] using wordTrace_append hprefix tailTrace_2348183
  have hstable : (prefixWord ++ tailWord_2348183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348183).length < 2 ^ (prefixWord ++ tailWord_2348183).sum := by decide
  have hdescent : baseEnd_2348183 < baseStart_2348183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348193 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_2348193 : Nat := 118140960795 + 2348193 * 2 ^ 59
def prefixEnd_2348193 : Nat := 4983230072969 + 3 ^ 40 * 2348193 * 2
def baseEnd_2348193 : Nat := 1205751678523236417788363

theorem tailTrace_2348193 : CollatzResearch.WordTrace tailWord_2348193 prefixEnd_2348193 1205751678523236417788363 := by
  unfold tailWord_2348193
  simp only [CollatzResearch.WordTrace]
  refine ⟨85645634781905275281129233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57097089854603516854086155 85645634781905275281129233)
  ·
    refine ⟨64234226086428956460846925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85645634781905275281129233 64234226086428956460846925)
    ·
      refine ⟨24087834782410858672817597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64234226086428956460846925 24087834782410858672817597)
      ·
        refine ⟨9032938043404072002306599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24087834782410858672817597 9032938043404072002306599)
        ·
          refine ⟨13549407065106108003459899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9032938043404072002306599 13549407065106108003459899)
          ·
            refine ⟨20324110597659162005189849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13549407065106108003459899 20324110597659162005189849)
            ·
              refine ⟨15243082948244371503892387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20324110597659162005189849 15243082948244371503892387)
              ·
                refine ⟨22864624422366557255838581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15243082948244371503892387 22864624422366557255838581)
                ·
                  refine ⟨2143558539596864742734867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22864624422366557255838581 2143558539596864742734867)
                  ·
                    refine ⟨3215337809395297114102301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2143558539596864742734867 3215337809395297114102301)
                    ·
                      refine ⟨1205751678523236417788363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3215337809395297114102301 1205751678523236417788363)
                      ·
                        rfl

theorem cell23_2348193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_2348193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348193 prefixEnd_2348193 := by exact prefixLift 2348193
  have htrace : WordTrace (prefixWord ++ tailWord_2348193) baseStart_2348193 baseEnd_2348193 := by
    simpa [prefixWord, tailWord_2348193, baseEnd_2348193] using wordTrace_append hprefix tailTrace_2348193
  have hstable : (prefixWord ++ tailWord_2348193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348193).length < 2 ^ (prefixWord ++ tailWord_2348193).sum := by decide
  have hdescent : baseEnd_2348193 < baseStart_2348193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348220 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 2, 3, 2]
def baseStart_2348220 : Nat := 118140960795 + 2348220 * 2 ^ 59
def prefixEnd_2348220 : Nat := 4983230072969 + 3 ^ 40 * 2348220 * 2
def baseEnd_2348220 : Nat := 1205765542500907812150739

theorem tailTrace_2348220 : CollatzResearch.WordTrace tailWord_2348220 prefixEnd_2348220 1205765542500907812150739 := by
  unfold tailWord_2348220
  simp only [CollatzResearch.WordTrace]
  refine ⟨42823309776403729446181057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57097746368538305928241409 42823309776403729446181057)
  ·
    refine ⟨32117482332302797084635793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42823309776403729446181057 32117482332302797084635793)
    ·
      refine ⟨24088111749227097813476845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32117482332302797084635793 24088111749227097813476845)
      ·
        refine ⟨9033041905960161680053817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24088111749227097813476845 9033041905960161680053817)
        ·
          refine ⟨6774781429470121260040363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9033041905960161680053817 6774781429470121260040363)
          ·
            refine ⟨10162172144205181890060545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6774781429470121260040363 10162172144205181890060545)
            ·
              refine ⟨7621629108153886417545409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10162172144205181890060545 7621629108153886417545409)
              ·
                refine ⟨5716221831115414813159057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7621629108153886417545409 5716221831115414813159057)
                ·
                  refine ⟨4287166373336561109869293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5716221831115414813159057 4287166373336561109869293)
                  ·
                    refine ⟨1607687390001210416200985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4287166373336561109869293 1607687390001210416200985)
                    ·
                      refine ⟨1205765542500907812150739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607687390001210416200985 1205765542500907812150739)
                      ·
                        rfl

theorem cell23_2348220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_2348220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348220 prefixEnd_2348220 := by exact prefixLift 2348220
  have htrace : WordTrace (prefixWord ++ tailWord_2348220) baseStart_2348220 baseEnd_2348220 := by
    simpa [prefixWord, tailWord_2348220, baseEnd_2348220] using wordTrace_append hprefix tailTrace_2348220
  have hstable : (prefixWord ++ tailWord_2348220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348220).length < 2 ^ (prefixWord ++ tailWord_2348220).sum := by decide
  have hdescent : baseEnd_2348220 < baseStart_2348220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348239 : List Nat := [1, 1, 2, 1, 1, 3, 2, 12]
def baseStart_2348239 : Nat := 118140960795 + 2348239 * 2 ^ 59
def prefixEnd_2348239 : Nat := 4983230072969 + 3 ^ 40 * 2348239 * 2
def baseEnd_2348239 : Nat := 44658344393827527326413

theorem tailTrace_2348239 : CollatzResearch.WordTrace tailWord_2348239 prefixEnd_2348239 44658344393827527326413 := by
  unfold tailWord_2348239
  simp only [CollatzResearch.WordTrace]
  refine ⟨85647312539738625137303771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57098208359825750091535847 85647312539738625137303771)
  ·
    refine ⟨128470968809607937705955657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85647312539738625137303771 128470968809607937705955657)
    ·
      refine ⟨96353226607205953279466743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128470968809607937705955657 96353226607205953279466743)
      ·
        refine ⟨144529839910808929919200115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96353226607205953279466743 144529839910808929919200115)
        ·
          refine ⟨216794759866213394878800173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144529839910808929919200115 216794759866213394878800173)
          ·
            refine ⟨81298034949830023079550065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216794759866213394878800173 81298034949830023079550065)
            ·
              refine ⟨60973526212372517309662549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81298034949830023079550065 60973526212372517309662549)
              ·
                refine ⟨44658344393827527326413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 60973526212372517309662549 44658344393827527326413)
                ·
                  rfl

theorem cell23_2348239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 12].length) (baseStart_2348239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348239 prefixEnd_2348239 := by exact prefixLift 2348239
  have htrace : WordTrace (prefixWord ++ tailWord_2348239) baseStart_2348239 baseEnd_2348239 := by
    simpa [prefixWord, tailWord_2348239, baseEnd_2348239] using wordTrace_append hprefix tailTrace_2348239
  have hstable : (prefixWord ++ tailWord_2348239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348239).length < 2 ^ (prefixWord ++ tailWord_2348239).sum := by decide
  have hdescent : baseEnd_2348239 < baseStart_2348239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348267 : List Nat := [1, 1, 1, 1, 2, 6, 1, 5, 1, 2, 2]
def baseStart_2348267 : Nat := 118140960795 + 2348267 * 2 ^ 59
def prefixEnd_2348267 : Nat := 4983230072969 + 3 ^ 40 * 2348267 * 2
def baseEnd_2348267 : Nat := 1205789676091669128263023

theorem tailTrace_2348267 : CollatzResearch.WordTrace tailWord_2348267 prefixEnd_2348267 1205789676091669128263023 := by
  unfold tailWord_2348267
  simp only [CollatzResearch.WordTrace]
  refine ⟨85648333783637185919323055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57098889189091457279548703 85648333783637185919323055)
  ·
    refine ⟨128472500675455778878984583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85648333783637185919323055 128472500675455778878984583)
    ·
      refine ⟨192708751013183668318476875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128472500675455778878984583 192708751013183668318476875)
      ·
        refine ⟨289063126519775502477715313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192708751013183668318476875 289063126519775502477715313)
        ·
          refine ⟨216797344889831626858286485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289063126519775502477715313 216797344889831626858286485)
          ·
            refine ⟨10162375541710857508982179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 216797344889831626858286485 10162375541710857508982179)
            ·
              refine ⟨15243563312566286263473269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10162375541710857508982179 15243563312566286263473269)
              ·
                refine ⟨1429084060553089337200619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15243563312566286263473269 1429084060553089337200619)
                ·
                  refine ⟨2143626090829634005800929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429084060553089337200619 2143626090829634005800929)
                  ·
                    refine ⟨1607719568122225504350697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2143626090829634005800929 1607719568122225504350697)
                    ·
                      refine ⟨1205789676091669128263023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607719568122225504350697 1205789676091669128263023)
                      ·
                        rfl

theorem cell23_2348267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 1, 2, 2].length) (baseStart_2348267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348267 prefixEnd_2348267 := by exact prefixLift 2348267
  have htrace : WordTrace (prefixWord ++ tailWord_2348267) baseStart_2348267 baseEnd_2348267 := by
    simpa [prefixWord, tailWord_2348267, baseEnd_2348267] using wordTrace_append hprefix tailTrace_2348267
  have hstable : (prefixWord ++ tailWord_2348267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348267).length < 2 ^ (prefixWord ++ tailWord_2348267).sum := by decide
  have hdescent : baseEnd_2348267 < baseStart_2348267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348300 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 1, 3, 3]
def baseStart_2348300 : Nat := 118140960795 + 2348300 * 2 ^ 59
def prefixEnd_2348300 : Nat := 4983230072969 + 3 ^ 40 * 2348300 * 2
def baseEnd_2348300 : Nat := 1205806620953267499150371

theorem tailTrace_2348300 : CollatzResearch.WordTrace tailWord_2348300 prefixEnd_2348300 1205806620953267499150371 := by
  unfold tailWord_2348300
  simp only [CollatzResearch.WordTrace]
  refine ⟨42824768696258816277637177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57099691595011755036849569 42824768696258816277637177)
  ·
    refine ⟨32118576522194112208227883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42824768696258816277637177 32118576522194112208227883)
    ·
      refine ⟨48177864783291168312341825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32118576522194112208227883 48177864783291168312341825)
      ·
        refine ⟨36133398587468376234256369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48177864783291168312341825 36133398587468376234256369)
        ·
          refine ⟨27100048940601282175692277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36133398587468376234256369 27100048940601282175692277)
          ·
            refine ⟨2540629588181370203971151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27100048940601282175692277 2540629588181370203971151)
            ·
              refine ⟨3810944382272055305956727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540629588181370203971151 3810944382272055305956727)
              ·
                refine ⟨5716416573408082958935091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810944382272055305956727 5716416573408082958935091)
                ·
                  refine ⟨8574624860112124438402637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5716416573408082958935091 8574624860112124438402637)
                  ·
                    refine ⟨3215484322542046664400989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8574624860112124438402637 3215484322542046664400989)
                    ·
                      refine ⟨1205806620953267499150371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3215484322542046664400989 1205806620953267499150371)
                      ·
                        rfl

theorem cell23_2348300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_2348300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348300 prefixEnd_2348300 := by exact prefixLift 2348300
  have htrace : WordTrace (prefixWord ++ tailWord_2348300) baseStart_2348300 baseEnd_2348300 := by
    simpa [prefixWord, tailWord_2348300, baseEnd_2348300] using wordTrace_append hprefix tailTrace_2348300
  have hstable : (prefixWord ++ tailWord_2348300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348300).length < 2 ^ (prefixWord ++ tailWord_2348300).sum := by decide
  have hdescent : baseEnd_2348300 < baseStart_2348300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348316 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_2348316 : Nat := 118140960795 + 2348316 * 2 ^ 59
def prefixEnd_2348316 : Nat := 4983230072969 + 3 ^ 40 * 2348316 * 2
def baseEnd_2348316 : Nat := 401938278881246478850099

theorem tailTrace_2348316 : CollatzResearch.WordTrace tailWord_2348316 prefixEnd_2348316 401938278881246478850099 := by
  unfold tailWord_2348316
  simp only [CollatzResearch.WordTrace]
  refine ⟨42825060480229833643928401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57100080640306444858571201 42825060480229833643928401)
  ·
    refine ⟨32118795360172375232946301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42825060480229833643928401 32118795360172375232946301)
    ·
      refine ⟨12044548260064640712354863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32118795360172375232946301 12044548260064640712354863)
      ·
        refine ⟨18066822390096961068532295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12044548260064640712354863 18066822390096961068532295)
        ·
          refine ⟨27100233585145441602798443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18066822390096961068532295 27100233585145441602798443)
          ·
            refine ⟨40650350377718162404197665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27100233585145441602798443 40650350377718162404197665)
            ·
              refine ⟨30487762783288621803148249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40650350377718162404197665 30487762783288621803148249)
              ·
                refine ⟨22865822087466466352361187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30487762783288621803148249 22865822087466466352361187)
                ·
                  refine ⟨34298733131199699528541781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22865822087466466352361187 34298733131199699528541781)
                  ·
                    refine ⟨401938278881246478850099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34298733131199699528541781 401938278881246478850099)
                    ·
                      rfl

theorem cell23_2348316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_2348316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348316 prefixEnd_2348316 := by exact prefixLift 2348316
  have htrace : WordTrace (prefixWord ++ tailWord_2348316) baseStart_2348316 baseEnd_2348316 := by
    simpa [prefixWord, tailWord_2348316, baseEnd_2348316] using wordTrace_append hprefix tailTrace_2348316
  have hstable : (prefixWord ++ tailWord_2348316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348316).length < 2 ^ (prefixWord ++ tailWord_2348316).sum := by decide
  have hdescent : baseEnd_2348316 < baseStart_2348316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348397 : List Nat := [1, 5, 1, 1, 1, 3, 4, 2, 5]
def baseStart_2348397 : Nat := 118140960795 + 2348397 * 2 ^ 59
def prefixEnd_2348397 : Nat := 4983230072969 + 3 ^ 40 * 2348397 * 2
def baseEnd_2348397 : Nat := 133984047619639291070825

theorem tailTrace_2348397 : CollatzResearch.WordTrace tailWord_2348397 prefixEnd_2348397 133984047619639291070825 := by
  unfold tailWord_2348397
  simp only [CollatzResearch.WordTrace]
  refine ⟨85653075273166218121555445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57102050182110812081036963 85653075273166218121555445)
  ·
    refine ⟨8029975806859332948895823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85653075273166218121555445 8029975806859332948895823)
    ·
      refine ⟨12044963710288999423343735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8029975806859332948895823 12044963710288999423343735)
      ·
        refine ⟨18067445565433499135015603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12044963710288999423343735 18067445565433499135015603)
        ·
          refine ⟨27101168348150248702523405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18067445565433499135015603 27101168348150248702523405)
          ·
            refine ⟨10162938130556343263446277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27101168348150248702523405 10162938130556343263446277)
            ·
              refine ⟨1905550899479314361896177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10162938130556343263446277 1905550899479314361896177)
              ·
                refine ⟨1429163174609485771422133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1905550899479314361896177 1429163174609485771422133)
                ·
                  refine ⟨133984047619639291070825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1429163174609485771422133 133984047619639291070825)
                  ·
                    rfl

theorem cell23_2348397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_2348397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348397 prefixEnd_2348397 := by exact prefixLift 2348397
  have htrace : WordTrace (prefixWord ++ tailWord_2348397) baseStart_2348397 baseEnd_2348397 := by
    simpa [prefixWord, tailWord_2348397, baseEnd_2348397] using wordTrace_append hprefix tailTrace_2348397
  have hstable : (prefixWord ++ tailWord_2348397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348397).length < 2 ^ (prefixWord ++ tailWord_2348397).sum := by decide
  have hdescent : baseEnd_2348397 < baseStart_2348397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348413 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_2348413 : Nat := 118140960795 + 2348413 * 2 ^ 59
def prefixEnd_2348413 : Nat := 4983230072969 + 3 ^ 40 * 2348413 * 2
def baseEnd_2348413 : Nat := 1205864644267225557037351

theorem tailTrace_2348413 : CollatzResearch.WordTrace tailWord_2348413 prefixEnd_2348413 1205864644267225557037351 := by
  unfold tailWord_2348413
  simp only [CollatzResearch.WordTrace]
  refine ⟨85653658841108252854137893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57102439227405501902758595 85653658841108252854137893)
  ·
    refine ⟨16060061032707797410150855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85653658841108252854137893 16060061032707797410150855)
    ·
      refine ⟨24090091549061696115226283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16060061032707797410150855 24090091549061696115226283)
      ·
        refine ⟨36135137323592544172839425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24090091549061696115226283 36135137323592544172839425)
        ·
          refine ⟨27101352992694408129629569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36135137323592544172839425 27101352992694408129629569)
          ·
            refine ⟨20326014744520806097222177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27101352992694408129629569 20326014744520806097222177)
            ·
              refine ⟨15244511058390604572916633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20326014744520806097222177 15244511058390604572916633)
              ·
                refine ⟨11433383293792953429687475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15244511058390604572916633 11433383293792953429687475)
                ·
                  refine ⟨17150074940689430144531213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11433383293792953429687475 17150074940689430144531213)
                  ·
                    refine ⟨6431278102758536304199205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17150074940689430144531213 6431278102758536304199205)
                    ·
                      refine ⟨1205864644267225557037351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6431278102758536304199205 1205864644267225557037351)
                      ·
                        rfl

theorem cell23_2348413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_2348413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348413 prefixEnd_2348413 := by exact prefixLift 2348413
  have htrace : WordTrace (prefixWord ++ tailWord_2348413) baseStart_2348413 baseEnd_2348413 := by
    simpa [prefixWord, tailWord_2348413, baseEnd_2348413] using wordTrace_append hprefix tailTrace_2348413
  have hstable : (prefixWord ++ tailWord_2348413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348413).length < 2 ^ (prefixWord ++ tailWord_2348413).sum := by decide
  have hdescent : baseEnd_2348413 < baseStart_2348413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348433 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 3]
def baseStart_2348433 : Nat := 118140960795 + 2348433 * 2 ^ 59
def prefixEnd_2348433 : Nat := 4983230072969 + 3 ^ 40 * 2348433 * 2
def baseEnd_2348433 : Nat := 1205874913880315478787259

theorem tailTrace_2348433 : CollatzResearch.WordTrace tailWord_2348433 prefixEnd_2348433 1205874913880315478787259 := by
  unfold tailWord_2348433
  simp only [CollatzResearch.WordTrace]
  refine ⟨85654388301035796269865953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57102925534023864179910635 85654388301035796269865953)
  ·
    refine ⟨64240791225776847202399465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85654388301035796269865953 64240791225776847202399465)
    ·
      refine ⟨48180593419332635401799599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64240791225776847202399465 48180593419332635401799599)
      ·
        refine ⟨72270890128998953102699399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48180593419332635401799599 72270890128998953102699399)
        ·
          refine ⟨108406335193498429654049099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72270890128998953102699399 108406335193498429654049099)
          ·
            refine ⟨162609502790247644481073649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108406335193498429654049099 162609502790247644481073649)
            ·
              refine ⟨121957127092685733360805237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162609502790247644481073649 121957127092685733360805237)
              ·
                refine ⟨11433480664939287502575491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121957127092685733360805237 11433480664939287502575491)
                ·
                  refine ⟨17150220997408931253863237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11433480664939287502575491 17150220997408931253863237)
                  ·
                    refine ⟨3215666437014174610099357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17150220997408931253863237 3215666437014174610099357)
                    ·
                      refine ⟨1205874913880315478787259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3215666437014174610099357 1205874913880315478787259)
                      ·
                        rfl

theorem cell23_2348433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_2348433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348433 prefixEnd_2348433 := by exact prefixLift 2348433
  have htrace : WordTrace (prefixWord ++ tailWord_2348433) baseStart_2348433 baseEnd_2348433 := by
    simpa [prefixWord, tailWord_2348433, baseEnd_2348433] using wordTrace_append hprefix tailTrace_2348433
  have hstable : (prefixWord ++ tailWord_2348433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348433).length < 2 ^ (prefixWord ++ tailWord_2348433).sum := by decide
  have hdescent : baseEnd_2348433 < baseStart_2348433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348453 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 6]
def baseStart_2348453 : Nat := 118140960795 + 2348453 * 2 ^ 59
def prefixEnd_2348453 : Nat := 4983230072969 + 3 ^ 40 * 2348453 * 2
def baseEnd_2348453 : Nat := 133987242610378377837463

theorem tailTrace_2348453 : CollatzResearch.WordTrace tailWord_2348453 prefixEnd_2348453 133987242610378377837463 := by
  unfold tailWord_2348453
  simp only [CollatzResearch.WordTrace]
  refine ⟨85655117760963339685594013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57103411840642226457062675 85655117760963339685594013)
  ·
    refine ⟨32120669160361252382097755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85655117760963339685594013 32120669160361252382097755)
    ·
      refine ⟨48181003740541878573146633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32120669160361252382097755 48181003740541878573146633)
      ·
        refine ⟨36135752805406408929859975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48181003740541878573146633 36135752805406408929859975)
        ·
          refine ⟨54203629208109613394789963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36135752805406408929859975 54203629208109613394789963)
          ·
            refine ⟨81305443812164420092184945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54203629208109613394789963 81305443812164420092184945)
            ·
              refine ⟨60979082859123315069138709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81305443812164420092184945 60979082859123315069138709)
              ·
                refine ⟨2858394509021405393865877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60979082859123315069138709 2858394509021405393865877)
                ·
                  refine ⟨133987242610378377837463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2858394509021405393865877 133987242610378377837463)
                  ·
                    rfl

theorem cell23_2348453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_2348453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348453 prefixEnd_2348453 := by exact prefixLift 2348453
  have htrace : WordTrace (prefixWord ++ tailWord_2348453) baseStart_2348453 baseEnd_2348453 := by
    simpa [prefixWord, tailWord_2348453, baseEnd_2348453] using wordTrace_append hprefix tailTrace_2348453
  have hstable : (prefixWord ++ tailWord_2348453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348453).length < 2 ^ (prefixWord ++ tailWord_2348453).sum := by decide
  have hdescent : baseEnd_2348453 < baseStart_2348453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348483 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 3, 5]
def baseStart_2348483 : Nat := 118140960795 + 2348483 * 2 ^ 59
def prefixEnd_2348483 : Nat := 4983230072969 + 3 ^ 40 * 2348483 * 2
def baseEnd_2348483 : Nat := 401966862637680094387343

theorem tailTrace_2348483 : CollatzResearch.WordTrace tailWord_2348483 prefixEnd_2348483 401966862637680094387343 := by
  unfold tailWord_2348483
  simp only [CollatzResearch.WordTrace]
  refine ⟨85656211950854654809186103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57104141300569769872790735 85656211950854654809186103)
  ·
    refine ⟨128484317926281982213779155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85656211950854654809186103 128484317926281982213779155)
    ·
      refine ⟨192726476889422973320668733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128484317926281982213779155 192726476889422973320668733)
      ·
        refine ⟨72272428833533614995250775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192726476889422973320668733 72272428833533614995250775)
        ·
          refine ⟨108408643250300422492876163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72272428833533614995250775 108408643250300422492876163)
          ·
            refine ⟨162612964875450633739314245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108408643250300422492876163 162612964875450633739314245)
            ·
              refine ⟨30489930914146993826121421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162612964875450633739314245 30489930914146993826121421)
              ·
                refine ⟨11433724092805122684795533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30489930914146993826121421 11433724092805122684795533)
                ·
                  refine ⟨4287646534801921006798325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11433724092805122684795533 4287646534801921006798325)
                  ·
                    refine ⟨401966862637680094387343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4287646534801921006798325 401966862637680094387343)
                    ·
                      rfl

theorem cell23_2348483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 5].length) (baseStart_2348483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348483 prefixEnd_2348483 := by exact prefixLift 2348483
  have htrace : WordTrace (prefixWord ++ tailWord_2348483) baseStart_2348483 baseEnd_2348483 := by
    simpa [prefixWord, tailWord_2348483, baseEnd_2348483] using wordTrace_append hprefix tailTrace_2348483
  have hstable : (prefixWord ++ tailWord_2348483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348483).length < 2 ^ (prefixWord ++ tailWord_2348483).sum := by decide
  have hdescent : baseEnd_2348483 < baseStart_2348483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348520 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_2348520 : Nat := 118140960795 + 2348520 * 2 ^ 59
def prefixEnd_2348520 : Nat := 4983230072969 + 3 ^ 40 * 2348520 * 2
def baseEnd_2348520 : Nat := 1205919586697256638399359

theorem tailTrace_2348520 : CollatzResearch.WordTrace tailWord_2348520 prefixEnd_2348520 1205919586697256638399359 := by
  unfold tailWord_2348520
  simp only [CollatzResearch.WordTrace]
  refine ⟨42828780725860305064141507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57105040967813740085522009 42828780725860305064141507)
  ·
    refine ⟨64243171088790457596212261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42828780725860305064141507 64243171088790457596212261)
    ·
      refine ⟨12045594579148210799289799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64243171088790457596212261 12045594579148210799289799)
      ·
        refine ⟨18068391868722316198934699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12045594579148210799289799 18068391868722316198934699)
        ·
          refine ⟨27102587803083474298402049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18068391868722316198934699 27102587803083474298402049)
          ·
            refine ⟨20326940852312605723801537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27102587803083474298402049 20326940852312605723801537)
            ·
              refine ⟨15245205639234454292851153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20326940852312605723801537 15245205639234454292851153)
              ·
                refine ⟨11433904229425840719638365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15245205639234454292851153 11433904229425840719638365)
                ·
                  refine ⟨4287714086034690269864387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11433904229425840719638365 4287714086034690269864387)
                  ·
                    refine ⟨6431571129052035404796581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4287714086034690269864387 6431571129052035404796581)
                    ·
                      refine ⟨1205919586697256638399359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6431571129052035404796581 1205919586697256638399359)
                      ·
                        rfl

theorem cell23_2348520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_2348520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348520 prefixEnd_2348520 := by exact prefixLift 2348520
  have htrace : WordTrace (prefixWord ++ tailWord_2348520) baseStart_2348520 baseEnd_2348520 := by
    simpa [prefixWord, tailWord_2348520, baseEnd_2348520] using wordTrace_append hprefix tailTrace_2348520
  have hstable : (prefixWord ++ tailWord_2348520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348520).length < 2 ^ (prefixWord ++ tailWord_2348520).sum := by decide
  have hdescent : baseEnd_2348520 < baseStart_2348520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348523 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 5]
def baseStart_2348523 : Nat := 118140960795 + 2348523 * 2 ^ 59
def prefixEnd_2348523 : Nat := 4983230072969 + 3 ^ 40 * 2348523 * 2
def baseEnd_2348523 : Nat := 1205921127139220126661845

theorem tailTrace_2348523 : CollatzResearch.WordTrace tailWord_2348523 prefixEnd_2348523 1205921127139220126661845 := by
  unfold tailWord_2348523
  simp only [CollatzResearch.WordTrace]
  refine ⟨85657670870709741640642223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57105113913806494427094815 85657670870709741640642223)
  ·
    refine ⟨128486506306064612460963335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85657670870709741640642223 128486506306064612460963335)
    ·
      refine ⟨192729759459096918691445003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128486506306064612460963335 192729759459096918691445003)
      ·
        refine ⟨289094639188645378037167505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192729759459096918691445003 289094639188645378037167505)
        ·
          refine ⟨216820979391484033527875629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289094639188645378037167505 216820979391484033527875629)
          ·
            refine ⟨81307867271806512572953361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216820979391484033527875629 81307867271806512572953361)
            ·
              refine ⟨60980900453854884429715021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81307867271806512572953361 60980900453854884429715021)
              ·
                refine ⟨22867837670195581661143133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60980900453854884429715021 22867837670195581661143133)
                ·
                  refine ⟨8575439126323343122928675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22867837670195581661143133 8575439126323343122928675)
                  ·
                    refine ⟨12863158689485014684393013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8575439126323343122928675 12863158689485014684393013)
                    ·
                      refine ⟨1205921127139220126661845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12863158689485014684393013 1205921127139220126661845)
                      ·
                        rfl

theorem cell23_2348523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 5].length) (baseStart_2348523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348523 prefixEnd_2348523 := by exact prefixLift 2348523
  have htrace : WordTrace (prefixWord ++ tailWord_2348523) baseStart_2348523 baseEnd_2348523 := by
    simpa [prefixWord, tailWord_2348523, baseEnd_2348523] using wordTrace_append hprefix tailTrace_2348523
  have hstable : (prefixWord ++ tailWord_2348523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348523).length < 2 ^ (prefixWord ++ tailWord_2348523).sum := by decide
  have hdescent : baseEnd_2348523 < baseStart_2348523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348534 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_2348534 : Nat := 118140960795 + 2348534 * 2 ^ 59
def prefixEnd_2348534 : Nat := 4983230072969 + 3 ^ 40 * 2348534 * 2
def baseEnd_2348534 : Nat := 401975591808806527874765

theorem tailTrace_2348534 : CollatzResearch.WordTrace tailWord_2348534 prefixEnd_2348534 401975591808806527874765 := by
  unfold tailWord_2348534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353629504604368157455791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57105381382446593679528437 5353629504604368157455791)
  ·
    refine ⟨8030444256906552236183687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5353629504604368157455791 8030444256906552236183687)
    ·
      refine ⟨12045666385359828354275531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8030444256906552236183687 12045666385359828354275531)
      ·
        refine ⟨18068499578039742531413297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12045666385359828354275531 18068499578039742531413297)
        ·
          refine ⟨13551374683529806898559973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18068499578039742531413297 13551374683529806898559973)
          ·
            refine ⟨2540882753161838793479995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13551374683529806898559973 2540882753161838793479995)
            ·
              refine ⟨3811324129742758190219993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540882753161838793479995 3811324129742758190219993)
              ·
                refine ⟨2858493097307068642664995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3811324129742758190219993 2858493097307068642664995)
                ·
                  refine ⟨4287739645960602963997493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858493097307068642664995 4287739645960602963997493)
                  ·
                    refine ⟨401975591808806527874765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4287739645960602963997493 401975591808806527874765)
                    ·
                      rfl

theorem cell23_2348534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_2348534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348534 prefixEnd_2348534 := by exact prefixLift 2348534
  have htrace : WordTrace (prefixWord ++ tailWord_2348534) baseStart_2348534 baseEnd_2348534 := by
    simpa [prefixWord, tailWord_2348534, baseEnd_2348534] using wordTrace_append hprefix tailTrace_2348534
  have hstable : (prefixWord ++ tailWord_2348534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348534).length < 2 ^ (prefixWord ++ tailWord_2348534).sum := by decide
  have hdescent : baseEnd_2348534 < baseStart_2348534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348537 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 5, 2, 2]
def baseStart_2348537 : Nat := 118140960795 + 2348537 * 2 ^ 59
def prefixEnd_2348537 : Nat := 4983230072969 + 3 ^ 40 * 2348537 * 2
def baseEnd_2348537 : Nat := 1205928315868383071886781

theorem tailTrace_2348537 : CollatzResearch.WordTrace tailWord_2348537 prefixEnd_2348537 1205928315868383071886781 := by
  unfold tailWord_2348537
  simp only [CollatzResearch.WordTrace]
  refine ⟨85658181492659022031651865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57105454328439348021101243 85658181492659022031651865)
  ·
    refine ⟨64243636119494266523738899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85658181492659022031651865 64243636119494266523738899)
    ·
      refine ⟨96365454179241399785608349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64243636119494266523738899 96365454179241399785608349)
      ·
        refine ⟨36137045317215524919603131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96365454179241399785608349 36137045317215524919603131)
        ·
          refine ⟨54205567975823287379404697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36137045317215524919603131 54205567975823287379404697)
          ·
            refine ⟨40654175981867465534553523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54205567975823287379404697 40654175981867465534553523)
            ·
              refine ⟨60981263972801198301830285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40654175981867465534553523 60981263972801198301830285)
              ·
                refine ⟨22867973989800449363186357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60981263972801198301830285 22867973989800449363186357)
                ·
                  refine ⟨2143872561543792127798721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22867973989800449363186357 2143872561543792127798721)
                  ·
                    refine ⟨1607904421157844095849041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2143872561543792127798721 1607904421157844095849041)
                    ·
                      refine ⟨1205928315868383071886781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607904421157844095849041 1205928315868383071886781)
                      ·
                        rfl

theorem cell23_2348537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_2348537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348537 prefixEnd_2348537 := by exact prefixLift 2348537
  have htrace : WordTrace (prefixWord ++ tailWord_2348537) baseStart_2348537 baseEnd_2348537 := by
    simpa [prefixWord, tailWord_2348537, baseEnd_2348537] using wordTrace_append hprefix tailTrace_2348537
  have hstable : (prefixWord ++ tailWord_2348537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348537).length < 2 ^ (prefixWord ++ tailWord_2348537).sum := by decide
  have hdescent : baseEnd_2348537 < baseStart_2348537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348554 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4]
def baseStart_2348554 : Nat := 118140960795 + 2348554 * 2 ^ 59
def prefixEnd_2348554 : Nat := 4983230072969 + 3 ^ 40 * 2348554 * 2
def baseEnd_2348554 : Nat := 1205937045039509505374203

theorem tailTrace_2348554 : CollatzResearch.WordTrace tailWord_2348554 prefixEnd_2348554 1205937045039509505374203 := by
  unfold tailWord_2348554
  simp only [CollatzResearch.WordTrace]
  refine ⟨21414700383399358483755179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57105867689064955956680477 21414700383399358483755179)
  ·
    refine ⟨32122050575099037725632769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21414700383399358483755179 32122050575099037725632769)
    ·
      refine ⟨24091537931324278294224577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32122050575099037725632769 24091537931324278294224577)
      ·
        refine ⟨18068653448493208720668433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24091537931324278294224577 18068653448493208720668433)
        ·
          refine ⟨13551490086369906540501325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18068653448493208720668433 13551490086369906540501325)
          ·
            refine ⟨5081808782388714952687997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13551490086369906540501325 5081808782388714952687997)
            ·
              refine ⟨1905678293395768107257999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5081808782388714952687997 1905678293395768107257999)
              ·
                refine ⟨2858517440093652160886999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905678293395768107257999 2858517440093652160886999)
                ·
                  refine ⟨4287776160140478241330499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858517440093652160886999 4287776160140478241330499)
                  ·
                    refine ⟨6431664240210717361995749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4287776160140478241330499 6431664240210717361995749)
                    ·
                      refine ⟨1205937045039509505374203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6431664240210717361995749 1205937045039509505374203)
                      ·
                        rfl

theorem cell23_2348554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_2348554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348554 prefixEnd_2348554 := by exact prefixLift 2348554
  have htrace : WordTrace (prefixWord ++ tailWord_2348554) baseStart_2348554 baseEnd_2348554 := by
    simpa [prefixWord, tailWord_2348554, baseEnd_2348554] using wordTrace_append hprefix tailTrace_2348554
  have hstable : (prefixWord ++ tailWord_2348554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348554).length < 2 ^ (prefixWord ++ tailWord_2348554).sum := by decide
  have hdescent : baseEnd_2348554 < baseStart_2348554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348570 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3]
def baseStart_2348570 : Nat := 118140960795 + 2348570 * 2 ^ 59
def prefixEnd_2348570 : Nat := 4983230072969 + 3 ^ 40 * 2348570 * 2
def baseEnd_2348570 : Nat := 1205945260729981442774129

theorem tailTrace_2348570 : CollatzResearch.WordTrace tailWord_2348570 prefixEnd_2348570 1205945260729981442774129 := by
  unfold tailWord_2348570
  simp only [CollatzResearch.WordTrace]
  refine ⟨21414846275384867166900791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57106256734359645778402109 21414846275384867166900791)
  ·
    refine ⟨32122269413077300750351187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21414846275384867166900791 32122269413077300750351187)
    ·
      refine ⟨48183404119615951125526781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32122269413077300750351187 48183404119615951125526781)
      ·
        refine ⟨18068776544855981672072543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48183404119615951125526781 18068776544855981672072543)
        ·
          refine ⟨27103164817283972508108815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18068776544855981672072543 27103164817283972508108815)
          ·
            refine ⟨40654747225925958762163223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27103164817283972508108815 40654747225925958762163223)
            ·
              refine ⟨60982120838888938143244835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40654747225925958762163223 60982120838888938143244835)
              ·
                refine ⟨91473181258333407214867253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60982120838888938143244835 91473181258333407214867253)
                ·
                  refine ⟨8575610742968756926393805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91473181258333407214867253 8575610742968756926393805)
                  ·
                    refine ⟨3215854028613283847397677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8575610742968756926393805 3215854028613283847397677)
                    ·
                      refine ⟨1205945260729981442774129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3215854028613283847397677 1205945260729981442774129)
                      ·
                        rfl

theorem cell23_2348570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_2348570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348570 prefixEnd_2348570 := by exact prefixLift 2348570
  have htrace : WordTrace (prefixWord ++ tailWord_2348570) baseStart_2348570 baseEnd_2348570 := by
    simpa [prefixWord, tailWord_2348570, baseEnd_2348570] using wordTrace_append hprefix tailTrace_2348570
  have hstable : (prefixWord ++ tailWord_2348570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348570).length < 2 ^ (prefixWord ++ tailWord_2348570).sum := by decide
  have hdescent : baseEnd_2348570 < baseStart_2348570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348584 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2348584 : Nat := 118140960795 + 2348584 * 2 ^ 59
def prefixEnd_2348584 : Nat := 4983230072969 + 3 ^ 40 * 2348584 * 2
def baseEnd_2348584 : Nat := 1205952449459144387999065

theorem tailTrace_2348584 : CollatzResearch.WordTrace tailWord_2348584 prefixEnd_2348584 1205952449459144387999065 := by
  unfold tailWord_2348584
  simp only [CollatzResearch.WordTrace]
  refine ⟨42829947861744374529306403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57106597148992499372408537 42829947861744374529306403)
  ·
    refine ⟨64244921792616561793959605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42829947861744374529306403 64244921792616561793959605)
    ·
      refine ⟨6022961418057802668183713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64244921792616561793959605 6022961418057802668183713)
      ·
        refine ⟨4517221063543352001137785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6022961418057802668183713 4517221063543352001137785)
        ·
          refine ⟨3387915797657514000853339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4517221063543352001137785 3387915797657514000853339)
          ·
            refine ⟨5081873696486271001280009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387915797657514000853339 5081873696486271001280009)
            ·
              refine ⟨3811405272364703250960007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5081873696486271001280009 3811405272364703250960007)
              ·
                refine ⟨5717107908547054876440011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811405272364703250960007 5717107908547054876440011)
                ·
                  refine ⟨8575661862820582314660017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5717107908547054876440011 8575661862820582314660017)
                  ·
                    refine ⟨6431746397115436735995013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8575661862820582314660017 6431746397115436735995013)
                    ·
                      refine ⟨1205952449459144387999065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6431746397115436735995013 1205952449459144387999065)
                      ·
                        rfl

theorem cell23_2348584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2348584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348584 prefixEnd_2348584 := by exact prefixLift 2348584
  have htrace : WordTrace (prefixWord ++ tailWord_2348584) baseStart_2348584 baseEnd_2348584 := by
    simpa [prefixWord, tailWord_2348584, baseEnd_2348584] using wordTrace_append hprefix tailTrace_2348584
  have hstable : (prefixWord ++ tailWord_2348584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348584).length < 2 ^ (prefixWord ++ tailWord_2348584).sum := by decide
  have hdescent : baseEnd_2348584 < baseStart_2348584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348620 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_2348620 : Nat := 118140960795 + 2348620 * 2 ^ 59
def prefixEnd_2348620 : Nat := 4983230072969 + 3 ^ 40 * 2348620 * 2
def baseEnd_2348620 : Nat := 401990311587568749049633

theorem tailTrace_2348620 : CollatzResearch.WordTrace tailWord_2348620 prefixEnd_2348620 401990311587568749049633 := by
  unfold tailWord_2348620
  simp only [CollatzResearch.WordTrace]
  refine ⟨42830604375679163603461657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57107472500905551471282209 42830604375679163603461657)
  ·
    refine ⟨32122953281759372702596243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42830604375679163603461657 32122953281759372702596243)
    ·
      refine ⟨48184429922639059053894365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32122953281759372702596243 48184429922639059053894365)
      ·
        refine ⟨18069161220989647145210387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48184429922639059053894365 18069161220989647145210387)
        ·
          refine ⟨27103741831484470717815581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18069161220989647145210387 27103741831484470717815581)
          ·
            refine ⟨10163903186806676519180843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27103741831484470717815581 10163903186806676519180843)
            ·
              refine ⟨15245854780210014778771265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10163903186806676519180843 15245854780210014778771265)
              ·
                refine ⟨11434391085157511084078449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15245854780210014778771265 11434391085157511084078449)
                ·
                  refine ⟨8575793313868133313058837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11434391085157511084078449 8575793313868133313058837)
                  ·
                    refine ⟨401990311587568749049633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8575793313868133313058837 401990311587568749049633)
                    ·
                      rfl

theorem cell23_2348620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_2348620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348620 prefixEnd_2348620 := by exact prefixLift 2348620
  have htrace : WordTrace (prefixWord ++ tailWord_2348620) baseStart_2348620 baseEnd_2348620 := by
    simpa [prefixWord, tailWord_2348620, baseEnd_2348620] using wordTrace_append hprefix tailTrace_2348620
  have hstable : (prefixWord ++ tailWord_2348620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348620).length < 2 ^ (prefixWord ++ tailWord_2348620).sum := by decide
  have hdescent : baseEnd_2348620 < baseStart_2348620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348621 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2348621 : Nat := 118140960795 + 2348621 * 2 ^ 59
def prefixEnd_2348621 : Nat := 4983230072969 + 3 ^ 40 * 2348621 * 2
def baseEnd_2348621 : Nat := 1205971448243360743236395

theorem tailTrace_2348621 : CollatzResearch.WordTrace tailWord_2348621 prefixEnd_2348621 1205971448243360743236395 := by
  unfold tailWord_2348621
  simp only [CollatzResearch.WordTrace]
  refine ⟨85661245224354704377709717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57107496816236469585139811 85661245224354704377709717)
  ·
    refine ⟨4015370869891626767705143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85661245224354704377709717 4015370869891626767705143)
    ·
      refine ⟨6023056304837440151557715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4015370869891626767705143 6023056304837440151557715)
      ·
        refine ⟨9034584457256160227336573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6023056304837440151557715 9034584457256160227336573)
        ·
          refine ⟨3387969171471060085251215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9034584457256160227336573 3387969171471060085251215)
          ·
            refine ⟨5081953757206590127876823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387969171471060085251215 5081953757206590127876823)
            ·
              refine ⟨7622930635809885191815235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5081953757206590127876823 7622930635809885191815235)
              ·
                refine ⟨11434395953714827787722853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7622930635809885191815235 11434395953714827787722853)
                ·
                  refine ⟨2143949241321530210198035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11434395953714827787722853 2143949241321530210198035)
                  ·
                    refine ⟨3215923861982295315297053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2143949241321530210198035 3215923861982295315297053)
                    ·
                      refine ⟨1205971448243360743236395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3215923861982295315297053 1205971448243360743236395)
                      ·
                        rfl

theorem cell23_2348621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2348621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348621 prefixEnd_2348621 := by exact prefixLift 2348621
  have htrace : WordTrace (prefixWord ++ tailWord_2348621) baseStart_2348621 baseEnd_2348621 := by
    simpa [prefixWord, tailWord_2348621, baseEnd_2348621] using wordTrace_append hprefix tailTrace_2348621
  have hstable : (prefixWord ++ tailWord_2348621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348621).length < 2 ^ (prefixWord ++ tailWord_2348621).sum := by decide
  have hdescent : baseEnd_2348621 < baseStart_2348621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348644 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 1, 4, 2]
def baseStart_2348644 : Nat := 118140960795 + 2348644 * 2 ^ 59
def prefixEnd_2348644 : Nat := 4983230072969 + 3 ^ 40 * 2348644 * 2
def baseEnd_2348644 : Nat := 1205983258298414153248789

theorem tailTrace_2348644 : CollatzResearch.WordTrace tailWord_2348644 prefixEnd_2348644 1205983258298414153248789 := by
  unfold tailWord_2348644
  simp only [CollatzResearch.WordTrace]
  refine ⟨42831042051635689652898493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57108056068847586203864657 42831042051635689652898493)
  ·
    refine ⟨16061640769363383619836935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42831042051635689652898493 16061640769363383619836935)
    ·
      refine ⟨24092461154045075429755403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16061640769363383619836935 24092461154045075429755403)
      ·
        refine ⟨36138691731067613144633105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24092461154045075429755403 36138691731067613144633105)
        ·
          refine ⟨27104018798300709858474829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36138691731067613144633105 27104018798300709858474829)
          ·
            refine ⟨10164007049362766196928061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27104018798300709858474829 10164007049362766196928061)
            ·
              refine ⟨3811502643511037323848023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10164007049362766196928061 3811502643511037323848023)
              ·
                refine ⟨5717253965266555985772035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811502643511037323848023 5717253965266555985772035)
                ·
                  refine ⟨8575880947899833978658053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5717253965266555985772035 8575880947899833978658053)
                  ·
                    refine ⟨1607977677731218870998385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8575880947899833978658053 1607977677731218870998385)
                    ·
                      refine ⟨1205983258298414153248789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607977677731218870998385 1205983258298414153248789)
                      ·
                        rfl

theorem cell23_2348644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_2348644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348644 prefixEnd_2348644 := by exact prefixLift 2348644
  have htrace : WordTrace (prefixWord ++ tailWord_2348644) baseStart_2348644 baseEnd_2348644 := by
    simpa [prefixWord, tailWord_2348644, baseEnd_2348644] using wordTrace_append hprefix tailTrace_2348644
  have hstable : (prefixWord ++ tailWord_2348644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348644).length < 2 ^ (prefixWord ++ tailWord_2348644).sum := by decide
  have hdescent : baseEnd_2348644 < baseStart_2348644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348661 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2348661 : Nat := 118140960795 + 2348661 * 2 ^ 59
def prefixEnd_2348661 : Nat := 4983230072969 + 3 ^ 40 * 2348661 * 2
def baseEnd_2348661 : Nat := 1205991987469540586736211

theorem tailTrace_2348661 : CollatzResearch.WordTrace tailWord_2348661 prefixEnd_2348661 1205991987469540586736211 := by
  unfold tailWord_2348661
  simp only [CollatzResearch.WordTrace]
  refine ⟨85662704144209791209165837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57108469429473194139443891 85662704144209791209165837)
  ·
    refine ⟨32123514054078671703437189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85662704144209791209165837 32123514054078671703437189)
    ·
      refine ⟨6023158885139750944394473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32123514054078671703437189 6023158885139750944394473)
      ·
        refine ⟨4517369163854813208295855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6023158885139750944394473 4517369163854813208295855)
        ·
          refine ⟨6776053745782219812443783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517369163854813208295855 6776053745782219812443783)
          ·
            refine ⟨10164080618673329718665675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6776053745782219812443783 10164080618673329718665675)
            ·
              refine ⟨15246120928009994577998513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10164080618673329718665675 15246120928009994577998513)
              ·
                refine ⟨11434590696007495933498885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15246120928009994577998513 11434590696007495933498885)
                ·
                  refine ⟨2143985755501405487531041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11434590696007495933498885 2143985755501405487531041)
                  ·
                    refine ⟨1607989316626054115648281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2143985755501405487531041 1607989316626054115648281)
                    ·
                      refine ⟨1205991987469540586736211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607989316626054115648281 1205991987469540586736211)
                      ·
                        rfl

theorem cell23_2348661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2348661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348661 prefixEnd_2348661 := by exact prefixLift 2348661
  have htrace : WordTrace (prefixWord ++ tailWord_2348661) baseStart_2348661 baseEnd_2348661 := by
    simpa [prefixWord, tailWord_2348661, baseEnd_2348661] using wordTrace_append hprefix tailTrace_2348661
  have hstable : (prefixWord ++ tailWord_2348661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348661).length < 2 ^ (prefixWord ++ tailWord_2348661).sum := by decide
  have hdescent : baseEnd_2348661 < baseStart_2348661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348684 : List Nat := [2, 2, 1, 2, 1, 1, 7, 2, 5]
def baseStart_2348684 : Nat := 118140960795 + 2348684 * 2 ^ 59
def prefixEnd_2348684 : Nat := 4983230072969 + 3 ^ 40 * 2348684 * 2
def baseEnd_2348684 : Nat := 134000421947177110749845

theorem tailTrace_2348684 : CollatzResearch.WordTrace tailWord_2348684 prefixEnd_2348684 134000421947177110749845 := by
  unfold tailWord_2348684
  simp only [CollatzResearch.WordTrace]
  refine ⟨42831771511563233068626553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57109028682084310758168737 42831771511563233068626553)
  ·
    refine ⟨32123828633672424801469915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42831771511563233068626553 32123828633672424801469915)
    ·
      refine ⟨48185742950508637202204873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32123828633672424801469915 48185742950508637202204873)
      ·
        refine ⟨36139307212881477901653655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48185742950508637202204873 36139307212881477901653655)
        ·
          refine ⟨54208960819322216852480483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36139307212881477901653655 54208960819322216852480483)
          ·
            refine ⟨81313441228983325278720725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54208960819322216852480483 81313441228983325278720725)
            ·
              refine ⟨1905783778804296686220017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 81313441228983325278720725 1905783778804296686220017)
              ·
                refine ⟨1429337834103222514665013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1905783778804296686220017 1429337834103222514665013)
                ·
                  refine ⟨134000421947177110749845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1429337834103222514665013 134000421947177110749845)
                  ·
                    rfl

theorem cell23_2348684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_2348684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348684 prefixEnd_2348684 := by exact prefixLift 2348684
  have htrace : WordTrace (prefixWord ++ tailWord_2348684) baseStart_2348684 baseEnd_2348684 := by
    simpa [prefixWord, tailWord_2348684, baseEnd_2348684] using wordTrace_append hprefix tailTrace_2348684
  have hstable : (prefixWord ++ tailWord_2348684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348684).length < 2 ^ (prefixWord ++ tailWord_2348684).sum := by decide
  have hdescent : baseEnd_2348684 < baseStart_2348684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348734 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_2348734 : Nat := 118140960795 + 2348734 * 2 ^ 59
def prefixEnd_2348734 : Nat := 4983230072969 + 3 ^ 40 * 2348734 * 2
def baseEnd_2348734 : Nat := 1206029471557318801123375

theorem tailTrace_2348734 : CollatzResearch.WordTrace tailWord_2348734 prefixEnd_2348734 1206029471557318801123375 := by
  unfold tailWord_2348734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10708170834118165584571657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57110244448630216451048837 10708170834118165584571657)
  ·
    refine ⟨8031128125588624188428743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10708170834118165584571657 8031128125588624188428743)
    ·
      refine ⟨12046692188382936282643115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8031128125588624188428743 12046692188382936282643115)
      ·
        refine ⟨18070038282574404423964673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12046692188382936282643115 18070038282574404423964673)
        ·
          refine ⟨13552528711930803317973505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18070038282574404423964673 13552528711930803317973505)
          ·
            refine ⟨10164396533948102488480129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13552528711930803317973505 10164396533948102488480129)
            ·
              refine ⟨7623297400461076866360097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10164396533948102488480129 7623297400461076866360097)
              ·
                refine ⟨5717473050345807649770073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7623297400461076866360097 5717473050345807649770073)
                ·
                  refine ⟨4288104787759355737327555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5717473050345807649770073 4288104787759355737327555)
                  ·
                    refine ⟨6432157181639033605991333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4288104787759355737327555 6432157181639033605991333)
                    ·
                      refine ⟨1206029471557318801123375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6432157181639033605991333 1206029471557318801123375)
                      ·
                        rfl

theorem cell23_2348734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_2348734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348734 prefixEnd_2348734 := by exact prefixLift 2348734
  have htrace : WordTrace (prefixWord ++ tailWord_2348734) baseStart_2348734 baseEnd_2348734 := by
    simpa [prefixWord, tailWord_2348734, baseEnd_2348734] using wordTrace_append hprefix tailTrace_2348734
  have hstable : (prefixWord ++ tailWord_2348734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348734).length < 2 ^ (prefixWord ++ tailWord_2348734).sum := by decide
  have hdescent : baseEnd_2348734 < baseStart_2348734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348794 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2]
def baseStart_2348794 : Nat := 118140960795 + 2348794 * 2 ^ 59
def prefixEnd_2348794 : Nat := 4983230072969 + 3 ^ 40 * 2348794 * 2
def baseEnd_2348794 : Nat := 1206060280396588566373099

theorem tailTrace_2348794 : CollatzResearch.WordTrace tailWord_2348794 prefixEnd_2348794 1206060280396588566373099 := by
  unfold tailWord_2348794
  simp only [CollatzResearch.WordTrace]
  refine ⟨21416888763181988730939359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57111703368485303282504957 21416888763181988730939359)
  ·
    refine ⟨32125333144772983096409039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21416888763181988730939359 32125333144772983096409039)
    ·
      refine ⟨48187999717159474644613559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32125333144772983096409039 48187999717159474644613559)
      ·
        refine ⟨72281999575739211966920339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48187999717159474644613559 72281999575739211966920339)
        ·
          refine ⟨108422999363608817950380509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72281999575739211966920339 108422999363608817950380509)
          ·
            refine ⟨40658624761353306731392691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108422999363608817950380509 40658624761353306731392691)
            ·
              refine ⟨60987937142029960097089037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40658624761353306731392691 60987937142029960097089037)
              ·
                refine ⟨22870476428261235036408389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60987937142029960097089037 22870476428261235036408389)
                ·
                  refine ⟨4288214330298981569326573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22870476428261235036408389 4288214330298981569326573)
                  ·
                    refine ⟨1608080373862118088497465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4288214330298981569326573 1608080373862118088497465)
                    ·
                      refine ⟨1206060280396588566373099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608080373862118088497465 1206060280396588566373099)
                      ·
                        rfl

theorem cell23_2348794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_2348794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348794 prefixEnd_2348794 := by exact prefixLift 2348794
  have htrace : WordTrace (prefixWord ++ tailWord_2348794) baseStart_2348794 baseEnd_2348794 := by
    simpa [prefixWord, tailWord_2348794, baseEnd_2348794] using wordTrace_append hprefix tailTrace_2348794
  have hstable : (prefixWord ++ tailWord_2348794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348794).length < 2 ^ (prefixWord ++ tailWord_2348794).sum := by decide
  have hdescent : baseEnd_2348794 < baseStart_2348794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348818 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2348818 : Nat := 118140960795 + 2348818 * 2 ^ 59
def prefixEnd_2348818 : Nat := 4983230072969 + 3 ^ 40 * 2348818 * 2
def baseEnd_2348818 : Nat := 1206072603932296472472989

theorem tailTrace_2348818 : CollatzResearch.WordTrace tailWord_2348818 prefixEnd_2348818 1206072603932296472472989 := by
  unfold tailWord_2348818
  simp only [CollatzResearch.WordTrace]
  refine ⟨21417107601160251755657777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57112286936427338015087405 21417107601160251755657777)
  ·
    refine ⟨16062830700870188816743333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21417107601160251755657777 16062830700870188816743333)
    ·
      refine ⟨3011780756413160403139375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16062830700870188816743333 3011780756413160403139375)
      ·
        refine ⟨4517671134619740604709063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3011780756413160403139375 4517671134619740604709063)
        ·
          refine ⟨6776506701929610907063595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517671134619740604709063 6776506701929610907063595)
          ·
            refine ⟨10164760052894416360595393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6776506701929610907063595 10164760052894416360595393)
            ·
              refine ⟨7623570039670812270446545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10164760052894416360595393 7623570039670812270446545)
              ·
                refine ⟨5717677529753109202834909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7623570039670812270446545 5717677529753109202834909)
                ·
                  refine ⟨2144129073657415951063091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5717677529753109202834909 2144129073657415951063091)
                  ·
                    refine ⟨3216193610486123926594637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2144129073657415951063091 3216193610486123926594637)
                    ·
                      refine ⟨1206072603932296472472989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3216193610486123926594637 1206072603932296472472989)
                      ·
                        rfl

theorem cell23_2348818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2348818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348818 prefixEnd_2348818 := by exact prefixLift 2348818
  have htrace : WordTrace (prefixWord ++ tailWord_2348818) baseStart_2348818 baseEnd_2348818 := by
    simpa [prefixWord, tailWord_2348818, baseEnd_2348818] using wordTrace_append hprefix tailTrace_2348818
  have hstable : (prefixWord ++ tailWord_2348818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348818).length < 2 ^ (prefixWord ++ tailWord_2348818).sum := by decide
  have hdescent : baseEnd_2348818 < baseStart_2348818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348824 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2348824 : Nat := 118140960795 + 2348824 * 2 ^ 59
def prefixEnd_2348824 : Nat := 4983230072969 + 3 ^ 40 * 2348824 * 2
def baseEnd_2348824 : Nat := 1206075684816223448997961

theorem tailTrace_2348824 : CollatzResearch.WordTrace tailWord_2348824 prefixEnd_2348824 1206075684816223448997961 := by
  unfold tailWord_2348824
  simp only [CollatzResearch.WordTrace]
  refine ⟨42834324621309635023674763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57112432828412846698233017 42834324621309635023674763)
  ·
    refine ⟨64251486931964452535512145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42834324621309635023674763 64251486931964452535512145)
    ·
      refine ⟨48188615198973339401634109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64251486931964452535512145 48188615198973339401634109)
      ·
        refine ⟨18070730699615002275612791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48188615198973339401634109 18070730699615002275612791)
        ·
          refine ⟨27106096049422503413419187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18070730699615002275612791 27106096049422503413419187)
          ·
            refine ⟨40659144074133755120128781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27106096049422503413419187 40659144074133755120128781)
            ·
              refine ⟨15247179027800158170048293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40659144074133755120128781 15247179027800158170048293)
              ·
                refine ⟨2858846067712529656884055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15247179027800158170048293 2858846067712529656884055)
                ·
                  refine ⟨4288269101568794485326083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858846067712529656884055 4288269101568794485326083)
                  ·
                    refine ⟨6432403652353191727989125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4288269101568794485326083 6432403652353191727989125)
                    ·
                      refine ⟨1206075684816223448997961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6432403652353191727989125 1206075684816223448997961)
                      ·
                        rfl

theorem cell23_2348824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2348824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348824 prefixEnd_2348824 := by exact prefixLift 2348824
  have htrace : WordTrace (prefixWord ++ tailWord_2348824) baseStart_2348824 baseEnd_2348824 := by
    simpa [prefixWord, tailWord_2348824, baseEnd_2348824] using wordTrace_append hprefix tailTrace_2348824
  have hstable : (prefixWord ++ tailWord_2348824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348824).length < 2 ^ (prefixWord ++ tailWord_2348824).sum := by decide
  have hdescent : baseEnd_2348824 < baseStart_2348824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348834 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_2348834 : Nat := 118140960795 + 2348834 * 2 ^ 59
def prefixEnd_2348834 : Nat := 4983230072969 + 3 ^ 40 * 2348834 * 2
def baseEnd_2348834 : Nat := 402026939874256136624305

theorem tailTrace_2348834 : CollatzResearch.WordTrace tailWord_2348834 prefixEnd_2348834 402026939874256136624305 := by
  unfold tailWord_2348834
  simp only [CollatzResearch.WordTrace]
  refine ⟨21417253493145760438803389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57112675981722027836809037 21417253493145760438803389)
  ·
    refine ⟨8031470059929660164551271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21417253493145760438803389 8031470059929660164551271)
    ·
      refine ⟨12047205089894490246826907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8031470059929660164551271 12047205089894490246826907)
      ·
        refine ⟨18070807634841735370240361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12047205089894490246826907 18070807634841735370240361)
        ·
          refine ⟨13553105726131301527680271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18070807634841735370240361 13553105726131301527680271)
          ·
            refine ⟨20329658589196952291520407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13553105726131301527680271 20329658589196952291520407)
            ·
              refine ⟨30494487883795428437280611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20329658589196952291520407 30494487883795428437280611)
              ·
                refine ⟨45741731825693142655920917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30494487883795428437280611 45741731825693142655920917)
                ·
                  refine ⟨2144143679329366061996293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45741731825693142655920917 2144143679329366061996293)
                  ·
                    refine ⟨402026939874256136624305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2144143679329366061996293 402026939874256136624305)
                    ·
                      rfl

theorem cell23_2348834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_2348834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348834 prefixEnd_2348834 := by exact prefixLift 2348834
  have htrace : WordTrace (prefixWord ++ tailWord_2348834) baseStart_2348834 baseEnd_2348834 := by
    simpa [prefixWord, tailWord_2348834, baseEnd_2348834] using wordTrace_append hprefix tailTrace_2348834
  have hstable : (prefixWord ++ tailWord_2348834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348834).length < 2 ^ (prefixWord ++ tailWord_2348834).sum := by decide
  have hdescent : baseEnd_2348834 < baseStart_2348834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348844 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 5]
def baseStart_2348844 : Nat := 118140960795 + 2348844 * 2 ^ 59
def prefixEnd_2348844 : Nat := 4983230072969 + 3 ^ 40 * 2348844 * 2
def baseEnd_2348844 : Nat := 1206085954429313370747869

theorem tailTrace_2348844 : CollatzResearch.WordTrace tailWord_2348844 prefixEnd_2348844 1206085954429313370747869 := by
  unfold tailWord_2348844
  simp only [CollatzResearch.WordTrace]
  refine ⟨42834689351273406731538793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57112919135031208975385057 42834689351273406731538793)
  ·
    refine ⟨32126017013455055048654095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42834689351273406731538793 32126017013455055048654095)
    ·
      refine ⟨48189025520182582572981143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32126017013455055048654095 48189025520182582572981143)
      ·
        refine ⟨72283538280273873859471715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48189025520182582572981143 72283538280273873859471715)
        ·
          refine ⟨108425307420410810789207573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72283538280273873859471715 108425307420410810789207573)
          ·
            refine ⟨5082436285331756755744105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108425307420410810789207573 5082436285331756755744105)
            ·
              refine ⟨3811827213998817566808079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5082436285331756755744105 3811827213998817566808079)
              ·
                refine ⟨5717740820998226350212119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811827213998817566808079 5717740820998226350212119)
                ·
                  refine ⟨8576611231497339525318179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5717740820998226350212119 8576611231497339525318179)
                  ·
                    refine ⟨12864916847246009287977269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8576611231497339525318179 12864916847246009287977269)
                    ·
                      refine ⟨1206085954429313370747869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12864916847246009287977269 1206085954429313370747869)
                      ·
                        rfl

theorem cell23_2348844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_2348844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348844 prefixEnd_2348844 := by exact prefixLift 2348844
  have htrace : WordTrace (prefixWord ++ tailWord_2348844) baseStart_2348844 baseEnd_2348844 := by
    simpa [prefixWord, tailWord_2348844, baseEnd_2348844] using wordTrace_append hprefix tailTrace_2348844
  have hstable : (prefixWord ++ tailWord_2348844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348844).length < 2 ^ (prefixWord ++ tailWord_2348844).sum := by decide
  have hdescent : baseEnd_2348844 < baseStart_2348844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348852 : List Nat := [2, 5, 1, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_2348852 : Nat := 118140960795 + 2348852 * 2 ^ 59
def prefixEnd_2348852 : Nat := 4983230072969 + 3 ^ 40 * 2348852 * 2
def baseEnd_2348852 : Nat := 1206090062274549339447833

theorem tailTrace_2348852 : CollatzResearch.WordTrace tailWord_2348852 prefixEnd_2348852 1206090062274549339447833 := by
  unfold tailWord_2348852
  simp only [CollatzResearch.WordTrace]
  refine ⟨42834835243258915414684405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57113113657678553886245873 42834835243258915414684405)
  ·
    refine ⟨4015765804055523320126663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42834835243258915414684405 4015765804055523320126663)
    ·
      refine ⟨6023648706083284980189995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4015765804055523320126663 6023648706083284980189995)
      ·
        refine ⟨9035473059124927470284993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6023648706083284980189995 9035473059124927470284993)
        ·
          refine ⟨6776604794343695602713745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9035473059124927470284993 6776604794343695602713745)
          ·
            refine ⟨5082453595757771702035309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6776604794343695602713745 5082453595757771702035309)
            ·
              refine ⟨1905920098409164388263241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5082453595757771702035309 1905920098409164388263241)
              ·
                refine ⟨1429440073806873291197431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1905920098409164388263241 1429440073806873291197431)
                ·
                  refine ⟨2144160110710309936796147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429440073806873291197431 2144160110710309936796147)
                  ·
                    refine ⟨3216240166065464905194221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2144160110710309936796147 3216240166065464905194221)
                    ·
                      refine ⟨1206090062274549339447833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3216240166065464905194221 1206090062274549339447833)
                      ·
                        rfl

theorem cell23_2348852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_2348852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348852 prefixEnd_2348852 := by exact prefixLift 2348852
  have htrace : WordTrace (prefixWord ++ tailWord_2348852) baseStart_2348852 baseEnd_2348852 := by
    simpa [prefixWord, tailWord_2348852, baseEnd_2348852] using wordTrace_append hprefix tailTrace_2348852
  have hstable : (prefixWord ++ tailWord_2348852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348852).length < 2 ^ (prefixWord ++ tailWord_2348852).sum := by decide
  have hdescent : baseEnd_2348852 < baseStart_2348852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348858 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2]
def baseStart_2348858 : Nat := 118140960795 + 2348858 * 2 ^ 59
def prefixEnd_2348858 : Nat := 4983230072969 + 3 ^ 40 * 2348858 * 2
def baseEnd_2348858 : Nat := 1206093143158476315972805

theorem tailTrace_2348858 : CollatzResearch.WordTrace tailWord_2348858 prefixEnd_2348858 1206093143158476315972805 := by
  unfold tailWord_2348858
  simp only [CollatzResearch.WordTrace]
  refine ⟨21417472331124023463521807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57113259549664062569391485 21417472331124023463521807)
  ·
    refine ⟨32126208496686035195282711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21417472331124023463521807 32126208496686035195282711)
    ·
      refine ⟨48189312745029052792924067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32126208496686035195282711 48189312745029052792924067)
      ·
        refine ⟨72283969117543579189386101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48189312745029052792924067 72283969117543579189386101)
        ·
          refine ⟨6776622104769710549004947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72283969117543579189386101 6776622104769710549004947)
          ·
            refine ⟨10164933157154565823507421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6776622104769710549004947 10164933157154565823507421)
            ·
              refine ⟨3811849933932962183815283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10164933157154565823507421 3811849933932962183815283)
              ·
                refine ⟨5717774900899443275722925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811849933932962183815283 5717774900899443275722925)
                ·
                  refine ⟨2144165587837291228396097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5717774900899443275722925 2144165587837291228396097)
                  ·
                    refine ⟨1608124190877968421297073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2144165587837291228396097 1608124190877968421297073)
                    ·
                      refine ⟨1206093143158476315972805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608124190877968421297073 1206093143158476315972805)
                      ·
                        rfl

theorem cell23_2348858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_2348858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348858 prefixEnd_2348858 := by exact prefixLift 2348858
  have htrace : WordTrace (prefixWord ++ tailWord_2348858) baseStart_2348858 baseEnd_2348858 := by
    simpa [prefixWord, tailWord_2348858, baseEnd_2348858] using wordTrace_append hprefix tailTrace_2348858
  have hstable : (prefixWord ++ tailWord_2348858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348858).length < 2 ^ (prefixWord ++ tailWord_2348858).sum := by decide
  have hdescent : baseEnd_2348858 < baseStart_2348858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348874 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_2348874 : Nat := 118140960795 + 2348874 * 2 ^ 59
def prefixEnd_2348874 : Nat := 4983230072969 + 3 ^ 40 * 2348874 * 2
def baseEnd_2348874 : Nat := 1206101358848948253372731

theorem tailTrace_2348874 : CollatzResearch.WordTrace tailWord_2348874 prefixEnd_2348874 1206101358848948253372731 := by
  unfold tailWord_2348874
  simp only [CollatzResearch.WordTrace]
  refine ⟨21417618223109532146667419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57113648594958752391113117 21417618223109532146667419)
  ·
    refine ⟨32126427334664298220001129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21417618223109532146667419 32126427334664298220001129)
    ·
      refine ⟨24094820500998223665000847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32126427334664298220001129 24094820500998223665000847)
      ·
        refine ⟨36142230751497335497501271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24094820500998223665000847 36142230751497335497501271)
        ·
          refine ⟨54213346127246003246251907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36142230751497335497501271 54213346127246003246251907)
          ·
            refine ⟨81320019190869004869377861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54213346127246003246251907 81320019190869004869377861)
            ·
              refine ⟨15247503598287938413008349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81320019190869004869377861 15247503598287938413008349)
              ·
                refine ⟨5717813849357976904878131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15247503598287938413008349 5717813849357976904878131)
                ·
                  refine ⟨8576720774036965357317197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5717813849357976904878131 8576720774036965357317197)
                  ·
                    refine ⟨3216270290263862008993949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8576720774036965357317197 3216270290263862008993949)
                    ·
                      refine ⟨1206101358848948253372731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3216270290263862008993949 1206101358848948253372731)
                      ·
                        rfl

theorem cell23_2348874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_2348874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348874 prefixEnd_2348874 := by exact prefixLift 2348874
  have htrace : WordTrace (prefixWord ++ tailWord_2348874) baseStart_2348874 baseEnd_2348874 := by
    simpa [prefixWord, tailWord_2348874, baseEnd_2348874] using wordTrace_append hprefix tailTrace_2348874
  have hstable : (prefixWord ++ tailWord_2348874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348874).length < 2 ^ (prefixWord ++ tailWord_2348874).sum := by decide
  have hdescent : baseEnd_2348874 < baseStart_2348874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348907 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 2, 6]
def baseStart_2348907 : Nat := 118140960795 + 2348907 * 2 ^ 59
def prefixEnd_2348907 : Nat := 4983230072969 + 3 ^ 40 * 2348907 * 2
def baseEnd_2348907 : Nat := 402039434570182208086693

theorem tailTrace_2348907 : CollatzResearch.WordTrace tailWord_2348907 prefixEnd_2348907 402039434570182208086693 := by
  unfold tailWord_2348907
  simp only [CollatzResearch.WordTrace]
  refine ⟨85671676501318575222620975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57114451000879050148413983 85671676501318575222620975)
  ·
    refine ⟨128507514751977862833931463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85671676501318575222620975 128507514751977862833931463)
    ·
      refine ⟨192761272127966794250897195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128507514751977862833931463 192761272127966794250897195)
      ·
        refine ⟨289141908191950191376345793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192761272127966794250897195 289141908191950191376345793)
        ·
          refine ⟨216856431143962643532259345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289141908191950191376345793 216856431143962643532259345)
          ·
            refine ⟨162642323357971982649194509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216856431143962643532259345 162642323357971982649194509)
            ·
              refine ⟨60990871259239493493447941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162642323357971982649194509 60990871259239493493447941)
              ·
                refine ⟨11435788361107405030021489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60990871259239493493447941 11435788361107405030021489)
                ·
                  refine ⟨8576841270830553772516117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11435788361107405030021489 8576841270830553772516117)
                  ·
                    refine ⟨402039434570182208086693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8576841270830553772516117 402039434570182208086693)
                    ·
                      rfl

theorem cell23_2348907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 6].length) (baseStart_2348907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348907 prefixEnd_2348907 := by exact prefixLift 2348907
  have htrace : WordTrace (prefixWord ++ tailWord_2348907) baseStart_2348907 baseEnd_2348907 := by
    simpa [prefixWord, tailWord_2348907, baseEnd_2348907] using wordTrace_append hprefix tailTrace_2348907
  have hstable : (prefixWord ++ tailWord_2348907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348907).length < 2 ^ (prefixWord ++ tailWord_2348907).sum := by decide
  have hdescent : baseEnd_2348907 < baseStart_2348907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348908 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 3]
def baseStart_2348908 : Nat := 118140960795 + 2348908 * 2 ^ 59
def prefixEnd_2348908 : Nat := 4983230072969 + 3 ^ 40 * 2348908 * 2
def baseEnd_2348908 : Nat := 1206118817191201120347575

theorem tailTrace_2348908 : CollatzResearch.WordTrace tailWord_2348908 prefixEnd_2348908 1206118817191201120347575 := by
  unfold tailWord_2348908
  simp only [CollatzResearch.WordTrace]
  refine ⟨42835856487157476196703689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57114475316209968262271585 42835856487157476196703689)
  ·
    refine ⟨32126892365368107147527767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42835856487157476196703689 32126892365368107147527767)
    ·
      refine ⟨48190338548052160721291651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32126892365368107147527767 48190338548052160721291651)
      ·
        refine ⟨72285507822078241081937477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48190338548052160721291651 72285507822078241081937477)
        ·
          refine ⟨13553532716639670202863277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72285507822078241081937477 13553532716639670202863277)
          ·
            refine ⟨5082574768739876326073729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13553532716639670202863277 5082574768739876326073729)
            ·
              refine ⟨3811931076554907244555297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5082574768739876326073729 3811931076554907244555297)
              ·
                refine ⟨2858948307416180433416473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3811931076554907244555297 2858948307416180433416473)
                ·
                  refine ⟨2144211230562135325062355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2858948307416180433416473 2144211230562135325062355)
                  ·
                    refine ⟨3216316845843202987593533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2144211230562135325062355 3216316845843202987593533)
                    ·
                      refine ⟨1206118817191201120347575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3216316845843202987593533 1206118817191201120347575)
                      ·
                        rfl

theorem cell23_2348908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_2348908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348908 prefixEnd_2348908 := by exact prefixLift 2348908
  have htrace : WordTrace (prefixWord ++ tailWord_2348908) baseStart_2348908 baseEnd_2348908 := by
    simpa [prefixWord, tailWord_2348908, baseEnd_2348908] using wordTrace_append hprefix tailTrace_2348908
  have hstable : (prefixWord ++ tailWord_2348908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348908).length < 2 ^ (prefixWord ++ tailWord_2348908).sum := by decide
  have hdescent : baseEnd_2348908 < baseStart_2348908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348931 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 1, 4, 2]
def baseStart_2348931 : Nat := 118140960795 + 2348931 * 2 ^ 59
def prefixEnd_2348931 : Nat := 4983230072969 + 3 ^ 40 * 2348931 * 2
def baseEnd_2348931 : Nat := 1206130627246254530359969

theorem tailTrace_2348931 : CollatzResearch.WordTrace tailWord_2348931 prefixEnd_2348931 1206130627246254530359969 := by
  unfold tailWord_2348931
  simp only [CollatzResearch.WordTrace]
  refine ⟨85672551853231627321494647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57115034568821084880996431 85672551853231627321494647)
  ·
    refine ⟨128508827779847440982241971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85672551853231627321494647 128508827779847440982241971)
    ·
      refine ⟨192763241669771161473362957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128508827779847440982241971 192763241669771161473362957)
      ·
        refine ⟨72286215626164185552511109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192763241669771161473362957 72286215626164185552511109)
        ·
          refine ⟨13553665429905784791095833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72286215626164185552511109 13553665429905784791095833)
          ·
            refine ⟨10165249072429338593321875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13553665429905784791095833 10165249072429338593321875)
            ·
              refine ⟨15247873608644007889982813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10165249072429338593321875 15247873608644007889982813)
              ·
                refine ⟨5717952603241502958743555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15247873608644007889982813 5717952603241502958743555)
                ·
                  refine ⟨8576928904862254438115333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5717952603241502958743555 8576928904862254438115333)
                  ·
                    refine ⟨1608174169661672707146625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8576928904862254438115333 1608174169661672707146625)
                    ·
                      refine ⟨1206130627246254530359969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608174169661672707146625 1206130627246254530359969)
                      ·
                        rfl

theorem cell23_2348931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_2348931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348931 prefixEnd_2348931 := by exact prefixLift 2348931
  have htrace : WordTrace (prefixWord ++ tailWord_2348931) baseStart_2348931 baseEnd_2348931 := by
    simpa [prefixWord, tailWord_2348931, baseEnd_2348931] using wordTrace_append hprefix tailTrace_2348931
  have hstable : (prefixWord ++ tailWord_2348931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348931).length < 2 ^ (prefixWord ++ tailWord_2348931).sum := by decide
  have hdescent : baseEnd_2348931 < baseStart_2348931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348948 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_2348948 : Nat := 118140960795 + 2348948 * 2 ^ 59
def prefixEnd_2348948 : Nat := 4983230072969 + 3 ^ 40 * 2348948 * 2
def baseEnd_2348948 : Nat := 1206139356417380963847391

theorem tailTrace_2348948 : CollatzResearch.WordTrace tailWord_2348948 prefixEnd_2348948 1206139356417380963847391 := by
  unfold tailWord_2348948
  simp only [CollatzResearch.WordTrace]
  refine ⟨42836585947085019612431749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57115447929446692816575665 42836585947085019612431749)
  ·
    refine ⟨8031859865078441177330953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42836585947085019612431749 8031859865078441177330953)
    ·
      refine ⟨6023894898808830882998215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8031859865078441177330953 6023894898808830882998215)
      ·
        refine ⟨9035842348213246324497323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6023894898808830882998215 9035842348213246324497323)
        ·
          refine ⟨13553763522319869486745985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9035842348213246324497323 13553763522319869486745985)
          ·
            refine ⟨10165322641739902115059489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13553763522319869486745985 10165322641739902115059489)
            ·
              refine ⟨7623991981304926586294617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10165322641739902115059489 7623991981304926586294617)
              ·
                refine ⟨5717993985978694939720963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7623991981304926586294617 5717993985978694939720963)
                ·
                  refine ⟨8576990978968042409581445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5717993985978694939720963 8576990978968042409581445)
                  ·
                    refine ⟨1608185808556507951796521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8576990978968042409581445 1608185808556507951796521)
                    ·
                      refine ⟨1206139356417380963847391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608185808556507951796521 1206139356417380963847391)
                      ·
                        rfl

theorem cell23_2348948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_2348948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348948 prefixEnd_2348948 := by exact prefixLift 2348948
  have htrace : WordTrace (prefixWord ++ tailWord_2348948) baseStart_2348948 baseEnd_2348948 := by
    simpa [prefixWord, tailWord_2348948, baseEnd_2348948] using wordTrace_append hprefix tailTrace_2348948
  have hstable : (prefixWord ++ tailWord_2348948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348948).length < 2 ^ (prefixWord ++ tailWord_2348948).sum := by decide
  have hdescent : baseEnd_2348948 < baseStart_2348948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348981 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2348981 : Nat := 118140960795 + 2348981 * 2 ^ 59
def prefixEnd_2348981 : Nat := 4983230072969 + 3 ^ 40 * 2348981 * 2
def baseEnd_2348981 : Nat := 1206156301278979334734739

theorem tailTrace_2348981 : CollatzResearch.WordTrace tailWord_2348981 prefixEnd_2348981 1206156301278979334734739 := by
  unfold tailWord_2348981
  simp only [CollatzResearch.WordTrace]
  refine ⟨85674375503050485860814797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57116250335366990573876531 85674375503050485860814797)
  ·
    refine ⟨32127890813643932197805549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85674375503050485860814797 32127890813643932197805549)
    ·
      refine ⟨12047959055116474574177081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32127890813643932197805549 12047959055116474574177081)
      ·
        refine ⟨9035969291337355930632811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12047959055116474574177081 9035969291337355930632811)
        ·
          refine ⟨13553953937006033895949217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9035969291337355930632811 13553953937006033895949217)
          ·
            refine ⟨10165465452754525421961913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13553953937006033895949217 10165465452754525421961913)
            ·
              refine ⟨7624099089565894066471435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10165465452754525421961913 7624099089565894066471435)
              ·
                refine ⟨11436148634348841099707153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7624099089565894066471435 11436148634348841099707153)
                ·
                  refine ⟨8577111475761630824780365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11436148634348841099707153 8577111475761630824780365)
                  ·
                    refine ⟨3216416803410611559292637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8577111475761630824780365 3216416803410611559292637)
                    ·
                      refine ⟨1206156301278979334734739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3216416803410611559292637 1206156301278979334734739)
                      ·
                        rfl

theorem cell23_2348981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2348981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2348981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2348981 prefixEnd_2348981 := by exact prefixLift 2348981
  have htrace : WordTrace (prefixWord ++ tailWord_2348981) baseStart_2348981 baseEnd_2348981 := by
    simpa [prefixWord, tailWord_2348981, baseEnd_2348981] using wordTrace_append hprefix tailTrace_2348981
  have hstable : (prefixWord ++ tailWord_2348981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348981).length < 2 ^ (prefixWord ++ tailWord_2348981).sum := by decide
  have hdescent : baseEnd_2348981 < baseStart_2348981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349081 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 3, 5, 2]
def baseStart_2349081 : Nat := 118140960795 + 2349081 * 2 ^ 59
def prefixEnd_2349081 : Nat := 4983230072969 + 3 ^ 40 * 2349081 * 2
def baseEnd_2349081 : Nat := 1206207649344428943484279

theorem tailTrace_2349081 : CollatzResearch.WordTrace tailWord_2349081 prefixEnd_2349081 1206207649344428943484279 := by
  unfold tailWord_2349081
  simp only [CollatzResearch.WordTrace]
  refine ⟨85678022802688202939455097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57118681868458801959636731 85678022802688202939455097)
  ·
    refine ⟨64258517102016152204591323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85678022802688202939455097 64258517102016152204591323)
    ·
      refine ⟨96387775653024228306886985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64258517102016152204591323 96387775653024228306886985)
      ·
        refine ⟨72290831739768171230165239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96387775653024228306886985 72290831739768171230165239)
        ·
          refine ⟨108436247609652256845247859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72290831739768171230165239 108436247609652256845247859)
          ·
            refine ⟨162654371414478385267871789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108436247609652256845247859 162654371414478385267871789)
            ·
              refine ⟨60995389280429394475451921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162654371414478385267871789 60995389280429394475451921)
              ·
                refine ⟨45746541960322045856588941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60995389280429394475451921 45746541960322045856588941)
                ·
                  refine ⟨17154953235120767196220853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45746541960322045856588941 17154953235120767196220853)
                  ·
                    refine ⟨1608276865792571924645705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17154953235120767196220853 1608276865792571924645705)
                    ·
                      refine ⟨1206207649344428943484279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608276865792571924645705 1206207649344428943484279)
                      ·
                        rfl

theorem cell23_2349081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_2349081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349081 prefixEnd_2349081 := by exact prefixLift 2349081
  have htrace : WordTrace (prefixWord ++ tailWord_2349081) baseStart_2349081 baseEnd_2349081 := by
    simpa [prefixWord, tailWord_2349081, baseEnd_2349081] using wordTrace_append hprefix tailTrace_2349081
  have hstable : (prefixWord ++ tailWord_2349081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349081).length < 2 ^ (prefixWord ++ tailWord_2349081).sum := by decide
  have hdescent : baseEnd_2349081 < baseStart_2349081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349082 : List Nat := [3, 1, 1, 3, 1, 5, 2, 2, 1, 4]
def baseStart_2349082 : Nat := 118140960795 + 2349082 * 2 ^ 59
def prefixEnd_2349082 : Nat := 4983230072969 + 3 ^ 40 * 2349082 * 2
def baseEnd_2349082 : Nat := 402069387608361146523925

theorem tailTrace_2349082 : CollatzResearch.WordTrace tailWord_2349082 prefixEnd_2349082 402069387608361146523925 := by
  unfold tailWord_2349082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21419514818921145027560375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57118706183789720073494333 21419514818921145027560375)
  ·
    refine ⟨32129272228381717541340563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21419514818921145027560375 32129272228381717541340563)
    ·
      refine ⟨48193908342572576312010845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32129272228381717541340563 48193908342572576312010845)
      ·
        refine ⟨18072715628464716117004067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48193908342572576312010845 18072715628464716117004067)
        ·
          refine ⟨27109073442697074175506101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18072715628464716117004067 27109073442697074175506101)
          ·
            refine ⟨2541475635252850703953697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27109073442697074175506101 2541475635252850703953697)
            ·
              refine ⟨1906106726439638027965273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2541475635252850703953697 1906106726439638027965273)
              ·
                refine ⟨1429580044829728520973955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906106726439638027965273 1429580044829728520973955)
                ·
                  refine ⟨2144370067244592781460933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429580044829728520973955 2144370067244592781460933)
                  ·
                    refine ⟨402069387608361146523925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2144370067244592781460933 402069387608361146523925)
                    ·
                      rfl

theorem cell23_2349082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_2349082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349082 prefixEnd_2349082 := by exact prefixLift 2349082
  have htrace : WordTrace (prefixWord ++ tailWord_2349082) baseStart_2349082 baseEnd_2349082 := by
    simpa [prefixWord, tailWord_2349082, baseEnd_2349082] using wordTrace_append hprefix tailTrace_2349082
  have hstable : (prefixWord ++ tailWord_2349082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349082).length < 2 ^ (prefixWord ++ tailWord_2349082).sum := by decide
  have hdescent : baseEnd_2349082 < baseStart_2349082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349111 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_2349111 : Nat := 118140960795 + 2349111 * 2 ^ 59
def prefixEnd_2349111 : Nat := 4983230072969 + 3 ^ 40 * 2349111 * 2
def baseEnd_2349111 : Nat := 1206223053764063826109141

theorem tailTrace_2349111 : CollatzResearch.WordTrace tailWord_2349111 prefixEnd_2349111 1206223053764063826109141 := by
  unfold tailWord_2349111
  simp only [CollatzResearch.WordTrace]
  refine ⟨85679116992579518063047187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57119411328386345375364791 85679116992579518063047187)
  ·
    refine ⟨128518675488869277094570781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85679116992579518063047187 128518675488869277094570781)
    ·
      refine ⟨48194503308325978910464043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128518675488869277094570781 48194503308325978910464043)
      ·
        refine ⟨72291754962488968365696065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48194503308325978910464043 72291754962488968365696065)
        ·
          refine ⟨54218816221866726274272049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72291754962488968365696065 54218816221866726274272049)
          ·
            refine ⟨40664112166400044705704037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54218816221866726274272049 40664112166400044705704037)
            ·
              refine ⟨7624521031200008382319507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40664112166400044705704037 7624521031200008382319507)
              ·
                refine ⟨11436781546800012573479261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7624521031200008382319507 11436781546800012573479261)
                ·
                  refine ⟨4288793080050004715054723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11436781546800012573479261 4288793080050004715054723)
                  ·
                    refine ⟨6433189620075007072582085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4288793080050004715054723 6433189620075007072582085)
                    ·
                      refine ⟨1206223053764063826109141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6433189620075007072582085 1206223053764063826109141)
                      ·
                        rfl

theorem cell23_2349111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_2349111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349111 prefixEnd_2349111 := by exact prefixLift 2349111
  have htrace : WordTrace (prefixWord ++ tailWord_2349111) baseStart_2349111 baseEnd_2349111 := by
    simpa [prefixWord, tailWord_2349111, baseEnd_2349111] using wordTrace_append hprefix tailTrace_2349111
  have hstable : (prefixWord ++ tailWord_2349111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349111).length < 2 ^ (prefixWord ++ tailWord_2349111).sum := by decide
  have hdescent : baseEnd_2349111 < baseStart_2349111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349145 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 3, 2, 2]
def baseStart_2349145 : Nat := 118140960795 + 2349145 * 2 ^ 59
def prefixEnd_2349145 : Nat := 4983230072969 + 3 ^ 40 * 2349145 * 2
def baseEnd_2349145 : Nat := 1206240512106316693083985

theorem tailTrace_2349145 : CollatzResearch.WordTrace tailWord_2349145 prefixEnd_2349145 1206240512106316693083985 := by
  unfold tailWord_2349145
  simp only [CollatzResearch.WordTrace]
  refine ⟨85680357074456341869784889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57120238049637561246523259 85680357074456341869784889)
  ·
    refine ⟨64260267805842256402338667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85680357074456341869784889 64260267805842256402338667)
    ·
      refine ⟨96390401708763384603508001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64260267805842256402338667 96390401708763384603508001)
      ·
        refine ⟨72292801281572538452631001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96390401708763384603508001 72292801281572538452631001)
        ·
          refine ⟨54219600961179403839473251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72292801281572538452631001 54219600961179403839473251)
          ·
            refine ⟨81329401441769105759209877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54219600961179403839473251 81329401441769105759209877)
            ·
              refine ⟨3812315692582926832462963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81329401441769105759209877 3812315692582926832462963)
              ·
                refine ⟨5718473538874390248694445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812315692582926832462963 5718473538874390248694445)
                ·
                  refine ⟨2144427577077896343260417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5718473538874390248694445 2144427577077896343260417)
                  ·
                    refine ⟨1608320682808422257445313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2144427577077896343260417 1608320682808422257445313)
                    ·
                      refine ⟨1206240512106316693083985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608320682808422257445313 1206240512106316693083985)
                      ·
                        rfl

theorem cell23_2349145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_2349145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349145 prefixEnd_2349145 := by exact prefixLift 2349145
  have htrace : WordTrace (prefixWord ++ tailWord_2349145) baseStart_2349145 baseEnd_2349145 := by
    simpa [prefixWord, tailWord_2349145, baseEnd_2349145] using wordTrace_append hprefix tailTrace_2349145
  have hstable : (prefixWord ++ tailWord_2349145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349145).length < 2 ^ (prefixWord ++ tailWord_2349145).sum := by decide
  have hdescent : baseEnd_2349145 < baseStart_2349145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349148 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2349148 : Nat := 118140960795 + 2349148 * 2 ^ 59
def prefixEnd_2349148 : Nat := 4983230072969 + 3 ^ 40 * 2349148 * 2
def baseEnd_2349148 : Nat := 1206242052548280181346471

theorem tailTrace_2349148 : CollatzResearch.WordTrace tailWord_2349148 prefixEnd_2349148 1206242052548280181346471 := by
  unfold tailWord_2349148
  simp only [CollatzResearch.WordTrace]
  refine ⟨42840233246722736691072049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57120310995630315588096065 42840233246722736691072049)
  ·
    refine ⟨32130174935042052518304037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42840233246722736691072049 32130174935042052518304037)
    ·
      refine ⟨6024407800320384847182007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32130174935042052518304037 6024407800320384847182007)
      ·
        refine ⟨9036611700480577270773011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6024407800320384847182007 9036611700480577270773011)
        ·
          refine ⟨13554917550720865906159517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9036611700480577270773011 13554917550720865906159517)
          ·
            refine ⟨5083094081520324714809819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13554917550720865906159517 5083094081520324714809819)
            ·
              refine ⟨7624641122280487072214729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083094081520324714809819 7624641122280487072214729)
              ·
                refine ⟨5718480841710365304161047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7624641122280487072214729 5718480841710365304161047)
                ·
                  refine ⟨8577721262565547956241571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5718480841710365304161047 8577721262565547956241571)
                  ·
                    refine ⟨12866581893848321934362357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8577721262565547956241571 12866581893848321934362357)
                    ·
                      refine ⟨1206242052548280181346471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12866581893848321934362357 1206242052548280181346471)
                      ·
                        rfl

theorem cell23_2349148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2349148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349148 prefixEnd_2349148 := by exact prefixLift 2349148
  have htrace : WordTrace (prefixWord ++ tailWord_2349148) baseStart_2349148 baseEnd_2349148 := by
    simpa [prefixWord, tailWord_2349148, baseEnd_2349148] using wordTrace_append hprefix tailTrace_2349148
  have hstable : (prefixWord ++ tailWord_2349148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349148).length < 2 ^ (prefixWord ++ tailWord_2349148).sum := by decide
  have hdescent : baseEnd_2349148 < baseStart_2349148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349165 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2349165 : Nat := 118140960795 + 2349165 * 2 ^ 59
def prefixEnd_2349165 : Nat := 4983230072969 + 3 ^ 40 * 2349165 * 2
def baseEnd_2349165 : Nat := 1206250781719406614833893

theorem tailTrace_2349165 : CollatzResearch.WordTrace tailWord_2349165 prefixEnd_2349165 1206250781719406614833893 := by
  unfold tailWord_2349165
  simp only [CollatzResearch.WordTrace]
  refine ⟨85681086534383885285512949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57120724356255923523675299 85681086534383885285512949)
  ·
    refine ⟨8032601862598489245516839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85681086534383885285512949 8032601862598489245516839)
    ·
      refine ⟨12048902793897733868275259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8032601862598489245516839 12048902793897733868275259)
      ·
        refine ⟨18073354190846600802412889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12048902793897733868275259 18073354190846600802412889)
        ·
          refine ⟨13555015643134950601809667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18073354190846600802412889 13555015643134950601809667)
          ·
            refine ⟨20332523464702425902714501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13555015643134950601809667 20332523464702425902714501)
            ·
              refine ⟨3812348149631704856758969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20332523464702425902714501 3812348149631704856758969)
              ·
                refine ⟨2859261112223778642569227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3812348149631704856758969 2859261112223778642569227)
                ·
                  refine ⟨4288891668335667963853841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859261112223778642569227 4288891668335667963853841)
                  ·
                    refine ⟨3216668751251750972890381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4288891668335667963853841 3216668751251750972890381)
                    ·
                      refine ⟨1206250781719406614833893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3216668751251750972890381 1206250781719406614833893)
                      ·
                        rfl

theorem cell23_2349165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2349165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349165 prefixEnd_2349165 := by exact prefixLift 2349165
  have htrace : WordTrace (prefixWord ++ tailWord_2349165) baseStart_2349165 baseEnd_2349165 := by
    simpa [prefixWord, tailWord_2349165, baseEnd_2349165] using wordTrace_append hprefix tailTrace_2349165
  have hstable : (prefixWord ++ tailWord_2349165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349165).length < 2 ^ (prefixWord ++ tailWord_2349165).sum := by decide
  have hdescent : baseEnd_2349165 < baseStart_2349165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349168 : List Nat := [2, 1, 1, 1, 5, 4, 2, 7]
def baseStart_2349168 : Nat := 118140960795 + 2349168 * 2 ^ 59
def prefixEnd_2349168 : Nat := 4983230072969 + 3 ^ 40 * 2349168 * 2
def baseEnd_2349168 : Nat := 44676011931902596410977

theorem tailTrace_2349168 : CollatzResearch.WordTrace tailWord_2349168 prefixEnd_2349168 44676011931902596410977 := by
  unfold tailWord_2349168
  simp only [CollatzResearch.WordTrace]
  refine ⟨42840597976686508398936079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57120797302248677865248105 42840597976686508398936079)
  ·
    refine ⟨64260896965029762598404119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42840597976686508398936079 64260896965029762598404119)
    ·
      refine ⟨96391345447544643897606179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64260896965029762598404119 96391345447544643897606179)
      ·
        refine ⟨144587018171316965846409269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96391345447544643897606179 144587018171316965846409269)
        ·
          refine ⟨13555032953560965548100869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144587018171316965846409269 13555032953560965548100869)
          ·
            refine ⟨2541568678792681040268913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13555032953560965548100869 2541568678792681040268913)
            ·
              refine ⟨1906176509094510780201685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2541568678792681040268913 1906176509094510780201685)
              ·
                refine ⟨44676011931902596410977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1906176509094510780201685 44676011931902596410977)
                ·
                  rfl

theorem cell23_2349168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 7].length) (baseStart_2349168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349168 prefixEnd_2349168 := by exact prefixLift 2349168
  have htrace : WordTrace (prefixWord ++ tailWord_2349168) baseStart_2349168 baseEnd_2349168 := by
    simpa [prefixWord, tailWord_2349168, baseEnd_2349168] using wordTrace_append hprefix tailTrace_2349168
  have hstable : (prefixWord ++ tailWord_2349168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349168).length < 2 ^ (prefixWord ++ tailWord_2349168).sum := by decide
  have hdescent : baseEnd_2349168 < baseStart_2349168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349221 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_2349221 : Nat := 118140960795 + 2349221 * 2 ^ 59
def prefixEnd_2349221 : Nat := 4983230072969 + 3 ^ 40 * 2349221 * 2
def baseEnd_2349221 : Nat := 1206279536636058395733635

theorem tailTrace_2349221 : CollatzResearch.WordTrace tailWord_2349221 prefixEnd_2349221 1206279536636058395733635 := by
  unfold tailWord_2349221
  simp only [CollatzResearch.WordTrace]
  refine ⟨85683129022181006849551517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57122086014787337899701011 85683129022181006849551517)
  ·
    refine ⟨32131173383317877568581819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85683129022181006849551517 32131173383317877568581819)
    ·
      refine ⟨48196760074976816352872729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32131173383317877568581819 48196760074976816352872729)
      ·
        refine ⟨36147570056232612264654547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48196760074976816352872729 36147570056232612264654547)
        ·
          refine ⟨54221355084348918396981821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36147570056232612264654547 54221355084348918396981821)
          ·
            refine ⟨20333008156630844398868183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54221355084348918396981821 20333008156630844398868183)
            ·
              refine ⟨30499512234946266598302275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20333008156630844398868183 30499512234946266598302275)
              ·
                refine ⟨45749268352419399897453413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30499512234946266598302275 45749268352419399897453413)
                ·
                  refine ⟨8577987816078637480772515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45749268352419399897453413 8577987816078637480772515)
                  ·
                    refine ⟨12866981724117956221158773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8577987816078637480772515 12866981724117956221158773)
                    ·
                      refine ⟨1206279536636058395733635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12866981724117956221158773 1206279536636058395733635)
                      ·
                        rfl

theorem cell23_2349221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_2349221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349221 prefixEnd_2349221 := by exact prefixLift 2349221
  have htrace : WordTrace (prefixWord ++ tailWord_2349221) baseStart_2349221 baseEnd_2349221 := by
    simpa [prefixWord, tailWord_2349221, baseEnd_2349221] using wordTrace_append hprefix tailTrace_2349221
  have hstable : (prefixWord ++ tailWord_2349221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349221).length < 2 ^ (prefixWord ++ tailWord_2349221).sum := by decide
  have hdescent : baseEnd_2349221 < baseStart_2349221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349231 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_2349231 : Nat := 118140960795 + 2349231 * 2 ^ 59
def prefixEnd_2349231 : Nat := 4983230072969 + 3 ^ 40 * 2349231 * 2
def baseEnd_2349231 : Nat := 1206284671442603356608589

theorem tailTrace_2349231 : CollatzResearch.WordTrace tailWord_2349231 prefixEnd_2349231 1206284671442603356608589 := by
  unfold tailWord_2349231
  simp only [CollatzResearch.WordTrace]
  refine ⟨85683493752144778557415547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57122329168096519038277031 85683493752144778557415547)
  ·
    refine ⟨128525240628217167836123321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85683493752144778557415547 128525240628217167836123321)
    ·
      refine ⟨96393930471162875877092491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128525240628217167836123321 96393930471162875877092491)
      ·
        refine ⟨144590895706744313815638737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96393930471162875877092491 144590895706744313815638737)
        ·
          refine ⟨108443171780058235361729053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144590895706744313815638737 108443171780058235361729053)
          ·
            refine ⟨40666189417521838260648395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108443171780058235361729053 40666189417521838260648395)
            ·
              refine ⟨60999284126282757390972593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40666189417521838260648395 60999284126282757390972593)
              ·
                refine ⟨45749463094712068043229445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60999284126282757390972593 45749463094712068043229445)
                ·
                  refine ⟨8578024330258512758105521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45749463094712068043229445 8578024330258512758105521)
                  ·
                    refine ⟨6433518247693884568579141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8578024330258512758105521 6433518247693884568579141)
                    ·
                      refine ⟨1206284671442603356608589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6433518247693884568579141 1206284671442603356608589)
                      ·
                        rfl

theorem cell23_2349231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_2349231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349231 prefixEnd_2349231 := by exact prefixLift 2349231
  have htrace : WordTrace (prefixWord ++ tailWord_2349231) baseStart_2349231 baseEnd_2349231 := by
    simpa [prefixWord, tailWord_2349231, baseEnd_2349231] using wordTrace_append hprefix tailTrace_2349231
  have hstable : (prefixWord ++ tailWord_2349231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349231).length < 2 ^ (prefixWord ++ tailWord_2349231).sum := by decide
  have hdescent : baseEnd_2349231 < baseStart_2349231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349271 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 1, 7]
def baseStart_2349271 : Nat := 118140960795 + 2349271 * 2 ^ 59
def prefixEnd_2349271 : Nat := 4983230072969 + 3 ^ 40 * 2349271 * 2
def baseEnd_2349271 : Nat := 402101736889594400036135

theorem tailTrace_2349271 : CollatzResearch.WordTrace tailWord_2349271 prefixEnd_2349271 402101736889594400036135 := by
  unfold tailWord_2349271
  simp only [CollatzResearch.WordTrace]
  refine ⟨85684952671999865388871667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57123301781333243592581111 85684952671999865388871667)
  ·
    refine ⟨128527429007999798083307501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85684952671999865388871667 128527429007999798083307501)
    ·
      refine ⟨48197785877999924281240313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128527429007999798083307501 48197785877999924281240313)
      ·
        refine ⟨36148339408499943210930235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48197785877999924281240313 36148339408499943210930235)
        ·
          refine ⟨54222509112749914816395353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36148339408499943210930235 54222509112749914816395353)
          ·
            refine ⟨40666881834562436112296515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54222509112749914816395353 40666881834562436112296515)
            ·
              refine ⟨61000322751843654168444773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40666881834562436112296515 61000322751843654168444773)
              ·
                refine ⟨11437560515970685156583395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61000322751843654168444773 11437560515970685156583395)
                ·
                  refine ⟨17156340773956027734875093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11437560515970685156583395 17156340773956027734875093)
                  ·
                    refine ⟨402101736889594400036135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17156340773956027734875093 402101736889594400036135)
                    ·
                      rfl

theorem cell23_2349271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_2349271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349271 prefixEnd_2349271 := by exact prefixLift 2349271
  have htrace : WordTrace (prefixWord ++ tailWord_2349271) baseStart_2349271 baseEnd_2349271 := by
    simpa [prefixWord, tailWord_2349271, baseEnd_2349271] using wordTrace_append hprefix tailTrace_2349271
  have hstable : (prefixWord ++ tailWord_2349271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349271).length < 2 ^ (prefixWord ++ tailWord_2349271).sum := by decide
  have hdescent : baseEnd_2349271 < baseStart_2349271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349288 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 1, 7]
def baseStart_2349288 : Nat := 118140960795 + 2349288 * 2 ^ 59
def prefixEnd_2349288 : Nat := 4983230072969 + 3 ^ 40 * 2349288 * 2
def baseEnd_2349288 : Nat := 402104646613303211198609

theorem tailTrace_2349288 : CollatzResearch.WordTrace tailWord_2349288 prefixEnd_2349288 402104646613303211198609 := by
  unfold tailWord_2349288
  simp only [CollatzResearch.WordTrace]
  refine ⟨42842786356469138646120259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57123715141958851528160345 42842786356469138646120259)
  ·
    refine ⟨64264179534703707969180389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42842786356469138646120259 64264179534703707969180389)
    ·
      refine ⟨12049533662756945244221323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64264179534703707969180389 12049533662756945244221323)
      ·
        refine ⟨18074300494135417866331985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12049533662756945244221323 18074300494135417866331985)
        ·
          refine ⟨13555725370601563399748989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18074300494135417866331985 13555725370601563399748989)
          ·
            refine ⟨5083397013975586274905871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13555725370601563399748989 5083397013975586274905871)
            ·
              refine ⟨7625095520963379412358807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083397013975586274905871 7625095520963379412358807)
              ·
                refine ⟨11437643281445069118538211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7625095520963379412358807 11437643281445069118538211)
                ·
                  refine ⟨17156464922167603677807317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11437643281445069118538211 17156464922167603677807317)
                  ·
                    refine ⟨402104646613303211198609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17156464922167603677807317 402104646613303211198609)
                    ·
                      rfl

theorem cell23_2349288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_2349288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349288 prefixEnd_2349288 := by exact prefixLift 2349288
  have htrace : WordTrace (prefixWord ++ tailWord_2349288) baseStart_2349288 baseEnd_2349288 := by
    simpa [prefixWord, tailWord_2349288, baseEnd_2349288] using wordTrace_append hprefix tailTrace_2349288
  have hstable : (prefixWord ++ tailWord_2349288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349288).length < 2 ^ (prefixWord ++ tailWord_2349288).sum := by decide
  have hdescent : baseEnd_2349288 < baseStart_2349288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349335 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 3, 4]
def baseStart_2349335 : Nat := 118140960795 + 2349335 * 2 ^ 59
def prefixEnd_2349335 : Nat := 4983230072969 + 3 ^ 40 * 2349335 * 2
def baseEnd_2349335 : Nat := 402112691143556983236037

theorem tailTrace_2349335 : CollatzResearch.WordTrace tailWord_2349335 prefixEnd_2349335 402112691143556983236037 := by
  unfold tailWord_2349335
  simp only [CollatzResearch.WordTrace]
  refine ⟨85687286943768004319201459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57124857962512002879467639 85687286943768004319201459)
  ·
    refine ⟨128530930415652006478802189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85687286943768004319201459 128530930415652006478802189)
    ·
      refine ⟨48199098905869502429550821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128530930415652006478802189 48199098905869502429550821)
      ·
        refine ⟨9037331044850531705540779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48199098905869502429550821 9037331044850531705540779)
        ·
          refine ⟨13555996567275797558311169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9037331044850531705540779 13555996567275797558311169)
          ·
            refine ⟨10166997425456848168733377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13555996567275797558311169 10166997425456848168733377)
            ·
              refine ⟨7625248069092636126550033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10166997425456848168733377 7625248069092636126550033)
              ·
                refine ⟨5718936051819477094912525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7625248069092636126550033 5718936051819477094912525)
                ·
                  refine ⟨2144601019432303910592197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5718936051819477094912525 2144601019432303910592197)
                  ·
                    refine ⟨402112691143556983236037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2144601019432303910592197 402112691143556983236037)
                    ·
                      rfl

theorem cell23_2349335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_2349335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349335 prefixEnd_2349335 := by exact prefixLift 2349335
  have htrace : WordTrace (prefixWord ++ tailWord_2349335) baseStart_2349335 baseEnd_2349335 := by
    simpa [prefixWord, tailWord_2349335, baseEnd_2349335] using wordTrace_append hprefix tailTrace_2349335
  have hstable : (prefixWord ++ tailWord_2349335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349335).length < 2 ^ (prefixWord ++ tailWord_2349335).sum := by decide
  have hdescent : baseEnd_2349335 < baseStart_2349335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349342 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2349342 : Nat := 118140960795 + 2349342 * 2 ^ 59
def prefixEnd_2349342 : Nat := 4983230072969 + 3 ^ 40 * 2349342 * 2
def baseEnd_2349342 : Nat := 1206341667795252422320579

theorem tailTrace_2349342 : CollatzResearch.WordTrace tailWord_2349342 prefixEnd_2349342 1206341667795252422320579 := by
  unfold tailWord_2349342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10710942781842830564338285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57125028169828429676470853 10710942781842830564338285)
  ·
    refine ⟨4016603543191061461626857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10710942781842830564338285 4016603543191061461626857)
    ·
      refine ⟨3012452657393296096220143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4016603543191061461626857 3012452657393296096220143)
      ·
        refine ⟨4518678986089944144330215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012452657393296096220143 4518678986089944144330215)
        ·
          refine ⟨6778018479134916216495323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4518678986089944144330215 6778018479134916216495323)
          ·
            refine ⟨10167027718702374324742985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778018479134916216495323 10167027718702374324742985)
            ·
              refine ⟨7625270789026780743557239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10167027718702374324742985 7625270789026780743557239)
              ·
                refine ⟨11437906183540171115335859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7625270789026780743557239 11437906183540171115335859)
                ·
                  refine ⟨17156859275310256673003789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11437906183540171115335859 17156859275310256673003789)
                  ·
                    refine ⟨6433822228241346252376421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17156859275310256673003789 6433822228241346252376421)
                    ·
                      refine ⟨1206341667795252422320579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6433822228241346252376421 1206341667795252422320579)
                      ·
                        rfl

theorem cell23_2349342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2349342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349342 prefixEnd_2349342 := by exact prefixLift 2349342
  have htrace : WordTrace (prefixWord ++ tailWord_2349342) baseStart_2349342 baseEnd_2349342 := by
    simpa [prefixWord, tailWord_2349342, baseEnd_2349342] using wordTrace_append hprefix tailTrace_2349342
  have hstable : (prefixWord ++ tailWord_2349342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349342).length < 2 ^ (prefixWord ++ tailWord_2349342).sum := by decide
  have hdescent : baseEnd_2349342 < baseStart_2349342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349348 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 8]
def baseStart_2349348 : Nat := 118140960795 + 2349348 * 2 ^ 59
def prefixEnd_2349348 : Nat := 4983230072969 + 3 ^ 40 * 2349348 * 2
def baseEnd_2349348 : Nat := 134038305408797710982839

theorem tailTrace_2349348 : CollatzResearch.WordTrace tailWord_2349348 prefixEnd_2349348 134038305408797710982839 := by
  unfold tailWord_2349348
  simp only [CollatzResearch.WordTrace]
  refine ⟨42843880546360453769712349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57125174061813938359616465 42843880546360453769712349)
  ·
    refine ⟨16066455204885170163642131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42843880546360453769712349 16066455204885170163642131)
    ·
      refine ⟨24099682807327755245463197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16066455204885170163642131 24099682807327755245463197)
      ·
        refine ⟨9037381052747908217048699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24099682807327755245463197 9037381052747908217048699)
        ·
          refine ⟨13556071579121862325573049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9037381052747908217048699 13556071579121862325573049)
          ·
            refine ⟨10167053684341396744179787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13556071579121862325573049 10167053684341396744179787)
            ·
              refine ⟨15250580526512095116269681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10167053684341396744179787 15250580526512095116269681)
              ·
                refine ⟨11437935394884071337202261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15250580526512095116269681 11437935394884071337202261)
                ·
                  refine ⟨134038305408797710982839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11437935394884071337202261 134038305408797710982839)
                  ·
                    rfl

theorem cell23_2349348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_2349348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349348 prefixEnd_2349348 := by exact prefixLift 2349348
  have htrace : WordTrace (prefixWord ++ tailWord_2349348) baseStart_2349348 baseEnd_2349348 := by
    simpa [prefixWord, tailWord_2349348, baseEnd_2349348] using wordTrace_append hprefix tailTrace_2349348
  have hstable : (prefixWord ++ tailWord_2349348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349348).length < 2 ^ (prefixWord ++ tailWord_2349348).sum := by decide
  have hdescent : baseEnd_2349348 < baseStart_2349348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349362 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_2349362 : Nat := 118140960795 + 2349362 * 2 ^ 59
def prefixEnd_2349362 : Nat := 4983230072969 + 3 ^ 40 * 2349362 * 2
def baseEnd_2349362 : Nat := 1206351937408342344070487

theorem tailTrace_2349362 : CollatzResearch.WordTrace tailWord_2349362 prefixEnd_2349362 1206351937408342344070487 := by
  unfold tailWord_2349362
  simp only [CollatzResearch.WordTrace]
  refine ⟨21422067928667546982608585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57125514476446791953622893 21422067928667546982608585)
  ·
    refine ⟨16066550946500660236956439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21422067928667546982608585 16066550946500660236956439)
    ·
      refine ⟨24099826419750990355434659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16066550946500660236956439 24099826419750990355434659)
      ·
        refine ⟨36149739629626485533151989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24099826419750990355434659 36149739629626485533151989)
        ·
          refine ⟨3389038090277483018732999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36149739629626485533151989 3389038090277483018732999)
          ·
            refine ⟨5083557135416224528099499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389038090277483018732999 5083557135416224528099499)
            ·
              refine ⟨7625335703124336792149249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083557135416224528099499 7625335703124336792149249)
              ·
                refine ⟨5719001777343252594111937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7625335703124336792149249 5719001777343252594111937)
                ·
                  refine ⟨4289251333007439445583953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5719001777343252594111937 4289251333007439445583953)
                  ·
                    refine ⟨3216938499755579584187965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4289251333007439445583953 3216938499755579584187965)
                    ·
                      refine ⟨1206351937408342344070487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3216938499755579584187965 1206351937408342344070487)
                      ·
                        rfl

theorem cell23_2349362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_2349362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349362 prefixEnd_2349362 := by exact prefixLift 2349362
  have htrace : WordTrace (prefixWord ++ tailWord_2349362) baseStart_2349362 baseEnd_2349362 := by
    simpa [prefixWord, tailWord_2349362, baseEnd_2349362] using wordTrace_append hprefix tailTrace_2349362
  have hstable : (prefixWord ++ tailWord_2349362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349362).length < 2 ^ (prefixWord ++ tailWord_2349362).sum := by decide
  have hdescent : baseEnd_2349362 < baseStart_2349362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349385 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 6, 3, 2]
def baseStart_2349385 : Nat := 118140960795 + 2349385 * 2 ^ 59
def prefixEnd_2349385 : Nat := 4983230072969 + 3 ^ 40 * 2349385 * 2
def baseEnd_2349385 : Nat := 1206363747463395754082881

theorem tailTrace_2349385 : CollatzResearch.WordTrace tailWord_2349385 prefixEnd_2349385 1206363747463395754082881 := by
  unfold tailWord_2349385
  simp only [CollatzResearch.WordTrace]
  refine ⟨85689110593586862858521609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57126073729057908572347739 85689110593586862858521609)
  ·
    refine ⟨64266832945190147143891207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85689110593586862858521609 64266832945190147143891207)
    ·
      refine ⟨96400249417785220715836811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64266832945190147143891207 96400249417785220715836811)
      ·
        refine ⟨144600374126677831073755217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96400249417785220715836811 144600374126677831073755217)
        ·
          refine ⟨108450280595008373305316413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144600374126677831073755217 108450280595008373305316413)
          ·
            refine ⟨40668855223128139989493655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108450280595008373305316413 40668855223128139989493655)
            ·
              refine ⟨61003282834692209984240483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40668855223128139989493655 61003282834692209984240483)
              ·
                refine ⟨91504924252038314976360725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61003282834692209984240483 91504924252038314976360725)
                ·
                  refine ⟨4289293324314296014516909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91504924252038314976360725 4289293324314296014516909)
                  ·
                    refine ⟨1608484996617861005443841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4289293324314296014516909 1608484996617861005443841)
                    ·
                      refine ⟨1206363747463395754082881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608484996617861005443841 1206363747463395754082881)
                      ·
                        rfl

theorem cell23_2349385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 3, 2].length) (baseStart_2349385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349385 prefixEnd_2349385 := by exact prefixLift 2349385
  have htrace : WordTrace (prefixWord ++ tailWord_2349385) baseStart_2349385 baseEnd_2349385 := by
    simpa [prefixWord, tailWord_2349385, baseEnd_2349385] using wordTrace_append hprefix tailTrace_2349385
  have hstable : (prefixWord ++ tailWord_2349385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349385).length < 2 ^ (prefixWord ++ tailWord_2349385).sum := by decide
  have hdescent : baseEnd_2349385 < baseStart_2349385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349412 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_2349412 : Nat := 118140960795 + 2349412 * 2 ^ 59
def prefixEnd_2349412 : Nat := 4983230072969 + 3 ^ 40 * 2349412 * 2
def baseEnd_2349412 : Nat := 402125870480355716148419

theorem tailTrace_2349412 : CollatzResearch.WordTrace tailWord_2349412 prefixEnd_2349412 402125870480355716148419 := by
  unfold tailWord_2349412
  simp only [CollatzResearch.WordTrace]
  refine ⟨42845047682244523234877245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57126730242992697646502993 42845047682244523234877245)
  ·
    refine ⟨16066892880841696213078967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42845047682244523234877245 16066892880841696213078967)
    ·
      refine ⟨24100339321262544319618451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16066892880841696213078967 24100339321262544319618451)
      ·
        refine ⟨36150508981893816479427677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24100339321262544319618451 36150508981893816479427677)
        ·
          refine ⟨13556440868210181179785379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36150508981893816479427677 13556440868210181179785379)
          ·
            refine ⟨20334661302315271769678069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13556440868210181179785379 20334661302315271769678069)
            ·
              refine ⟨1906374497092056728407319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20334661302315271769678069 1906374497092056728407319)
              ·
                refine ⟨2859561745638085092610979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906374497092056728407319 2859561745638085092610979)
                ·
                  refine ⟨4289342618457127638916469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859561745638085092610979 4289342618457127638916469)
                  ·
                    refine ⟨402125870480355716148419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4289342618457127638916469 402125870480355716148419)
                    ·
                      rfl

theorem cell23_2349412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_2349412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349412 prefixEnd_2349412 := by exact prefixLift 2349412
  have htrace : WordTrace (prefixWord ++ tailWord_2349412) baseStart_2349412 baseEnd_2349412 := by
    simpa [prefixWord, tailWord_2349412, baseEnd_2349412] using wordTrace_append hprefix tailTrace_2349412
  have hstable : (prefixWord ++ tailWord_2349412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349412).length < 2 ^ (prefixWord ++ tailWord_2349412).sum := by decide
  have hdescent : baseEnd_2349412 < baseStart_2349412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349426 : List Nat := [3, 2, 1, 2, 1, 3, 4, 2, 1, 1, 3]
def baseStart_2349426 : Nat := 118140960795 + 2349426 * 2 ^ 59
def prefixEnd_2349426 : Nat := 4983230072969 + 3 ^ 40 * 2349426 * 2
def baseEnd_2349426 : Nat := 1206384800170230093670193

theorem tailTrace_2349426 : CollatzResearch.WordTrace tailWord_2349426 prefixEnd_2349426 1206384800170230093670193 := by
  unfold tailWord_2349426
  simp only [CollatzResearch.WordTrace]
  refine ⟨21422651496609581715191033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57127070657625551240509421 21422651496609581715191033)
  ·
    refine ⟨16066988622457186286393275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21422651496609581715191033 16066988622457186286393275)
    ·
      refine ⟨24100482933685779429589913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16066988622457186286393275 24100482933685779429589913)
      ·
        refine ⟨18075362200264334572192435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24100482933685779429589913 18075362200264334572192435)
        ·
          refine ⟨27113043300396501858288653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18075362200264334572192435 27113043300396501858288653)
          ·
            refine ⟨10167391237648688196858245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27113043300396501858288653 10167391237648688196858245)
            ·
              refine ⟨1906385857059129036910921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10167391237648688196858245 1906385857059129036910921)
              ·
                refine ⟨1429789392794346777683191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906385857059129036910921 1429789392794346777683191)
                ·
                  refine ⟨2144684089191520166524787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429789392794346777683191 2144684089191520166524787)
                  ·
                    refine ⟨3217026133787280249787181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2144684089191520166524787 3217026133787280249787181)
                    ·
                      refine ⟨1206384800170230093670193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3217026133787280249787181 1206384800170230093670193)
                      ·
                        rfl

theorem cell23_2349426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_2349426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349426 prefixEnd_2349426 := by exact prefixLift 2349426
  have htrace : WordTrace (prefixWord ++ tailWord_2349426) baseStart_2349426 baseEnd_2349426 := by
    simpa [prefixWord, tailWord_2349426, baseEnd_2349426] using wordTrace_append hprefix tailTrace_2349426
  have hstable : (prefixWord ++ tailWord_2349426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349426).length < 2 ^ (prefixWord ++ tailWord_2349426).sum := by decide
  have hdescent : baseEnd_2349426 < baseStart_2349426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349435 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 3]
def baseStart_2349435 : Nat := 118140960795 + 2349435 * 2 ^ 59
def prefixEnd_2349435 : Nat := 4983230072969 + 3 ^ 40 * 2349435 * 2
def baseEnd_2349435 : Nat := 1206389421496120558457651

theorem tailTrace_2349435 : CollatzResearch.WordTrace tailWord_2349435 prefixEnd_2349435 1206389421496120558457651 := by
  unfold tailWord_2349435
  simp only [CollatzResearch.WordTrace]
  refine ⟨85690934243405721397841759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57127289495603814265227839 85690934243405721397841759)
  ·
    refine ⟨128536401365108582096762639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85690934243405721397841759 128536401365108582096762639)
    ·
      refine ⟨192804602047662873145143959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128536401365108582096762639 192804602047662873145143959)
      ·
        refine ⟨289206903071494309717715939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192804602047662873145143959 289206903071494309717715939)
        ·
          refine ⟨433810354607241464576573909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289206903071494309717715939 433810354607241464576573909)
          ·
            refine ⟨10167430186107221826013451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 433810354607241464576573909 10167430186107221826013451)
            ·
              refine ⟨15251145279160832739020177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10167430186107221826013451 15251145279160832739020177)
              ·
                refine ⟨11438358959370624554265133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15251145279160832739020177 11438358959370624554265133)
                ·
                  refine ⟨4289384609763984207849425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11438358959370624554265133 4289384609763984207849425)
                  ·
                    refine ⟨3217038457322988155887069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4289384609763984207849425 3217038457322988155887069)
                    ·
                      refine ⟨1206389421496120558457651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3217038457322988155887069 1206389421496120558457651)
                      ·
                        rfl

theorem cell23_2349435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 3].length) (baseStart_2349435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349435 prefixEnd_2349435 := by exact prefixLift 2349435
  have htrace : WordTrace (prefixWord ++ tailWord_2349435) baseStart_2349435 baseEnd_2349435 := by
    simpa [prefixWord, tailWord_2349435, baseEnd_2349435] using wordTrace_append hprefix tailTrace_2349435
  have hstable : (prefixWord ++ tailWord_2349435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349435).length < 2 ^ (prefixWord ++ tailWord_2349435).sum := by decide
  have hdescent : baseEnd_2349435 < baseStart_2349435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349449 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 3, 2, 2]
def baseStart_2349449 : Nat := 118140960795 + 2349449 * 2 ^ 59
def prefixEnd_2349449 : Nat := 4983230072969 + 3 ^ 40 * 2349449 * 2
def baseEnd_2349449 : Nat := 1206396610225283503682587

theorem tailTrace_2349449 : CollatzResearch.WordTrace tailWord_2349449 prefixEnd_2349449 1206396610225283503682587 := by
  unfold tailWord_2349449
  simp only [CollatzResearch.WordTrace]
  refine ⟨85691444865355001788851401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57127629910236667859234267 85691444865355001788851401)
  ·
    refine ⟨64268583649016251341638551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85691444865355001788851401 64268583649016251341638551)
    ·
      refine ⟨96402875473524377012457827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64268583649016251341638551 96402875473524377012457827)
      ·
        refine ⟨144604313210286565518686741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96402875473524377012457827 144604313210286565518686741)
        ·
          refine ⟨6778327181732182758688441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 144604313210286565518686741 6778327181732182758688441)
          ·
            refine ⟨5083745386299137069016331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6778327181732182758688441 5083745386299137069016331)
            ·
              refine ⟨7625618079448705603524497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083745386299137069016331 7625618079448705603524497)
              ·
                refine ⟨5719213559586529202643373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7625618079448705603524497 5719213559586529202643373)
                ·
                  refine ⟨2144705084844948450991265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5719213559586529202643373 2144705084844948450991265)
                  ·
                    refine ⟨1608528813633711338243449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2144705084844948450991265 1608528813633711338243449)
                    ·
                      refine ⟨1206396610225283503682587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608528813633711338243449 1206396610225283503682587)
                      ·
                        rfl

theorem cell23_2349449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 2, 2].length) (baseStart_2349449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349449 prefixEnd_2349449 := by exact prefixLift 2349449
  have htrace : WordTrace (prefixWord ++ tailWord_2349449) baseStart_2349449 baseEnd_2349449 := by
    simpa [prefixWord, tailWord_2349449, baseEnd_2349449] using wordTrace_append hprefix tailTrace_2349449
  have hstable : (prefixWord ++ tailWord_2349449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349449).length < 2 ^ (prefixWord ++ tailWord_2349449).sum := by decide
  have hdescent : baseEnd_2349449 < baseStart_2349449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349465 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 1, 3, 3]
def baseStart_2349465 : Nat := 118140960795 + 2349465 * 2 ^ 59
def prefixEnd_2349465 : Nat := 4983230072969 + 3 ^ 40 * 2349465 * 2
def baseEnd_2349465 : Nat := 1206404825915755441082513

theorem tailTrace_2349465 : CollatzResearch.WordTrace tailWord_2349465 prefixEnd_2349465 1206404825915755441082513 := by
  unfold tailWord_2349465
  simp only [CollatzResearch.WordTrace]
  refine ⟨85692028433297036521433849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57128018955531357680955899 85692028433297036521433849)
  ·
    refine ⟨64269021324972777391075387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85692028433297036521433849 64269021324972777391075387)
    ·
      refine ⟨96403531987459166086613081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64269021324972777391075387 96403531987459166086613081)
      ·
        refine ⟨72302648990594374564959811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96403531987459166086613081 72302648990594374564959811)
        ·
          refine ⟨108453973485891561847439717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72302648990594374564959811 108453973485891561847439717)
          ·
            refine ⟨20335120028604667846394947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108453973485891561847439717 20335120028604667846394947)
            ·
              refine ⟨30502680042907001769592421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20335120028604667846394947 30502680042907001769592421)
              ·
                refine ⟨5719252508045062831798579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30502680042907001769592421 5719252508045062831798579)
                ·
                  refine ⟨8578878762067594247697869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5719252508045062831798579 8578878762067594247697869)
                  ·
                    refine ⟨3217079535775347842886701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8578878762067594247697869 3217079535775347842886701)
                    ·
                      refine ⟨1206404825915755441082513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3217079535775347842886701 1206404825915755441082513)
                      ·
                        rfl

theorem cell23_2349465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_2349465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349465 prefixEnd_2349465 := by exact prefixLift 2349465
  have htrace : WordTrace (prefixWord ++ tailWord_2349465) baseStart_2349465 baseEnd_2349465 := by
    simpa [prefixWord, tailWord_2349465, baseEnd_2349465] using wordTrace_append hprefix tailTrace_2349465
  have hstable : (prefixWord ++ tailWord_2349465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349465).length < 2 ^ (prefixWord ++ tailWord_2349465).sum := by decide
  have hdescent : baseEnd_2349465 < baseStart_2349465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349466 : List Nat := [3, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2]
def baseStart_2349466 : Nat := 118140960795 + 2349466 * 2 ^ 59
def prefixEnd_2349466 : Nat := 4983230072969 + 3 ^ 40 * 2349466 * 2
def baseEnd_2349466 : Nat := 1206405339396409937170009

theorem tailTrace_2349466 : CollatzResearch.WordTrace tailWord_2349466 prefixEnd_2349466 1206405339396409937170009 := by
  unfold tailWord_2349466
  simp only [CollatzResearch.WordTrace]
  refine ⟨21423016226573353423055063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57128043270862275794813501 21423016226573353423055063)
  ·
    refine ⟨32134524339860030134582595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21423016226573353423055063 32134524339860030134582595)
    ·
      refine ⟨48201786509790045201873893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32134524339860030134582595 48201786509790045201873893)
      ·
        refine ⟨9037834970585633475351355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48201786509790045201873893 9037834970585633475351355)
        ·
          refine ⟨13556752455878450213027033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9037834970585633475351355 13556752455878450213027033)
          ·
            refine ⟨10167564341908837659770275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13556752455878450213027033 10167564341908837659770275)
            ·
              refine ⟨15251346512863256489655413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10167564341908837659770275 15251346512863256489655413)
              ·
                refine ⟨1429813735580930295905195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15251346512863256489655413 1429813735580930295905195)
                ·
                  refine ⟨2144720603371395443857793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429813735580930295905195 2144720603371395443857793)
                  ·
                    refine ⟨1608540452528546582893345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2144720603371395443857793 1608540452528546582893345)
                    ·
                      refine ⟨1206405339396409937170009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608540452528546582893345 1206405339396409937170009)
                      ·
                        rfl

theorem cell23_2349466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_2349466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349466 prefixEnd_2349466 := by exact prefixLift 2349466
  have htrace : WordTrace (prefixWord ++ tailWord_2349466) baseStart_2349466 baseEnd_2349466 := by
    simpa [prefixWord, tailWord_2349466, baseEnd_2349466] using wordTrace_append hprefix tailTrace_2349466
  have hstable : (prefixWord ++ tailWord_2349466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349466).length < 2 ^ (prefixWord ++ tailWord_2349466).sum := by decide
  have hdescent : baseEnd_2349466 < baseStart_2349466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349469 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_2349469 : Nat := 118140960795 + 2349469 * 2 ^ 59
def prefixEnd_2349469 : Nat := 4983230072969 + 3 ^ 40 * 2349469 * 2
def baseEnd_2349469 : Nat := 1206406879838373425432495

theorem tailTrace_2349469 : CollatzResearch.WordTrace tailWord_2349469 prefixEnd_2349469 1206406879838373425432495 := by
  unfold tailWord_2349469
  simp only [CollatzResearch.WordTrace]
  refine ⟨85692174325282545204579461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57128116216855030136386307 85692174325282545204579461)
  ·
    refine ⟨16067282685990477225858649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85692174325282545204579461 16067282685990477225858649)
    ·
      refine ⟨12050462014492857919393987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16067282685990477225858649 12050462014492857919393987)
      ·
        refine ⟨18075693021739286879090981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12050462014492857919393987 18075693021739286879090981)
        ·
          refine ⟨3389192441576116289829559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18075693021739286879090981 3389192441576116289829559)
          ·
            refine ⟨5083788662364174434744339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389192441576116289829559 5083788662364174434744339)
            ·
              refine ⟨7625682993546261652116509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083788662364174434744339 7625682993546261652116509)
              ·
                refine ⟨2859631122579848119543691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7625682993546261652116509 2859631122579848119543691)
                ·
                  refine ⟨4289446683869772179315537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859631122579848119543691 4289446683869772179315537)
                  ·
                    refine ⟨3217085012902329134486653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4289446683869772179315537 3217085012902329134486653)
                    ·
                      refine ⟨1206406879838373425432495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3217085012902329134486653 1206406879838373425432495)
                      ·
                        rfl

theorem cell23_2349469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_2349469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349469 prefixEnd_2349469 := by exact prefixLift 2349469
  have htrace : WordTrace (prefixWord ++ tailWord_2349469) baseStart_2349469 baseEnd_2349469 := by
    simpa [prefixWord, tailWord_2349469, baseEnd_2349469] using wordTrace_append hprefix tailTrace_2349469
  have hstable : (prefixWord ++ tailWord_2349469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349469).length < 2 ^ (prefixWord ++ tailWord_2349469).sum := by decide
  have hdescent : baseEnd_2349469 < baseStart_2349469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349525 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2349525 : Nat := 118140960795 + 2349525 * 2 ^ 59
def prefixEnd_2349525 : Nat := 4983230072969 + 3 ^ 40 * 2349525 * 2
def baseEnd_2349525 : Nat := 1206435634755025206332237

theorem tailTrace_2349525 : CollatzResearch.WordTrace tailWord_2349525 prefixEnd_2349525 1206435634755025206332237 := by
  unfold tailWord_2349525
  simp only [CollatzResearch.WordTrace]
  refine ⟨85694216813079666768618029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57129477875386444512412019 85694216813079666768618029)
  ·
    refine ⟨32135331304904875038231761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85694216813079666768618029 32135331304904875038231761)
    ·
      refine ⟨24101498478678656278673821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32135331304904875038231761 24101498478678656278673821)
      ·
        refine ⟨9038061929504496104502683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24101498478678656278673821 9038061929504496104502683)
        ·
          refine ⟨13557092894256744156754025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9038061929504496104502683 13557092894256744156754025)
          ·
            refine ⟨10167819670692558117565519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13557092894256744156754025 10167819670692558117565519)
            ·
              refine ⟨15251729506038837176348279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10167819670692558117565519 15251729506038837176348279)
              ·
                refine ⟨22877594259058255764522419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15251729506038837176348279 22877594259058255764522419)
                ·
                  refine ⟨34316391388587383646783629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22877594259058255764522419 34316391388587383646783629)
                  ·
                    refine ⟨12868646770720268867543861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34316391388587383646783629 12868646770720268867543861)
                    ·
                      refine ⟨1206435634755025206332237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12868646770720268867543861 1206435634755025206332237)
                      ·
                        rfl

theorem cell23_2349525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2349525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349525 prefixEnd_2349525 := by exact prefixLift 2349525
  have htrace : WordTrace (prefixWord ++ tailWord_2349525) baseStart_2349525 baseEnd_2349525 := by
    simpa [prefixWord, tailWord_2349525, baseEnd_2349525] using wordTrace_append hprefix tailTrace_2349525
  have hstable : (prefixWord ++ tailWord_2349525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349525).length < 2 ^ (prefixWord ++ tailWord_2349525).sum := by decide
  have hdescent : baseEnd_2349525 < baseStart_2349525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349526 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_2349526 : Nat := 118140960795 + 2349526 * 2 ^ 59
def prefixEnd_2349526 : Nat := 4983230072969 + 3 ^ 40 * 2349526 * 2
def baseEnd_2349526 : Nat := 1206436148235679702419733

theorem tailTrace_2349526 : CollatzResearch.WordTrace tailWord_2349526 prefixEnd_2349526 1206436148235679702419733 := by
  unfold tailWord_2349526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5355890830379752746212777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57129502190717362626269621 5355890830379752746212777)
  ·
    refine ⟨4016918122784814559659583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5355890830379752746212777 4016918122784814559659583)
    ·
      refine ⟨6025377184177221839489375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4016918122784814559659583 6025377184177221839489375)
      ·
        refine ⟨9038065776265832759234063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6025377184177221839489375 9038065776265832759234063)
        ·
          refine ⟨13557098664398749138851095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9038065776265832759234063 13557098664398749138851095)
          ·
            refine ⟨20335647996598123708276643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13557098664398749138851095 20335647996598123708276643)
            ·
              refine ⟨30503471994897185562414965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20335647996598123708276643 30503471994897185562414965)
              ·
                refine ⟨2859700499521611146476403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30503471994897185562414965 2859700499521611146476403)
                ·
                  refine ⟨4289550749282416719714605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859700499521611146476403 4289550749282416719714605)
                  ·
                    refine ⟨1608581530980906269892977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4289550749282416719714605 1608581530980906269892977)
                    ·
                      refine ⟨1206436148235679702419733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608581530980906269892977 1206436148235679702419733)
                      ·
                        rfl

theorem cell23_2349526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_2349526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349526 prefixEnd_2349526 := by exact prefixLift 2349526
  have htrace : WordTrace (prefixWord ++ tailWord_2349526) baseStart_2349526 baseEnd_2349526 := by
    simpa [prefixWord, tailWord_2349526, baseEnd_2349526] using wordTrace_append hprefix tailTrace_2349526
  have hstable : (prefixWord ++ tailWord_2349526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349526).length < 2 ^ (prefixWord ++ tailWord_2349526).sum := by decide
  have hdescent : baseEnd_2349526 < baseStart_2349526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349555 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 3]
def baseStart_2349555 : Nat := 118140960795 + 2349555 * 2 ^ 59
def prefixEnd_2349555 : Nat := 4983230072969 + 3 ^ 40 * 2349555 * 2
def baseEnd_2349555 : Nat := 1206451039174660088957099

theorem tailTrace_2349555 : CollatzResearch.WordTrace tailWord_2349555 prefixEnd_2349555 1206451039174660088957099 := by
  unfold tailWord_2349555
  simp only [CollatzResearch.WordTrace]
  refine ⟨85695311002970981892210119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57130207335313987928140079 85695311002970981892210119)
  ·
    refine ⟨128542966504456472838315179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85695311002970981892210119 128542966504456472838315179)
    ·
      refine ⟨192814449756684709257472769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128542966504456472838315179 192814449756684709257472769)
      ·
        refine ⟨144610837317513531943104577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192814449756684709257472769 144610837317513531943104577)
        ·
          refine ⟨108458127988135148957328433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144610837317513531943104577 108458127988135148957328433)
          ·
            refine ⟨81343595991101361717996325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108458127988135148957328433 81343595991101361717996325)
            ·
              refine ⟨15251924248331505322124311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81343595991101361717996325 15251924248331505322124311)
              ·
                refine ⟨22877886372497257983186467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15251924248331505322124311 22877886372497257983186467)
                ·
                  refine ⟨34316829558745886974779701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22877886372497257983186467 34316829558745886974779701)
                  ·
                    refine ⟨3217202771132426903885597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34316829558745886974779701 3217202771132426903885597)
                    ·
                      refine ⟨1206451039174660088957099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3217202771132426903885597 1206451039174660088957099)
                      ·
                        rfl

theorem cell23_2349555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 3].length) (baseStart_2349555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349555 prefixEnd_2349555 := by exact prefixLift 2349555
  have htrace : WordTrace (prefixWord ++ tailWord_2349555) baseStart_2349555 baseEnd_2349555 := by
    simpa [prefixWord, tailWord_2349555, baseEnd_2349555] using wordTrace_append hprefix tailTrace_2349555
  have hstable : (prefixWord ++ tailWord_2349555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349555).length < 2 ^ (prefixWord ++ tailWord_2349555).sum := by decide
  have hdescent : baseEnd_2349555 < baseStart_2349555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349592 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 2, 5]
def baseStart_2349592 : Nat := 118140960795 + 2349592 * 2 ^ 59
def prefixEnd_2349592 : Nat := 4983230072969 + 3 ^ 40 * 2349592 * 2
def baseEnd_2349592 : Nat := 402156679319625481398143

theorem tailTrace_2349592 : CollatzResearch.WordTrace tailWord_2349592 prefixEnd_2349592 402156679319625481398143 := by
  unfold tailWord_2349592
  simp only [CollatzResearch.WordTrace]
  refine ⟨42848330251918468605653515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57131107002557958140871353 42848330251918468605653515)
  ·
    refine ⟨64272495377877702908480273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42848330251918468605653515 64272495377877702908480273)
    ·
      refine ⟨48204371533408277181360205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64272495377877702908480273 48204371533408277181360205)
      ·
        refine ⟨18076639325028103943010077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48204371533408277181360205 18076639325028103943010077)
        ·
          refine ⟨6778739746885538978628779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18076639325028103943010077 6778739746885538978628779)
          ·
            refine ⟨10168109620328308467943169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778739746885538978628779 10168109620328308467943169)
            ·
              refine ⟨7626082215246231350957377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10168109620328308467943169 7626082215246231350957377)
              ·
                refine ⟨5719561661434673513218033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7626082215246231350957377 5719561661434673513218033)
                ·
                  refine ⟨4289671246076005134913525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5719561661434673513218033 4289671246076005134913525)
                  ·
                    refine ⟨402156679319625481398143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4289671246076005134913525 402156679319625481398143)
                    ·
                      rfl

theorem cell23_2349592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_2349592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349592 prefixEnd_2349592 := by exact prefixLift 2349592
  have htrace : WordTrace (prefixWord ++ tailWord_2349592) baseStart_2349592 baseEnd_2349592 := by
    simpa [prefixWord, tailWord_2349592, baseEnd_2349592] using wordTrace_append hprefix tailTrace_2349592
  have hstable : (prefixWord ++ tailWord_2349592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349592).length < 2 ^ (prefixWord ++ tailWord_2349592).sum := by decide
  have hdescent : baseEnd_2349592 < baseStart_2349592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349596 : List Nat := [2, 2, 3, 1, 2, 4, 2, 2, 5]
def baseStart_2349596 : Nat := 118140960795 + 2349596 * 2 ^ 59
def prefixEnd_2349596 : Nat := 4983230072969 + 3 ^ 40 * 2349596 * 2
def baseEnd_2349596 : Nat := 134052454653499380949379

theorem tailTrace_2349596 : CollatzResearch.WordTrace tailWord_2349596 prefixEnd_2349596 134052454653499380949379 := by
  unfold tailWord_2349596
  simp only [CollatzResearch.WordTrace]
  refine ⟨42848403197911222947226321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57131204263881630596301761 42848403197911222947226321)
  ·
    refine ⟨32136302398433417210419741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42848403197911222947226321 32136302398433417210419741)
    ·
      refine ⟨12051113399412531453907403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32136302398433417210419741 12051113399412531453907403)
      ·
        refine ⟨18076670099118797180861105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12051113399412531453907403 18076670099118797180861105)
        ·
          refine ⟨13557502574339097885645829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18076670099118797180861105 13557502574339097885645829)
          ·
            refine ⟨2542031732688580853558593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13557502574339097885645829 2542031732688580853558593)
            ·
              refine ⟨1906523799516435640168945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542031732688580853558593 1906523799516435640168945)
              ·
                refine ⟨1429892849637326730126709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906523799516435640168945 1429892849637326730126709)
                ·
                  refine ⟨134052454653499380949379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1429892849637326730126709 134052454653499380949379)
                  ·
                    rfl

theorem cell23_2349596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_2349596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349596 prefixEnd_2349596 := by exact prefixLift 2349596
  have htrace : WordTrace (prefixWord ++ tailWord_2349596) baseStart_2349596 baseEnd_2349596 := by
    simpa [prefixWord, tailWord_2349596, baseEnd_2349596] using wordTrace_append hprefix tailTrace_2349596
  have hstable : (prefixWord ++ tailWord_2349596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349596).length < 2 ^ (prefixWord ++ tailWord_2349596).sum := by decide
  have hdescent : baseEnd_2349596 < baseStart_2349596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349629 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_2349629 : Nat := 118140960795 + 2349629 * 2 ^ 59
def prefixEnd_2349629 : Nat := 4983230072969 + 3 ^ 40 * 2349629 * 2
def baseEnd_2349629 : Nat := 1206489036743092799431759

theorem tailTrace_2349629 : CollatzResearch.WordTrace tailWord_2349629 prefixEnd_2349629 1206489036743092799431759 := by
  unfold tailWord_2349629
  simp only [CollatzResearch.WordTrace]
  refine ⟨85698010004702892530403941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57132006669801928353602627 85698010004702892530403941)
  ·
    refine ⟨16068376875881792349450739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85698010004702892530403941 16068376875881792349450739)
    ·
      refine ⟨24102565313822688524176109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16068376875881792349450739 24102565313822688524176109)
      ·
        refine ⟨9038461992683508196566041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24102565313822688524176109 9038461992683508196566041)
        ·
          refine ⟨6778846494512631147424531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9038461992683508196566041 6778846494512631147424531)
          ·
            refine ⟨10168269741768946721136797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778846494512631147424531 10168269741768946721136797)
            ·
              refine ⟨3813101153163355020426299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10168269741768946721136797 3813101153163355020426299)
              ·
                refine ⟨5719651729745032530639449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3813101153163355020426299 5719651729745032530639449)
                ·
                  refine ⟨4289738797308774397979587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5719651729745032530639449 4289738797308774397979587)
                  ·
                    refine ⟨6434608195963161596969381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4289738797308774397979587 6434608195963161596969381)
                    ·
                      refine ⟨1206489036743092799431759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6434608195963161596969381 1206489036743092799431759)
                      ·
                        rfl

theorem cell23_2349629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_2349629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349629 prefixEnd_2349629 := by exact prefixLift 2349629
  have htrace : WordTrace (prefixWord ++ tailWord_2349629) baseStart_2349629 baseEnd_2349629 := by
    simpa [prefixWord, tailWord_2349629, baseEnd_2349629] using wordTrace_append hprefix tailTrace_2349629
  have hstable : (prefixWord ++ tailWord_2349629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349629).length < 2 ^ (prefixWord ++ tailWord_2349629).sum := by decide
  have hdescent : baseEnd_2349629 < baseStart_2349629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349652 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 8]
def baseStart_2349652 : Nat := 118140960795 + 2349652 * 2 ^ 59
def prefixEnd_2349652 : Nat := 4983230072969 + 3 ^ 40 * 2349652 * 2
def baseEnd_2349652 : Nat := 134055649644238467716017

theorem tailTrace_2349652 : CollatzResearch.WordTrace tailWord_2349652 prefixEnd_2349652 134055649644238467716017 := by
  unfold tailWord_2349652
  simp only [CollatzResearch.WordTrace]
  refine ⟨42849424441809783729245605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57132565922413044972327473 42849424441809783729245605)
  ·
    refine ⟨8034267082839334449233551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42849424441809783729245605 8034267082839334449233551)
    ·
      refine ⟨12051400624259001673850327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8034267082839334449233551 12051400624259001673850327)
      ·
        refine ⟨18077100936388502510775491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12051400624259001673850327 18077100936388502510775491)
        ·
          refine ⟨27115651404582753766163237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18077100936388502510775491 27115651404582753766163237)
          ·
            refine ⟨5084184638359266331155607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27115651404582753766163237 5084184638359266331155607)
            ·
              refine ⟨7626276957538899496733411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084184638359266331155607 7626276957538899496733411)
              ·
                refine ⟨11439415436308349245100117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7626276957538899496733411 11439415436308349245100117)
                ·
                  refine ⟨134055649644238467716017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11439415436308349245100117 134055649644238467716017)
                  ·
                    rfl

theorem cell23_2349652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_2349652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349652 prefixEnd_2349652 := by exact prefixLift 2349652
  have htrace : WordTrace (prefixWord ++ tailWord_2349652) baseStart_2349652 baseEnd_2349652 := by
    simpa [prefixWord, tailWord_2349652, baseEnd_2349652] using wordTrace_append hprefix tailTrace_2349652
  have hstable : (prefixWord ++ tailWord_2349652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349652).length < 2 ^ (prefixWord ++ tailWord_2349652).sum := by decide
  have hdescent : baseEnd_2349652 < baseStart_2349652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349655 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_2349655 : Nat := 118140960795 + 2349655 * 2 ^ 59
def prefixEnd_2349655 : Nat := 4983230072969 + 3 ^ 40 * 2349655 * 2
def baseEnd_2349655 : Nat := 1206502387240109697706639

theorem tailTrace_2349655 : CollatzResearch.WordTrace tailWord_2349655 prefixEnd_2349655 1206502387240109697706639 := by
  unfold tailWord_2349655
  simp only [CollatzResearch.WordTrace]
  refine ⟨85698958302608698970850419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57132638868405799313900279 85698958302608698970850419)
  ·
    refine ⟨128548437453913048456275629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85698958302608698970850419 128548437453913048456275629)
    ·
      refine ⟨48205664045217393171103361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128548437453913048456275629 48205664045217393171103361)
      ·
        refine ⟨36154248033913044878327521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48205664045217393171103361 36154248033913044878327521)
        ·
          refine ⟨27115686025434783658745641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36154248033913044878327521 27115686025434783658745641)
          ·
            refine ⟨20336764519076087744059231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27115686025434783658745641 20336764519076087744059231)
            ·
              refine ⟨30505146778614131616088847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20336764519076087744059231 30505146778614131616088847)
              ·
                refine ⟨45757720167921197424133271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30505146778614131616088847 45757720167921197424133271)
                ·
                  refine ⟨68636580251881796136199907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45757720167921197424133271 68636580251881796136199907)
                  ·
                    refine ⟨102954870377822694204299861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68636580251881796136199907 102954870377822694204299861)
                    ·
                      refine ⟨1206502387240109697706639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 102954870377822694204299861 1206502387240109697706639)
                      ·
                        rfl

theorem cell23_2349655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_2349655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349655 prefixEnd_2349655 := by exact prefixLift 2349655
  have htrace : WordTrace (prefixWord ++ tailWord_2349655) baseStart_2349655 baseEnd_2349655 := by
    simpa [prefixWord, tailWord_2349655, baseEnd_2349655] using wordTrace_append hprefix tailTrace_2349655
  have hstable : (prefixWord ++ tailWord_2349655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349655).length < 2 ^ (prefixWord ++ tailWord_2349655).sum := by decide
  have hdescent : baseEnd_2349655 < baseStart_2349655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349679 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 3, 1, 3]
def baseStart_2349679 : Nat := 118140960795 + 2349679 * 2 ^ 59
def prefixEnd_2349679 : Nat := 4983230072969 + 3 ^ 40 * 2349679 * 2
def baseEnd_2349679 : Nat := 1206514710775817603806529

theorem tailTrace_2349679 : CollatzResearch.WordTrace tailWord_2349679 prefixEnd_2349679 1206514710775817603806529 := by
  unfold tailWord_2349679
  simp only [CollatzResearch.WordTrace]
  refine ⟨85699833654521751069724091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57133222436347834046482727 85699833654521751069724091)
  ·
    refine ⟨128549750481782626604586137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85699833654521751069724091 128549750481782626604586137)
    ·
      refine ⟨96412312861336969953439603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128549750481782626604586137 96412312861336969953439603)
      ·
        refine ⟨144618469292005454930159405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96412312861336969953439603 144618469292005454930159405)
        ·
          refine ⟨54231925984502045598809777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144618469292005454930159405 54231925984502045598809777)
          ·
            refine ⟨40673944488376534199107333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54231925984502045598809777 40673944488376534199107333)
            ·
              refine ⟨7626364591570600162332625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40673944488376534199107333 7626364591570600162332625)
              ·
                refine ⟨5719773443677950121749469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7626364591570600162332625 5719773443677950121749469)
                ·
                  refine ⟨2144915041379231295656051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5719773443677950121749469 2144915041379231295656051)
                  ·
                    refine ⟨3217372562068846943484077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2144915041379231295656051 3217372562068846943484077)
                    ·
                      refine ⟨1206514710775817603806529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3217372562068846943484077 1206514710775817603806529)
                      ·
                        rfl

theorem cell23_2349679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 1, 3].length) (baseStart_2349679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349679 prefixEnd_2349679 := by exact prefixLift 2349679
  have htrace : WordTrace (prefixWord ++ tailWord_2349679) baseStart_2349679 baseEnd_2349679 := by
    simpa [prefixWord, tailWord_2349679, baseEnd_2349679] using wordTrace_append hprefix tailTrace_2349679
  have hstable : (prefixWord ++ tailWord_2349679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349679).length < 2 ^ (prefixWord ++ tailWord_2349679).sum := by decide
  have hdescent : baseEnd_2349679 < baseStart_2349679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349689 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 1, 5, 2]
def baseStart_2349689 : Nat := 118140960795 + 2349689 * 2 ^ 59
def prefixEnd_2349689 : Nat := 4983230072969 + 3 ^ 40 * 2349689 * 2
def baseEnd_2349689 : Nat := 1206519845582362564681483

theorem tailTrace_2349689 : CollatzResearch.WordTrace tailWord_2349689 prefixEnd_2349689 1206519845582362564681483 := by
  unfold tailWord_2349689
  simp only [CollatzResearch.WordTrace]
  refine ⟨85700198384485522777588121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57133465589657015185058747 85700198384485522777588121)
  ·
    refine ⟨64275148788364142083191091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85700198384485522777588121 64275148788364142083191091)
    ·
      refine ⟨96412723182546213124786637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64275148788364142083191091 96412723182546213124786637)
      ·
        refine ⟨36154771193454829921794989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96412723182546213124786637 36154771193454829921794989)
        ·
          refine ⟨13558039197545561220673121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36154771193454829921794989 13558039197545561220673121)
          ·
            refine ⟨10168529398159170915504841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13558039197545561220673121 10168529398159170915504841)
            ·
              refine ⟨7626397048619378186628631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10168529398159170915504841 7626397048619378186628631)
              ·
                refine ⟨11439595572929067279942947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7626397048619378186628631 11439595572929067279942947)
                ·
                  refine ⟨17159393359393600919914421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11439595572929067279942947 17159393359393600919914421)
                  ·
                    refine ⟨1608693127443150086241977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17159393359393600919914421 1608693127443150086241977)
                    ·
                      refine ⟨1206519845582362564681483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608693127443150086241977 1206519845582362564681483)
                      ·
                        rfl

theorem cell23_2349689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_2349689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349689 prefixEnd_2349689 := by exact prefixLift 2349689
  have htrace : WordTrace (prefixWord ++ tailWord_2349689) baseStart_2349689 baseEnd_2349689 := by
    simpa [prefixWord, tailWord_2349689, baseEnd_2349689] using wordTrace_append hprefix tailTrace_2349689
  have hstable : (prefixWord ++ tailWord_2349689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349689).length < 2 ^ (prefixWord ++ tailWord_2349689).sum := by decide
  have hdescent : baseEnd_2349689 < baseStart_2349689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349732 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_2349732 : Nat := 118140960795 + 2349732 * 2 ^ 59
def prefixEnd_2349732 : Nat := 4983230072969 + 3 ^ 40 * 2349732 * 2
def baseEnd_2349732 : Nat := 1206541925250505896443785

theorem tailTrace_2349732 : CollatzResearch.WordTrace tailWord_2349732 prefixEnd_2349732 1206541925250505896443785 := by
  unfold tailWord_2349732
  simp only [CollatzResearch.WordTrace]
  refine ⟨42850883361664870560701725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57134511148886494080935633 42850883361664870560701725)
  ·
    refine ⟨16069081260624326460263147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42850883361664870560701725 16069081260624326460263147)
    ·
      refine ⟨24103621890936489690394721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16069081260624326460263147 24103621890936489690394721)
      ·
        refine ⟨18077716418202367267796041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24103621890936489690394721 18077716418202367267796041)
        ·
          refine ⟨13558287313651775450847031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18077716418202367267796041 13558287313651775450847031)
          ·
            refine ⟨20337430970477663176270547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13558287313651775450847031 20337430970477663176270547)
            ·
              refine ⟨30506146455716494764405821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20337430970477663176270547 30506146455716494764405821)
              ·
                refine ⟨11439804920893685536652183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30506146455716494764405821 11439804920893685536652183)
                ·
                  refine ⟨17159707381340528304978275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11439804920893685536652183 17159707381340528304978275)
                  ·
                    refine ⟨25739561072010792457467413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17159707381340528304978275 25739561072010792457467413)
                    ·
                      refine ⟨1206541925250505896443785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25739561072010792457467413 1206541925250505896443785)
                      ·
                        rfl

theorem cell23_2349732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_2349732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349732 prefixEnd_2349732 := by exact prefixLift 2349732
  have htrace : WordTrace (prefixWord ++ tailWord_2349732) baseStart_2349732 baseEnd_2349732 := by
    simpa [prefixWord, tailWord_2349732, baseEnd_2349732] using wordTrace_append hprefix tailTrace_2349732
  have hstable : (prefixWord ++ tailWord_2349732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349732).length < 2 ^ (prefixWord ++ tailWord_2349732).sum := by decide
  have hdescent : baseEnd_2349732 < baseStart_2349732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349749 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2349749 : Nat := 118140960795 + 2349749 * 2 ^ 59
def prefixEnd_2349749 : Nat := 4983230072969 + 3 ^ 40 * 2349749 * 2
def baseEnd_2349749 : Nat := 1206550654421632329931207

theorem tailTrace_2349749 : CollatzResearch.WordTrace tailWord_2349749 prefixEnd_2349749 1206550654421632329931207 := by
  unfold tailWord_2349749
  simp only [CollatzResearch.WordTrace]
  refine ⟨85702386764268153024772301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57134924509512102016514867 85702386764268153024772301)
  ·
    refine ⟨32138395036600557384289613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85702386764268153024772301 32138395036600557384289613)
    ·
      refine ⟨12051898138725209019108605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32138395036600557384289613 12051898138725209019108605)
      ·
        refine ⟨4519461802021953382165727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12051898138725209019108605 4519461802021953382165727)
        ·
          refine ⟨6779192703032930073248591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4519461802021953382165727 6779192703032930073248591)
          ·
            refine ⟨10168789054549395109872887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6779192703032930073248591 10168789054549395109872887)
            ·
              refine ⟨15253183581824092664809331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10168789054549395109872887 15253183581824092664809331)
              ·
                refine ⟨22879775372736138997213997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15253183581824092664809331 22879775372736138997213997)
                ·
                  refine ⟨8579915764776052123955249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22879775372736138997213997 8579915764776052123955249)
                  ·
                    refine ⟨6434936823582039092966437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8579915764776052123955249 6434936823582039092966437)
                    ·
                      refine ⟨1206550654421632329931207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6434936823582039092966437 1206550654421632329931207)
                      ·
                        rfl

theorem cell23_2349749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2349749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349749 prefixEnd_2349749 := by exact prefixLift 2349749
  have htrace : WordTrace (prefixWord ++ tailWord_2349749) baseStart_2349749 baseEnd_2349749 := by
    simpa [prefixWord, tailWord_2349749, baseEnd_2349749] using wordTrace_append hprefix tailTrace_2349749
  have hstable : (prefixWord ++ tailWord_2349749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349749).length < 2 ^ (prefixWord ++ tailWord_2349749).sum := by decide
  have hdescent : baseEnd_2349749 < baseStart_2349749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349750 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2349750 : Nat := 118140960795 + 2349750 * 2 ^ 59
def prefixEnd_2349750 : Nat := 4983230072969 + 3 ^ 40 * 2349750 * 2
def baseEnd_2349750 : Nat := 402183722634095608672901

theorem tailTrace_2349750 : CollatzResearch.WordTrace tailWord_2349750 prefixEnd_2349750 402183722634095608672901 := by
  unfold tailWord_2349750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5356401452329033137222419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57134948824843020130372469 5356401452329033137222419)
  ·
    refine ⟨8034602178493549705833629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5356401452329033137222419 8034602178493549705833629)
    ·
      refine ⟨3012975816935081139687611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8034602178493549705833629 3012975816935081139687611)
      ·
        refine ⟨4519463725402621709531417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012975816935081139687611 4519463725402621709531417)
        ·
          refine ⟨3389597794051966282148563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4519463725402621709531417 3389597794051966282148563)
          ·
            refine ⟨5084396691077949423222845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389597794051966282148563 5084396691077949423222845)
            ·
              refine ⟨1906648759154231033708567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5084396691077949423222845 1906648759154231033708567)
              ·
                refine ⟨2859973138731346550562851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906648759154231033708567 2859973138731346550562851)
                ·
                  refine ⟨4289959708097019825844277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859973138731346550562851 4289959708097019825844277)
                  ·
                    refine ⟨402183722634095608672901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4289959708097019825844277 402183722634095608672901)
                    ·
                      rfl

theorem cell23_2349750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2349750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349750 prefixEnd_2349750 := by exact prefixLift 2349750
  have htrace : WordTrace (prefixWord ++ tailWord_2349750) baseStart_2349750 baseEnd_2349750 := by
    simpa [prefixWord, tailWord_2349750, baseEnd_2349750] using wordTrace_append hprefix tailTrace_2349750
  have hstable : (prefixWord ++ tailWord_2349750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349750).length < 2 ^ (prefixWord ++ tailWord_2349750).sum := by decide
  have hdescent : baseEnd_2349750 < baseStart_2349750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349753 : List Nat := [1, 2, 1, 4, 1, 1, 1, 7, 1, 2, 2]
def baseStart_2349753 : Nat := 118140960795 + 2349753 * 2 ^ 59
def prefixEnd_2349753 : Nat := 4983230072969 + 3 ^ 40 * 2349753 * 2
def baseEnd_2349753 : Nat := 1206552708344250314281189

theorem tailTrace_2349753 : CollatzResearch.WordTrace tailWord_2349753 prefixEnd_2349753 1206552708344250314281189 := by
  unfold tailWord_2349753
  simp only [CollatzResearch.WordTrace]
  refine ⟨85702532656253661707917913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57135021770835774471945275 85702532656253661707917913)
  ·
    refine ⟨64276899492190246280938435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85702532656253661707917913 64276899492190246280938435)
    ·
      refine ⟨96415349238285369421407653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64276899492190246280938435 96415349238285369421407653)
      ·
        refine ⟨18077877982178506766513935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96415349238285369421407653 18077877982178506766513935)
        ·
          refine ⟨27116816973267760149770903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18077877982178506766513935 27116816973267760149770903)
          ·
            refine ⟨40675225459901640224656355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27116816973267760149770903 40675225459901640224656355)
            ·
              refine ⟨61012838189852460336984533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40675225459901640224656355 61012838189852460336984533)
              ·
                refine ⟨1429988395074667039148075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 61012838189852460336984533 1429988395074667039148075)
                ·
                  refine ⟨2144982592612000558722113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429988395074667039148075 2144982592612000558722113)
                  ·
                    refine ⟨1608736944459000419041585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2144982592612000558722113 1608736944459000419041585)
                    ·
                      refine ⟨1206552708344250314281189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608736944459000419041585 1206552708344250314281189)
                      ·
                        rfl

theorem cell23_2349753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_2349753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349753 prefixEnd_2349753 := by exact prefixLift 2349753
  have htrace : WordTrace (prefixWord ++ tailWord_2349753) baseStart_2349753 baseEnd_2349753 := by
    simpa [prefixWord, tailWord_2349753, baseEnd_2349753] using wordTrace_append hprefix tailTrace_2349753
  have hstable : (prefixWord ++ tailWord_2349753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349753).length < 2 ^ (prefixWord ++ tailWord_2349753).sum := by decide
  have hdescent : baseEnd_2349753 < baseStart_2349753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349770 : List Nat := [3, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2]
def baseStart_2349770 : Nat := 118140960795 + 2349770 * 2 ^ 59
def prefixEnd_2349770 : Nat := 4983230072969 + 3 ^ 40 * 2349770 * 2
def baseEnd_2349770 : Nat := 1206561437515376747768611

theorem tailTrace_2349770 : CollatzResearch.WordTrace tailWord_2349770 prefixEnd_2349770 1206561437515376747768611 := by
  unfold tailWord_2349770
  simp only [CollatzResearch.WordTrace]
  refine ⟨21425788174298018402821691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57135435131461382407524509 21425788174298018402821691)
  ·
    refine ⟨32138682261447027604232537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21425788174298018402821691 32138682261447027604232537)
    ·
      refine ⟨24104011696085270703174403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32138682261447027604232537 24104011696085270703174403)
      ·
        refine ⟨36156017544127906054761605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24104011696085270703174403 36156017544127906054761605)
        ·
          refine ⟨6779253289523982385267801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36156017544127906054761605 6779253289523982385267801)
          ·
            refine ⟨5084439967142986788950851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6779253289523982385267801 5084439967142986788950851)
            ·
              refine ⟨7626659950714480183426277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084439967142986788950851 7626659950714480183426277)
              ·
                refine ⟨1429998740758965034392427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7626659950714480183426277 1429998740758965034392427)
                ·
                  refine ⟨2144998111138447551588641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429998740758965034392427 2144998111138447551588641)
                  ·
                    refine ⟨1608748583353835663691481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2144998111138447551588641 1608748583353835663691481)
                    ·
                      refine ⟨1206561437515376747768611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608748583353835663691481 1206561437515376747768611)
                      ·
                        rfl

theorem cell23_2349770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_2349770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349770 prefixEnd_2349770 := by exact prefixLift 2349770
  have htrace : WordTrace (prefixWord ++ tailWord_2349770) baseStart_2349770 baseEnd_2349770 := by
    simpa [prefixWord, tailWord_2349770, baseEnd_2349770] using wordTrace_append hprefix tailTrace_2349770
  have hstable : (prefixWord ++ tailWord_2349770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349770).length < 2 ^ (prefixWord ++ tailWord_2349770).sum := by decide
  have hdescent : baseEnd_2349770 < baseStart_2349770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349786 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3]
def baseStart_2349786 : Nat := 118140960795 + 2349786 * 2 ^ 59
def prefixEnd_2349786 : Nat := 4983230072969 + 3 ^ 40 * 2349786 * 2
def baseEnd_2349786 : Nat := 1206569653205848685168537

theorem tailTrace_2349786 : CollatzResearch.WordTrace tailWord_2349786 prefixEnd_2349786 1206569653205848685168537 := by
  unfold tailWord_2349786
  simp only [CollatzResearch.WordTrace]
  refine ⟨21425934066283527085967303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57135824176756072229246141 21425934066283527085967303)
  ·
    refine ⟨32138901099425290628950955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21425934066283527085967303 32138901099425290628950955)
    ·
      refine ⟨48208351649137935943426433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32138901099425290628950955 48208351649137935943426433)
      ·
        refine ⟨36156263736853451957569825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48208351649137935943426433 36156263736853451957569825)
        ·
          refine ⟨27117197802640088968177369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36156263736853451957569825 27117197802640088968177369)
          ·
            refine ⟨20337898351980066726133027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27117197802640088968177369 20337898351980066726133027)
            ·
              refine ⟨30506847527970100089199541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20337898351980066726133027 30506847527970100089199541)
              ·
                refine ⟨2860016955747196883362457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30506847527970100089199541 2860016955747196883362457)
                ·
                  refine ⟨2145012716810397662521843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2860016955747196883362457 2145012716810397662521843)
                  ·
                    refine ⟨3217519075215596493782765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2145012716810397662521843 3217519075215596493782765)
                    ·
                      refine ⟨1206569653205848685168537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3217519075215596493782765 1206569653205848685168537)
                      ·
                        rfl

theorem cell23_2349786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_2349786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349786 prefixEnd_2349786 := by exact prefixLift 2349786
  have htrace : WordTrace (prefixWord ++ tailWord_2349786) baseStart_2349786 baseEnd_2349786 := by
    simpa [prefixWord, tailWord_2349786, baseEnd_2349786] using wordTrace_append hprefix tailTrace_2349786
  have hstable : (prefixWord ++ tailWord_2349786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349786).length < 2 ^ (prefixWord ++ tailWord_2349786).sum := by decide
  have hdescent : baseEnd_2349786 < baseStart_2349786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349792 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2349792 : Nat := 118140960795 + 2349792 * 2 ^ 59
def prefixEnd_2349792 : Nat := 4983230072969 + 3 ^ 40 * 2349792 * 2
def baseEnd_2349792 : Nat := 1206572734089775661693509

theorem tailTrace_2349792 : CollatzResearch.WordTrace tailWord_2349792 prefixEnd_2349792 1206572734089775661693509 := by
  unfold tailWord_2349792
  simp only [CollatzResearch.WordTrace]
  refine ⟨42851977551556185684293815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57135970068741580912391753 42851977551556185684293815)
  ·
    refine ⟨64277966327334278526440723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42851977551556185684293815 64277966327334278526440723)
    ·
      refine ⟨96416949491001417789661085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64277966327334278526440723 96416949491001417789661085)
      ·
        refine ⟨36156356059125531671122907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96416949491001417789661085 36156356059125531671122907)
        ·
          refine ⟨54234534088688297506684361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36156356059125531671122907 54234534088688297506684361)
          ·
            refine ⟨40675900566516223130013271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54234534088688297506684361 40675900566516223130013271)
            ·
              refine ⟨61013850849774334695019907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40675900566516223130013271 61013850849774334695019907)
              ·
                refine ⟨91520776274661502042529861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61013850849774334695019907 91520776274661502042529861)
                ·
                  refine ⟨17160145551499031632974349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91520776274661502042529861 17160145551499031632974349)
                  ·
                    refine ⟨6435054581812136862365381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17160145551499031632974349 6435054581812136862365381)
                    ·
                      refine ⟨1206572734089775661693509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6435054581812136862365381 1206572734089775661693509)
                      ·
                        rfl

theorem cell23_2349792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2349792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349792 prefixEnd_2349792 := by exact prefixLift 2349792
  have htrace : WordTrace (prefixWord ++ tailWord_2349792) baseStart_2349792 baseEnd_2349792 := by
    simpa [prefixWord, tailWord_2349792, baseEnd_2349792] using wordTrace_append hprefix tailTrace_2349792
  have hstable : (prefixWord ++ tailWord_2349792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349792).length < 2 ^ (prefixWord ++ tailWord_2349792).sum := by decide
  have hdescent : baseEnd_2349792 < baseStart_2349792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349796 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 3, 3, 2]
def baseStart_2349796 : Nat := 118140960795 + 2349796 * 2 ^ 59
def prefixEnd_2349796 : Nat := 4983230072969 + 3 ^ 40 * 2349796 * 2
def baseEnd_2349796 : Nat := 1206574788012393646043491

theorem tailTrace_2349796 : CollatzResearch.WordTrace tailWord_2349796 prefixEnd_2349796 1206574788012393646043491 := by
  unfold tailWord_2349796
  simp only [CollatzResearch.WordTrace]
  refine ⟨42852050497548940025866621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57136067330065253367822161 42852050497548940025866621)
  ·
    refine ⟨16069518936580852509699983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42852050497548940025866621 16069518936580852509699983)
    ·
      refine ⟨24104278404871278764549975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16069518936580852509699983 24104278404871278764549975)
      ·
        refine ⟨36156417607306918146824963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24104278404871278764549975 36156417607306918146824963)
        ·
          refine ⟨54234626410960377220237445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36156417607306918146824963 54234626410960377220237445)
          ·
            refine ⟨10168992452055070728794521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54234626410960377220237445 10168992452055070728794521)
            ·
              refine ⟨7626744339041303046595891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10168992452055070728794521 7626744339041303046595891)
              ·
                refine ⟨11440116508561954569893837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7626744339041303046595891 11440116508561954569893837)
                ·
                  refine ⟨4290043690710732963710189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11440116508561954569893837 4290043690710732963710189)
                  ·
                    refine ⟨1608766384016524861391321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4290043690710732963710189 1608766384016524861391321)
                    ·
                      refine ⟨1206574788012393646043491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608766384016524861391321 1206574788012393646043491)
                      ·
                        rfl

theorem cell23_2349796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_2349796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349796 prefixEnd_2349796 := by exact prefixLift 2349796
  have htrace : WordTrace (prefixWord ++ tailWord_2349796) baseStart_2349796 baseEnd_2349796 := by
    simpa [prefixWord, tailWord_2349796, baseEnd_2349796] using wordTrace_append hprefix tailTrace_2349796
  have hstable : (prefixWord ++ tailWord_2349796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349796).length < 2 ^ (prefixWord ++ tailWord_2349796).sum := by decide
  have hdescent : baseEnd_2349796 < baseStart_2349796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349802 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_2349802 : Nat := 118140960795 + 2349802 * 2 ^ 59
def prefixEnd_2349802 : Nat := 4983230072969 + 3 ^ 40 * 2349802 * 2
def baseEnd_2349802 : Nat := 402192622965440207522821

theorem tailTrace_2349802 : CollatzResearch.WordTrace tailWord_2349802 prefixEnd_2349802 402192622965440207522821 := by
  unfold tailWord_2349802
  simp only [CollatzResearch.WordTrace]
  refine ⟨21426079958269035769112915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57136213222050762050967773 21426079958269035769112915)
  ·
    refine ⟨32139119937403553653669373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21426079958269035769112915 32139119937403553653669373)
    ·
      refine ⟨12052169976526332620126015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32139119937403553653669373 12052169976526332620126015)
      ·
        refine ⟨18078254964789498930189023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12052169976526332620126015 18078254964789498930189023)
        ·
          refine ⟨27117382447184248395283535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18078254964789498930189023 27117382447184248395283535)
          ·
            refine ⟨40676073670776372592925303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27117382447184248395283535 40676073670776372592925303)
            ·
              refine ⟨61014110506164558889387955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40676073670776372592925303 61014110506164558889387955)
              ·
                refine ⟨91521165759246838334081933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61014110506164558889387955 91521165759246838334081933)
                ·
                  refine ⟨34320437159717564375280725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91521165759246838334081933 34320437159717564375280725)
                  ·
                    refine ⟨402192622965440207522821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34320437159717564375280725 402192622965440207522821)
                    ·
                      rfl

theorem cell23_2349802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_2349802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349802 prefixEnd_2349802 := by exact prefixLift 2349802
  have htrace : WordTrace (prefixWord ++ tailWord_2349802) baseStart_2349802 baseEnd_2349802 := by
    simpa [prefixWord, tailWord_2349802, baseEnd_2349802] using wordTrace_append hprefix tailTrace_2349802
  have hstable : (prefixWord ++ tailWord_2349802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349802).length < 2 ^ (prefixWord ++ tailWord_2349802).sum := by decide
  have hdescent : baseEnd_2349802 < baseStart_2349802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349872 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_2349872 : Nat := 118140960795 + 2349872 * 2 ^ 59
def prefixEnd_2349872 : Nat := 4983230072969 + 3 ^ 40 * 2349872 * 2
def baseEnd_2349872 : Nat := 1206613812542135348693141

theorem tailTrace_2349872 : CollatzResearch.WordTrace tailWord_2349872 prefixEnd_2349872 1206613812542135348693141 := by
  unfold tailWord_2349872
  simp only [CollatzResearch.WordTrace]
  refine ⟨42853436471411272515749935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57137915295215030020999913 42853436471411272515749935)
  ·
    refine ⟨64280154707116908773624903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42853436471411272515749935 64280154707116908773624903)
    ·
      refine ⟨96420232060675363160437355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64280154707116908773624903 96420232060675363160437355)
      ·
        refine ⟨144630348091013044740656033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96420232060675363160437355 144630348091013044740656033)
        ·
          refine ⟨108472761068259783555492025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144630348091013044740656033 108472761068259783555492025)
          ·
            refine ⟨81354570801194837666619019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108472761068259783555492025 81354570801194837666619019)
            ·
              refine ⟨122031856201792256499928529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81354570801194837666619019 122031856201792256499928529)
              ·
                refine ⟨91523892151344192374946397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122031856201792256499928529 91523892151344192374946397)
                ·
                  refine ⟨34321459556754072140604899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91523892151344192374946397 34321459556754072140604899)
                  ·
                    refine ⟨51482189335131108210907349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34321459556754072140604899 51482189335131108210907349)
                    ·
                      refine ⟨1206613812542135348693141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51482189335131108210907349 1206613812542135348693141)
                      ·
                        rfl

theorem cell23_2349872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_2349872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349872 prefixEnd_2349872 := by exact prefixLift 2349872
  have htrace : WordTrace (prefixWord ++ tailWord_2349872) baseStart_2349872 baseEnd_2349872 := by
    simpa [prefixWord, tailWord_2349872, baseEnd_2349872] using wordTrace_append hprefix tailTrace_2349872
  have hstable : (prefixWord ++ tailWord_2349872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349872).length < 2 ^ (prefixWord ++ tailWord_2349872).sum := by decide
  have hdescent : baseEnd_2349872 < baseStart_2349872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349879 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 2, 5]
def baseStart_2349879 : Nat := 118140960795 + 2349879 * 2 ^ 59
def prefixEnd_2349879 : Nat := 4983230072969 + 3 ^ 40 * 2349879 * 2
def baseEnd_2349879 : Nat := 402205802302238940435203

theorem tailTrace_2349879 : CollatzResearch.WordTrace tailWord_2349879 prefixEnd_2349879 402205802302238940435203 := by
  unfold tailWord_2349879
  simp only [CollatzResearch.WordTrace]
  refine ⟨85707128253797185227004691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57138085502531456818003127 85707128253797185227004691)
  ·
    refine ⟨128560692380695777840507037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85707128253797185227004691 128560692380695777840507037)
    ·
      refine ⟨48210259642760916690190139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128560692380695777840507037 48210259642760916690190139)
      ·
        refine ⟨72315389464141375035285209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48210259642760916690190139 72315389464141375035285209)
        ·
          refine ⟨54236542098106031276463907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72315389464141375035285209 54236542098106031276463907)
          ·
            refine ⟨81354813147159046914695861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54236542098106031276463907 81354813147159046914695861)
            ·
              refine ⟨7627013732546160648252737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81354813147159046914695861 7627013732546160648252737)
              ·
                refine ⟨5720260299409620486189553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7627013732546160648252737 5720260299409620486189553)
                ·
                  refine ⟨4290195224557215364642165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5720260299409620486189553 4290195224557215364642165)
                  ·
                    refine ⟨402205802302238940435203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4290195224557215364642165 402205802302238940435203)
                    ·
                      rfl

theorem cell23_2349879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_2349879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349879 prefixEnd_2349879 := by exact prefixLift 2349879
  have htrace : WordTrace (prefixWord ++ tailWord_2349879) baseStart_2349879 baseEnd_2349879 := by
    simpa [prefixWord, tailWord_2349879, baseEnd_2349879] using wordTrace_append hprefix tailTrace_2349879
  have hstable : (prefixWord ++ tailWord_2349879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349879).length < 2 ^ (prefixWord ++ tailWord_2349879).sum := by decide
  have hdescent : baseEnd_2349879 < baseStart_2349879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349894 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2349894 : Nat := 118140960795 + 2349894 * 2 ^ 59
def prefixEnd_2349894 : Nat := 4983230072969 + 3 ^ 40 * 2349894 * 2
def baseEnd_2349894 : Nat := 1206625109116534262618041

theorem tailTrace_2349894 : CollatzResearch.WordTrace tailWord_2349894 prefixEnd_2349894 1206625109116534262618041 := by
  unfold tailWord_2349894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678364854648213837150023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57138450232495228525867157 2678364854648213837150023)
  ·
    refine ⟨4017547281972320755725035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2678364854648213837150023 4017547281972320755725035)
    ·
      refine ⟨6026320922958481133587553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4017547281972320755725035 6026320922958481133587553)
      ·
        refine ⟨4519740692218860850190665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6026320922958481133587553 4519740692218860850190665)
        ·
          refine ⟨3389805519164145637642999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4519740692218860850190665 3389805519164145637642999)
          ·
            refine ⟨5084708278746218456464499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389805519164145637642999 5084708278746218456464499)
            ·
              refine ⟨7627062418119327684696749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084708278746218456464499 7627062418119327684696749)
              ·
                refine ⟨2860148406794747881761281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7627062418119327684696749 2860148406794747881761281)
                ·
                  refine ⟨2145111305096060911320961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2860148406794747881761281 2145111305096060911320961)
                  ·
                    refine ⟨1608833478822045683490721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2145111305096060911320961 1608833478822045683490721)
                    ·
                      refine ⟨1206625109116534262618041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608833478822045683490721 1206625109116534262618041)
                      ·
                        rfl

theorem cell23_2349894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2349894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349894 prefixEnd_2349894 := by exact prefixLift 2349894
  have htrace : WordTrace (prefixWord ++ tailWord_2349894) baseStart_2349894 baseEnd_2349894 := by
    simpa [prefixWord, tailWord_2349894, baseEnd_2349894] using wordTrace_append hprefix tailTrace_2349894
  have hstable : (prefixWord ++ tailWord_2349894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349894).length < 2 ^ (prefixWord ++ tailWord_2349894).sum := by decide
  have hdescent : baseEnd_2349894 < baseStart_2349894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349936 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 3]
def baseStart_2349936 : Nat := 118140960795 + 2349936 * 2 ^ 59
def prefixEnd_2349936 : Nat := 4983230072969 + 3 ^ 40 * 2349936 * 2
def baseEnd_2349936 : Nat := 1206646675304023098292847

theorem tailTrace_2349936 : CollatzResearch.WordTrace tailWord_2349936 prefixEnd_2349936 1206646675304023098292847 := by
  unfold tailWord_2349936
  simp only [CollatzResearch.WordTrace]
  refine ⟨42854603607295341980914831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57139471476393789307886441 42854603607295341980914831)
  ·
    refine ⟨64281905410943012971372247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42854603607295341980914831 64281905410943012971372247)
    ·
      refine ⟨96422858116414519457058371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64281905410943012971372247 96422858116414519457058371)
      ·
        refine ⟨144634287174621779185587557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96422858116414519457058371 144634287174621779185587557)
        ·
          refine ⟨27118928845241583597297667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144634287174621779185587557 27118928845241583597297667)
          ·
            refine ⟨40678393267862375395946501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27118928845241583597297667 40678393267862375395946501)
            ·
              refine ⟨7627198737724195386739969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40678393267862375395946501 7627198737724195386739969)
              ·
                refine ⟨5720399053293146540054977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7627198737724195386739969 5720399053293146540054977)
                ·
                  refine ⟨4290299289969859905041233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5720399053293146540054977 4290299289969859905041233)
                  ·
                    refine ⟨3217724467477394928780925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4290299289969859905041233 3217724467477394928780925)
                    ·
                      refine ⟨1206646675304023098292847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3217724467477394928780925 1206646675304023098292847)
                      ·
                        rfl

theorem cell23_2349936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 3].length) (baseStart_2349936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349936 prefixEnd_2349936 := by exact prefixLift 2349936
  have htrace : WordTrace (prefixWord ++ tailWord_2349936) baseStart_2349936 baseEnd_2349936 := by
    simpa [prefixWord, tailWord_2349936, baseEnd_2349936] using wordTrace_append hprefix tailTrace_2349936
  have hstable : (prefixWord ++ tailWord_2349936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349936).length < 2 ^ (prefixWord ++ tailWord_2349936).sum := by decide
  have hdescent : baseEnd_2349936 < baseStart_2349936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349939 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 6]
def baseStart_2349939 : Nat := 118140960795 + 2349939 * 2 ^ 59
def prefixEnd_2349939 : Nat := 4983230072969 + 3 ^ 40 * 2349939 * 2
def baseEnd_2349939 : Nat := 134072023971776287395037

theorem tailTrace_2349939 : CollatzResearch.WordTrace tailWord_2349939 prefixEnd_2349939 134072023971776287395037 := by
  unfold tailWord_2349939
  simp only [CollatzResearch.WordTrace]
  refine ⟨85709316633579815474188871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57139544422386543649459247 85709316633579815474188871)
  ·
    refine ⟨128563974950369723211283307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85709316633579815474188871 128563974950369723211283307)
    ·
      refine ⟨192845962425554584816924961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128563974950369723211283307 192845962425554584816924961)
      ·
        refine ⟨144634471819165938612693721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192845962425554584816924961 144634471819165938612693721)
        ·
          refine ⟨108475853864374453959520291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144634471819165938612693721 108475853864374453959520291)
          ·
            refine ⟨162713780796561680939280437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108475853864374453959520291 162713780796561680939280437)
            ·
              refine ⟨15254416949677657588057541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162713780796561680939280437 15254416949677657588057541)
              ·
                refine ⟨2860203178064560797760789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15254416949677657588057541 2860203178064560797760789)
                ·
                  refine ⟨134072023971776287395037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2860203178064560797760789 134072023971776287395037)
                  ·
                    rfl

theorem cell23_2349939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 6].length) (baseStart_2349939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2349939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2349939 prefixEnd_2349939 := by exact prefixLift 2349939
  have htrace : WordTrace (prefixWord ++ tailWord_2349939) baseStart_2349939 baseEnd_2349939 := by
    simpa [prefixWord, tailWord_2349939, baseEnd_2349939] using wordTrace_append hprefix tailTrace_2349939
  have hstable : (prefixWord ++ tailWord_2349939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349939).length < 2 ^ (prefixWord ++ tailWord_2349939).sum := by decide
  have hdescent : baseEnd_2349939 < baseStart_2349939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350016 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 1, 6]
def baseStart_2350016 : Nat := 118140960795 + 2350016 * 2 ^ 59
def prefixEnd_2350016 : Nat := 4983230072969 + 3 ^ 40 * 2350016 * 2
def baseEnd_2350016 : Nat := 402229251252127595097493

theorem tailTrace_2350016 : CollatzResearch.WordTrace tailWord_2350016 prefixEnd_2350016 402229251252127595097493 := by
  unfold tailWord_2350016
  simp only [CollatzResearch.WordTrace]
  refine ⟨42856062527150428812370951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57141416702867238416494601 42856062527150428812370951)
  ·
    refine ⟨64284093790725643218556427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42856062527150428812370951 64284093790725643218556427)
    ·
      refine ⟨96426140686088464827834641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64284093790725643218556427 96426140686088464827834641)
      ·
        refine ⟨72319605514566348620875981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96426140686088464827834641 72319605514566348620875981)
        ·
          refine ⟨27119852067962380732828493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72319605514566348620875981 27119852067962380732828493)
          ·
            refine ⟨10169944525485892774810685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27119852067962380732828493 10169944525485892774810685)
            ·
              refine ⟨3813729197057209790554007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10169944525485892774810685 3813729197057209790554007)
              ·
                refine ⟨5720593795585814685831011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3813729197057209790554007 5720593795585814685831011)
                ·
                  refine ⟨8580890693378722028746517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5720593795585814685831011 8580890693378722028746517)
                  ·
                    refine ⟨402229251252127595097493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8580890693378722028746517 402229251252127595097493)
                    ·
                      rfl

theorem cell23_2350016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 6].length) (baseStart_2350016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350016 prefixEnd_2350016 := by exact prefixLift 2350016
  have htrace : WordTrace (prefixWord ++ tailWord_2350016) baseStart_2350016 baseEnd_2350016 := by
    simpa [prefixWord, tailWord_2350016, baseEnd_2350016] using wordTrace_append hprefix tailTrace_2350016
  have hstable : (prefixWord ++ tailWord_2350016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350016).length < 2 ^ (prefixWord ++ tailWord_2350016).sum := by decide
  have hdescent : baseEnd_2350016 < baseStart_2350016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350019 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 6]
def baseStart_2350019 : Nat := 118140960795 + 2350019 * 2 ^ 59
def prefixEnd_2350019 : Nat := 4983230072969 + 3 ^ 40 * 2350019 * 2
def baseEnd_2350019 : Nat := 1206689294198346273554965

theorem tailTrace_2350019 : CollatzResearch.WordTrace tailWord_2350019 prefixEnd_2350019 1206689294198346273554965 := by
  unfold tailWord_2350019
  simp only [CollatzResearch.WordTrace]
  refine ⟨85712234473289989137101111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57141489648859992758067407 85712234473289989137101111)
  ·
    refine ⟨128568351709934983705651667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85712234473289989137101111 128568351709934983705651667)
    ·
      refine ⟨192852527564902475558477501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128568351709934983705651667 192852527564902475558477501)
      ·
        refine ⟨72319697836838428334429063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192852527564902475558477501 72319697836838428334429063)
        ·
          refine ⟨108479546755257642501643595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72319697836838428334429063 108479546755257642501643595)
          ·
            refine ⟨162719320132886463752465393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108479546755257642501643595 162719320132886463752465393)
            ·
              refine ⟨122039490099664847814349045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162719320132886463752465393 122039490099664847814349045)
              ·
                refine ⟨11441202196843579482595223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122039490099664847814349045 11441202196843579482595223)
                ·
                  refine ⟨17161803295265369223892835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11441202196843579482595223 17161803295265369223892835)
                  ·
                    refine ⟨25742704942898053835839253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17161803295265369223892835 25742704942898053835839253)
                    ·
                      refine ⟨1206689294198346273554965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25742704942898053835839253 1206689294198346273554965)
                      ·
                        rfl

theorem cell23_2350019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_2350019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350019 prefixEnd_2350019 := by exact prefixLift 2350019
  have htrace : WordTrace (prefixWord ++ tailWord_2350019) baseStart_2350019 baseEnd_2350019 := by
    simpa [prefixWord, tailWord_2350019, baseEnd_2350019] using wordTrace_append hprefix tailTrace_2350019
  have hstable : (prefixWord ++ tailWord_2350019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350019).length < 2 ^ (prefixWord ++ tailWord_2350019).sum := by decide
  have hdescent : baseEnd_2350019 < baseStart_2350019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350034 : List Nat := [3, 2, 2, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_2350034 : Nat := 118140960795 + 2350034 * 2 ^ 59
def prefixEnd_2350034 : Nat := 4983230072969 + 3 ^ 40 * 2350034 * 2
def baseEnd_2350034 : Nat := 1206696996408163714867397

theorem tailTrace_2350034 : CollatzResearch.WordTrace tailWord_2350034 prefixEnd_2350034 1206696996408163714867397 := by
  unfold tailWord_2350034
  simp only [CollatzResearch.WordTrace]
  refine ⟨21428195392058911674724289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57141854378823764465931437 21428195392058911674724289)
  ·
    refine ⟨16071146544044183756043217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21428195392058911674724289 16071146544044183756043217)
    ·
      refine ⟨12053359908033137817032413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16071146544044183756043217 12053359908033137817032413)
      ·
        refine ⟨4520009965512426681387155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12053359908033137817032413 4520009965512426681387155)
        ·
          refine ⟨6780014948268640022080733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4520009965512426681387155 6780014948268640022080733)
          ·
            refine ⟨2542505605600740008280275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6780014948268640022080733 2542505605600740008280275)
            ·
              refine ⟨3813758408401110012420413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542505605600740008280275 3813758408401110012420413)
              ·
                refine ⟨1430159403150416254657655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3813758408401110012420413 1430159403150416254657655)
                ·
                  refine ⟨2145239104725624381986483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430159403150416254657655 2145239104725624381986483)
                  ·
                    refine ⟨3217858657088436572979725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2145239104725624381986483 3217858657088436572979725)
                    ·
                      refine ⟨1206696996408163714867397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3217858657088436572979725 1206696996408163714867397)
                      ·
                        rfl

theorem cell23_2350034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_2350034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350034 prefixEnd_2350034 := by exact prefixLift 2350034
  have htrace : WordTrace (prefixWord ++ tailWord_2350034) baseStart_2350034 baseEnd_2350034 := by
    simpa [prefixWord, tailWord_2350034, baseEnd_2350034] using wordTrace_append hprefix tailTrace_2350034
  have hstable : (prefixWord ++ tailWord_2350034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350034).length < 2 ^ (prefixWord ++ tailWord_2350034).sum := by decide
  have hdescent : baseEnd_2350034 < baseStart_2350034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350050 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2350050 : Nat := 118140960795 + 2350050 * 2 ^ 59
def prefixEnd_2350050 : Nat := 4983230072969 + 3 ^ 40 * 2350050 * 2
def baseEnd_2350050 : Nat := 402235070699545217422441

theorem tailTrace_2350050 : CollatzResearch.WordTrace tailWord_2350050 prefixEnd_2350050 402235070699545217422441 := by
  unfold tailWord_2350050
  simp only [CollatzResearch.WordTrace]
  refine ⟨21428341284044420357869901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57142243424118454287653069 21428341284044420357869901)
  ·
    refine ⟨8035627981516657634201213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21428341284044420357869901 8035627981516657634201213)
    ·
      refine ⟨3013360493068746612825455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8035627981516657634201213 3013360493068746612825455)
      ·
        refine ⟨4520040739603119919238183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3013360493068746612825455 4520040739603119919238183)
        ·
          refine ⟨6780061109404679878857275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4520040739603119919238183 6780061109404679878857275)
          ·
            refine ⟨10170091664107019818285913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6780061109404679878857275 10170091664107019818285913)
            ·
              refine ⟨7627568748080264863714435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10170091664107019818285913 7627568748080264863714435)
              ·
                refine ⟨11441353122120397295571653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7627568748080264863714435 11441353122120397295571653)
                ·
                  refine ⟨2145253710397574492919685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11441353122120397295571653 2145253710397574492919685)
                  ·
                    refine ⟨402235070699545217422441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2145253710397574492919685 402235070699545217422441)
                    ·
                      rfl

theorem cell23_2350050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2350050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350050 prefixEnd_2350050 := by exact prefixLift 2350050
  have htrace : WordTrace (prefixWord ++ tailWord_2350050) baseStart_2350050 baseEnd_2350050 := by
    simpa [prefixWord, tailWord_2350050, baseEnd_2350050] using wordTrace_append hprefix tailTrace_2350050
  have hstable : (prefixWord ++ tailWord_2350050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350050).length < 2 ^ (prefixWord ++ tailWord_2350050).sum := by decide
  have hdescent : baseEnd_2350050 < baseStart_2350050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350079 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_2350079 : Nat := 118140960795 + 2350079 * 2 ^ 59
def prefixEnd_2350079 : Nat := 4983230072969 + 3 ^ 40 * 2350079 * 2
def baseEnd_2350079 : Nat := 1206720103037616038804689

theorem tailTrace_2350079 : CollatzResearch.WordTrace tailWord_2350079 prefixEnd_2350079 1206720103037616038804689 := by
  unfold tailWord_2350079
  simp only [CollatzResearch.WordTrace]
  refine ⟨85714422853072619384285291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57142948568715079589523527 85714422853072619384285291)
  ·
    refine ⟨128571634279608929076427937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85714422853072619384285291 128571634279608929076427937)
    ·
      refine ⟨96428725709706696807320953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128571634279608929076427937 96428725709706696807320953)
      ·
        refine ⟨72321544282280022605490715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96428725709706696807320953 72321544282280022605490715)
        ·
          refine ⟨108482316423420033908236073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72321544282280022605490715 108482316423420033908236073)
          ·
            refine ⟨81361737317565025431177055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108482316423420033908236073 81361737317565025431177055)
            ·
              refine ⟨122042605976347538146765583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81361737317565025431177055 122042605976347538146765583)
              ·
                refine ⟨183063908964521307220148375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122042605976347538146765583 183063908964521307220148375)
                ·
                  refine ⟨274595863446781960830222563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183063908964521307220148375 274595863446781960830222563)
                  ·
                    refine ⟨411893795170172941245333845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274595863446781960830222563 411893795170172941245333845)
                    ·
                      refine ⟨1206720103037616038804689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 411893795170172941245333845 1206720103037616038804689)
                      ·
                        rfl

theorem cell23_2350079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_2350079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350079 prefixEnd_2350079 := by exact prefixLift 2350079
  have htrace : WordTrace (prefixWord ++ tailWord_2350079) baseStart_2350079 baseEnd_2350079 := by
    simpa [prefixWord, tailWord_2350079, baseEnd_2350079] using wordTrace_append hprefix tailTrace_2350079
  have hstable : (prefixWord ++ tailWord_2350079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350079).length < 2 ^ (prefixWord ++ tailWord_2350079).sum := by decide
  have hdescent : baseEnd_2350079 < baseStart_2350079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350106 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_2350106 : Nat := 118140960795 + 2350106 * 2 ^ 59
def prefixEnd_2350106 : Nat := 4983230072969 + 3 ^ 40 * 2350106 * 2
def baseEnd_2350106 : Nat := 402244655671762477722355

theorem tailTrace_2350106 : CollatzResearch.WordTrace tailWord_2350106 prefixEnd_2350106 402244655671762477722355 := by
  unfold tailWord_2350106
  simp only [CollatzResearch.WordTrace]
  refine ⟨21428851905993700748879543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57143605082649868663678781 21428851905993700748879543)
  ·
    refine ⟨32143277858990551123319315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21428851905993700748879543 32143277858990551123319315)
    ·
      refine ⟨48214916788485826684978973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32143277858990551123319315 48214916788485826684978973)
      ·
        refine ⟨18080593795682185006867115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48214916788485826684978973 18080593795682185006867115)
        ·
          refine ⟨27120890693523277510300673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18080593795682185006867115 27120890693523277510300673)
          ·
            refine ⟨20340668020142458132725505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27120890693523277510300673 20340668020142458132725505)
            ·
              refine ⟨15255501015106843599544129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20340668020142458132725505 15255501015106843599544129)
              ·
                refine ⟨11441625761330132699658097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15255501015106843599544129 11441625761330132699658097)
                ·
                  refine ⟨8581219320997599524743573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11441625761330132699658097 8581219320997599524743573)
                  ·
                    refine ⟨402244655671762477722355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8581219320997599524743573 402244655671762477722355)
                    ·
                      rfl

theorem cell23_2350106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_2350106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350106 prefixEnd_2350106 := by exact prefixLift 2350106
  have htrace : WordTrace (prefixWord ++ tailWord_2350106) baseStart_2350106 baseEnd_2350106 := by
    simpa [prefixWord, tailWord_2350106, baseEnd_2350106] using wordTrace_append hprefix tailTrace_2350106
  have hstable : (prefixWord ++ tailWord_2350106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350106).length < 2 ^ (prefixWord ++ tailWord_2350106).sum := by decide
  have hdescent : baseEnd_2350106 < baseStart_2350106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350108 : List Nat := [2, 2, 3, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_2350108 : Nat := 118140960795 + 2350108 * 2 ^ 59
def prefixEnd_2350108 : Nat := 4983230072969 + 3 ^ 40 * 2350108 * 2
def baseEnd_2350108 : Nat := 1206734993976596425342057

theorem tailTrace_2350108 : CollatzResearch.WordTrace tailWord_2350108 prefixEnd_2350108 1206734993976596425342057 := by
  unfold tailWord_2350108
  simp only [CollatzResearch.WordTrace]
  refine ⟨42857740284983778668545489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57143653713311704891393985 42857740284983778668545489)
  ·
    refine ⟨32143305213737834001409117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42857740284983778668545489 32143305213737834001409117)
    ·
      refine ⟨12053739455151687750528419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32143305213737834001409117 12053739455151687750528419)
      ·
        refine ⟨18080609182727531625792629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12053739455151687750528419 18080609182727531625792629)
        ·
          refine ⟨1695057110880706089918059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18080609182727531625792629 1695057110880706089918059)
          ·
            refine ⟨2542585666321059134877089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695057110880706089918059 2542585666321059134877089)
            ·
              refine ⟨1906939249740794351157817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542585666321059134877089 1906939249740794351157817)
              ·
                refine ⟨1430204437305595763368363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906939249740794351157817 1430204437305595763368363)
                ·
                  refine ⟨2145306655958393645052545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430204437305595763368363 2145306655958393645052545)
                  ·
                    refine ⟨1608979991968795233789409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2145306655958393645052545 1608979991968795233789409)
                    ·
                      refine ⟨1206734993976596425342057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608979991968795233789409 1206734993976596425342057)
                      ·
                        rfl

theorem cell23_2350108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_2350108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350108 prefixEnd_2350108 := by exact prefixLift 2350108
  have htrace : WordTrace (prefixWord ++ tailWord_2350108) baseStart_2350108 baseEnd_2350108 := by
    simpa [prefixWord, tailWord_2350108, baseEnd_2350108] using wordTrace_append hprefix tailTrace_2350108
  have hstable : (prefixWord ++ tailWord_2350108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350108).length < 2 ^ (prefixWord ++ tailWord_2350108).sum := by decide
  have hdescent : baseEnd_2350108 < baseStart_2350108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350130 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2]
def baseStart_2350130 : Nat := 118140960795 + 2350130 * 2 ^ 59
def prefixEnd_2350130 : Nat := 4983230072969 + 3 ^ 40 * 2350130 * 2
def baseEnd_2350130 : Nat := 1206746290550995339266955

theorem tailTrace_2350130 : CollatzResearch.WordTrace tailWord_2350130 prefixEnd_2350130 1206746290550995339266955 := by
  unfold tailWord_2350130
  simp only [CollatzResearch.WordTrace]
  refine ⟨21429070743971963773597961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57144188650591903396261229 21429070743971963773597961)
  ·
    refine ⟨16071803057978972830198471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21429070743971963773597961 16071803057978972830198471)
    ·
      refine ⟨24107704586968459245297707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16071803057978972830198471 24107704586968459245297707)
      ·
        refine ⟨36161556880452688867946561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24107704586968459245297707 36161556880452688867946561)
        ·
          refine ⟨27121167660339516650959921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36161556880452688867946561 27121167660339516650959921)
          ·
            refine ⟨20340875745254637488219941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27121167660339516650959921 20340875745254637488219941)
            ·
              refine ⟨3813914202235244529041239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20340875745254637488219941 3813914202235244529041239)
              ·
                refine ⟨5720871303352866793561859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3813914202235244529041239 5720871303352866793561859)
                ·
                  refine ⟨8581306955029300190342789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5720871303352866793561859 8581306955029300190342789)
                  ·
                    refine ⟨1608995054067993785689273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8581306955029300190342789 1608995054067993785689273)
                    ·
                      refine ⟨1206746290550995339266955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1608995054067993785689273 1206746290550995339266955)
                      ·
                        rfl

theorem cell23_2350130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_2350130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350130 prefixEnd_2350130 := by exact prefixLift 2350130
  have htrace : WordTrace (prefixWord ++ tailWord_2350130) baseStart_2350130 baseEnd_2350130 := by
    simpa [prefixWord, tailWord_2350130, baseEnd_2350130] using wordTrace_append hprefix tailTrace_2350130
  have hstable : (prefixWord ++ tailWord_2350130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350130).length < 2 ^ (prefixWord ++ tailWord_2350130).sum := by decide
  have hdescent : baseEnd_2350130 < baseStart_2350130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350136 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 9]
def baseStart_2350136 : Nat := 118140960795 + 2350136 * 2 ^ 59
def prefixEnd_2350136 : Nat := 4983230072969 + 3 ^ 40 * 2350136 * 2
def baseEnd_2350136 : Nat := 134083263492769146199103

theorem tailTrace_2350136 : CollatzResearch.WordTrace tailWord_2350136 prefixEnd_2350136 134083263492769146199103 := by
  unfold tailWord_2350136
  simp only [CollatzResearch.WordTrace]
  refine ⟨42858250906933059059555131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57144334542577412079406841 42858250906933059059555131)
  ·
    refine ⟨64287376360399588589332697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42858250906933059059555131 64287376360399588589332697)
    ·
      refine ⟨48215532270299691441999523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64287376360399588589332697 48215532270299691441999523)
      ·
        refine ⟨72323298405449537162999285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48215532270299691441999523 72323298405449537162999285)
        ·
          refine ⟨6780309225510894109031183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72323298405449537162999285 6780309225510894109031183)
          ·
            refine ⟨10170463838266341163546775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6780309225510894109031183 10170463838266341163546775)
            ·
              refine ⟨15255695757399511745320163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10170463838266341163546775 15255695757399511745320163)
              ·
                refine ⟨22883543636099267617980245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15255695757399511745320163 22883543636099267617980245)
                ·
                  refine ⟨134083263492769146199103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22883543636099267617980245 134083263492769146199103)
                  ·
                    rfl

theorem cell23_2350136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 9].length) (baseStart_2350136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350136 prefixEnd_2350136 := by exact prefixLift 2350136
  have htrace : WordTrace (prefixWord ++ tailWord_2350136) baseStart_2350136 baseEnd_2350136 := by
    simpa [prefixWord, tailWord_2350136, baseEnd_2350136] using wordTrace_append hprefix tailTrace_2350136
  have hstable : (prefixWord ++ tailWord_2350136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350136).length < 2 ^ (prefixWord ++ tailWord_2350136).sum := by decide
  have hdescent : baseEnd_2350136 < baseStart_2350136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350176 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2350176 : Nat := 118140960795 + 2350176 * 2 ^ 59
def prefixEnd_2350176 : Nat := 4983230072969 + 3 ^ 40 * 2350176 * 2
def baseEnd_2350176 : Nat := 1206769910661102159291743

theorem tailTrace_2350176 : CollatzResearch.WordTrace tailWord_2350176 prefixEnd_2350176 1206769910661102159291743 := by
  unfold tailWord_2350176
  simp only [CollatzResearch.WordTrace]
  refine ⟨42858980366860602475283191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57145307155814136633710921 42858980366860602475283191)
  ·
    refine ⟨64288470550290903712924787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42858980366860602475283191 64288470550290903712924787)
    ·
      refine ⟨96432705825436355569387181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64288470550290903712924787 96432705825436355569387181)
      ·
        refine ⟨36162264684538633338520193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96432705825436355569387181 36162264684538633338520193)
        ·
          refine ⟨27121698513403975003890145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36162264684538633338520193 27121698513403975003890145)
          ·
            refine ⟨20341273885052981252917609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27121698513403975003890145 20341273885052981252917609)
            ·
              refine ⟨15255955413789735939688207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20341273885052981252917609 15255955413789735939688207)
              ·
                refine ⟨22883933120684603909532311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15255955413789735939688207 22883933120684603909532311)
                ·
                  refine ⟨34325899681026905864298467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22883933120684603909532311 34325899681026905864298467)
                  ·
                    refine ⟨51488849521540358796447701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34325899681026905864298467 51488849521540358796447701)
                    ·
                      refine ⟨1206769910661102159291743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51488849521540358796447701 1206769910661102159291743)
                      ·
                        rfl

theorem cell23_2350176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2350176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350176 prefixEnd_2350176 := by exact prefixLift 2350176
  have htrace : WordTrace (prefixWord ++ tailWord_2350176) baseStart_2350176 baseEnd_2350176 := by
    simpa [prefixWord, tailWord_2350176, baseEnd_2350176] using wordTrace_append hprefix tailTrace_2350176
  have hstable : (prefixWord ++ tailWord_2350176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350176).length < 2 ^ (prefixWord ++ tailWord_2350176).sum := by decide
  have hdescent : baseEnd_2350176 < baseStart_2350176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350203 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 1, 6, 2]
def baseStart_2350203 : Nat := 118140960795 + 2350203 * 2 ^ 59
def prefixEnd_2350203 : Nat := 4983230072969 + 3 ^ 40 * 2350203 * 2
def baseEnd_2350203 : Nat := 1206783774638773553654119

theorem tailTrace_2350203 : CollatzResearch.WordTrace tailWord_2350203 prefixEnd_2350203 1206783774638773553654119 := by
  unfold tailWord_2350203
  simp only [CollatzResearch.WordTrace]
  refine ⟨85718945504623388561799263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57145963669748925707866175 85718945504623388561799263)
  ·
    refine ⟨128578418256935082842698895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85718945504623388561799263 128578418256935082842698895)
    ·
      refine ⟨192867627385402624264048343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128578418256935082842698895 192867627385402624264048343)
      ·
        refine ⟨289301441078103936396072515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192867627385402624264048343 289301441078103936396072515)
        ·
          refine ⟨433952161617155904594108773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289301441078103936396072515 433952161617155904594108773)
          ·
            refine ⟨81366030303216732111395395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 433952161617155904594108773 81366030303216732111395395)
            ·
              refine ⟨122049045454825098167093093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81366030303216732111395395 122049045454825098167093093)
              ·
                refine ⟨22884196022779705906329955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122049045454825098167093093 22884196022779705906329955)
                ·
                  refine ⟨34326294034169558859494933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22884196022779705906329955 34326294034169558859494933)
                  ·
                    refine ⟨1609045032851698071538825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34326294034169558859494933 1609045032851698071538825)
                    ·
                      refine ⟨1206783774638773553654119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609045032851698071538825 1206783774638773553654119)
                      ·
                        rfl

theorem cell23_2350203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 6, 2].length) (baseStart_2350203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350203 prefixEnd_2350203 := by exact prefixLift 2350203
  have htrace : WordTrace (prefixWord ++ tailWord_2350203) baseStart_2350203 baseEnd_2350203 := by
    simpa [prefixWord, tailWord_2350203, baseEnd_2350203] using wordTrace_append hprefix tailTrace_2350203
  have hstable : (prefixWord ++ tailWord_2350203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350203).length < 2 ^ (prefixWord ++ tailWord_2350203).sum := by decide
  have hdescent : baseEnd_2350203 < baseStart_2350203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350256 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 2, 9]
def baseStart_2350256 : Nat := 118140960795 + 2350256 * 2 ^ 59
def prefixEnd_2350256 : Nat := 4983230072969 + 3 ^ 40 * 2350256 * 2
def baseEnd_2350256 : Nat := 402270329704487282097125

theorem tailTrace_2350256 : CollatzResearch.WordTrace tailWord_2350256 prefixEnd_2350256 402270329704487282097125 := by
  unfold tailWord_2350256
  simp only [CollatzResearch.WordTrace]
  refine ⟨42860439286715689306739311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57147252382287585742319081 42860439286715689306739311)
  ·
    refine ⟨64290658930073533960108967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42860439286715689306739311 64290658930073533960108967)
    ·
      refine ⟨96435988395110300940163451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64290658930073533960108967 96435988395110300940163451)
      ·
        refine ⟨144653982592665451410245177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96435988395110300940163451 144653982592665451410245177)
        ·
          refine ⟨108490486944499088557683883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144653982592665451410245177 108490486944499088557683883)
          ·
            refine ⟨162735730416748632836525825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108490486944499088557683883 162735730416748632836525825)
            ·
              refine ⟨122051797812561474627394369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162735730416748632836525825 122051797812561474627394369)
              ·
                refine ⟨91538848359421105970545777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122051797812561474627394369 91538848359421105970545777)
                ·
                  refine ⟨68654136269565829477909333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91538848359421105970545777 68654136269565829477909333)
                  ·
                    refine ⟨402270329704487282097125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 68654136269565829477909333 402270329704487282097125)
                    ·
                      rfl

theorem cell23_2350256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_2350256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350256 prefixEnd_2350256 := by exact prefixLift 2350256
  have htrace : WordTrace (prefixWord ++ tailWord_2350256) baseStart_2350256 baseEnd_2350256 := by
    simpa [prefixWord, tailWord_2350256, baseEnd_2350256] using wordTrace_append hprefix tailTrace_2350256
  have hstable : (prefixWord ++ tailWord_2350256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350256).length < 2 ^ (prefixWord ++ tailWord_2350256).sum := by decide
  have hdescent : baseEnd_2350256 < baseStart_2350256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350257 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2350257 : Nat := 118140960795 + 2350257 * 2 ^ 59
def prefixEnd_2350257 : Nat := 4983230072969 + 3 ^ 40 * 2350257 * 2
def baseEnd_2350257 : Nat := 1206811502594116342378871

theorem tailTrace_2350257 : CollatzResearch.WordTrace tailWord_2350257 prefixEnd_2350257 1206811502594116342378871 := by
  unfold tailWord_2350257
  simp only [CollatzResearch.WordTrace]
  refine ⟨85720915046427755784265025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57147276697618503856176683 85720915046427755784265025)
  ·
    refine ⟨64290686284820816838198769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85720915046427755784265025 64290686284820816838198769)
    ·
      refine ⟨48218014713615612628649077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64290686284820816838198769 48218014713615612628649077)
      ·
        refine ⟨4520438879401463683935851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48218014713615612628649077 4520438879401463683935851)
        ·
          refine ⟨6780658319102195525903777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4520438879401463683935851 6780658319102195525903777)
          ·
            refine ⟨5085493739326646644427833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6780658319102195525903777 5085493739326646644427833)
            ·
              refine ⟨3814120304494984983320875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5085493739326646644427833 3814120304494984983320875)
              ·
                refine ⟨5721180456742477474981313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814120304494984983320875 5721180456742477474981313)
                ·
                  refine ⟨4290885342556858106235985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5721180456742477474981313 4290885342556858106235985)
                  ·
                    refine ⟨3218164006917643579676989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4290885342556858106235985 3218164006917643579676989)
                    ·
                      refine ⟨1206811502594116342378871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3218164006917643579676989 1206811502594116342378871)
                      ·
                        rfl

theorem cell23_2350257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2350257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350257 prefixEnd_2350257 := by exact prefixLift 2350257
  have htrace : WordTrace (prefixWord ++ tailWord_2350257) baseStart_2350257 baseEnd_2350257 := by
    simpa [prefixWord, tailWord_2350257, baseEnd_2350257] using wordTrace_append hprefix tailTrace_2350257
  have hstable : (prefixWord ++ tailWord_2350257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350257).length < 2 ^ (prefixWord ++ tailWord_2350257).sum := by decide
  have hdescent : baseEnd_2350257 < baseStart_2350257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350303 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 1, 6]
def baseStart_2350303 : Nat := 118140960795 + 2350303 * 2 ^ 59
def prefixEnd_2350303 : Nat := 4983230072969 + 3 ^ 40 * 2350303 * 2
def baseEnd_2350303 : Nat := 402278374234741054134553

theorem tailTrace_2350303 : CollatzResearch.WordTrace tailWord_2350303 prefixEnd_2350303 402278374234741054134553 := by
  unfold tailWord_2350303
  simp only [CollatzResearch.WordTrace]
  refine ⟨85722592804261105640439563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57148395202840737093626375 85722592804261105640439563)
  ·
    refine ⟨128583889206391658460659345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85722592804261105640439563 128583889206391658460659345)
    ·
      refine ⟨96437916904793743845494509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128583889206391658460659345 96437916904793743845494509)
      ·
        refine ⟨36164218839297653942060441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96437916904793743845494509 36164218839297653942060441)
        ·
          refine ⟨27123164129473240456545331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36164218839297653942060441 27123164129473240456545331)
          ·
            refine ⟨40684746194209860684817997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27123164129473240456545331 40684746194209860684817997)
            ·
              refine ⟨15256779822828697756806749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40684746194209860684817997 15256779822828697756806749)
              ·
                refine ⟨5721292433560761658802531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15256779822828697756806749 5721292433560761658802531)
                ·
                  refine ⟨8581938650341142488203797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5721292433560761658802531 8581938650341142488203797)
                  ·
                    refine ⟨402278374234741054134553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8581938650341142488203797 402278374234741054134553)
                    ·
                      rfl

theorem cell23_2350303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_2350303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350303 prefixEnd_2350303 := by exact prefixLift 2350303
  have htrace : WordTrace (prefixWord ++ tailWord_2350303) baseStart_2350303 baseEnd_2350303 := by
    simpa [prefixWord, tailWord_2350303, baseEnd_2350303] using wordTrace_append hprefix tailTrace_2350303
  have hstable : (prefixWord ++ tailWord_2350303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350303).length < 2 ^ (prefixWord ++ tailWord_2350303).sum := by decide
  have hdescent : baseEnd_2350303 < baseStart_2350303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350314 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_2350314 : Nat := 118140960795 + 2350314 * 2 ^ 59
def prefixEnd_2350314 : Nat := 4983230072969 + 3 ^ 40 * 2350314 * 2
def baseEnd_2350314 : Nat := 1206840770991422619366109

theorem tailTrace_2350314 : CollatzResearch.WordTrace tailWord_2350314 prefixEnd_2350314 1206840770991422619366109 := by
  unfold tailWord_2350314
  simp only [CollatzResearch.WordTrace]
  refine ⟨21430748501805313629772499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57148662671480836346059997 21430748501805313629772499)
  ·
    refine ⟨32146122752707970444658749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21430748501805313629772499 32146122752707970444658749)
    ·
      refine ⟨12054796032265488916747031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32146122752707970444658749 12054796032265488916747031)
      ·
        refine ⟨18082194048398233375120547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12054796032265488916747031 18082194048398233375120547)
        ·
          refine ⟨27123291072597350062680821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18082194048398233375120547 27123291072597350062680821)
          ·
            refine ⟨2542808538056001568376327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27123291072597350062680821 2542808538056001568376327)
            ·
              refine ⟨3814212807084002352564491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542808538056001568376327 3814212807084002352564491)
              ·
                refine ⟨5721319210626003528846737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814212807084002352564491 5721319210626003528846737)
                ·
                  refine ⟨4290989407969502646635053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5721319210626003528846737 4290989407969502646635053)
                  ·
                    refine ⟨1609121027988563492488145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4290989407969502646635053 1609121027988563492488145)
                    ·
                      refine ⟨1206840770991422619366109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609121027988563492488145 1206840770991422619366109)
                      ·
                        rfl

theorem cell23_2350314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_2350314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350314 prefixEnd_2350314 := by exact prefixLift 2350314
  have htrace : WordTrace (prefixWord ++ tailWord_2350314) baseStart_2350314 baseEnd_2350314 := by
    simpa [prefixWord, tailWord_2350314, baseEnd_2350314] using wordTrace_append hprefix tailTrace_2350314
  have hstable : (prefixWord ++ tailWord_2350314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350314).length < 2 ^ (prefixWord ++ tailWord_2350314).sum := by decide
  have hdescent : baseEnd_2350314 < baseStart_2350314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350337 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2350337 : Nat := 118140960795 + 2350337 * 2 ^ 59
def prefixEnd_2350337 : Nat := 4983230072969 + 3 ^ 40 * 2350337 * 2
def baseEnd_2350337 : Nat := 402284193682158676459501

theorem tailTrace_2350337 : CollatzResearch.WordTrace tailWord_2350337 prefixEnd_2350337 402284193682158676459501 := by
  unfold tailWord_2350337
  simp only [CollatzResearch.WordTrace]
  refine ⟨85723832886137929447177265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57149221924091952964784843 85723832886137929447177265)
  ·
    refine ⟨64292874664603447085382949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85723832886137929447177265 64292874664603447085382949)
    ·
      refine ⟨12054913999613146328509303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64292874664603447085382949 12054913999613146328509303)
      ·
        refine ⟨18082370999419719492763955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12054913999613146328509303 18082370999419719492763955)
        ·
          refine ⟨27123556499129579239145933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18082370999419719492763955 27123556499129579239145933)
          ·
            refine ⟨10171333687173592214679725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27123556499129579239145933 10171333687173592214679725)
            ·
              refine ⟨3814250132690097080504897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10171333687173592214679725 3814250132690097080504897)
              ·
                refine ⟨2860687599517572810378673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3814250132690097080504897 2860687599517572810378673)
                ·
                  refine ⟨2145515699638179607784005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2860687599517572810378673 2145515699638179607784005)
                  ·
                    refine ⟨402284193682158676459501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2145515699638179607784005 402284193682158676459501)
                    ·
                      rfl

theorem cell23_2350337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2350337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350337 prefixEnd_2350337 := by exact prefixLift 2350337
  have htrace : WordTrace (prefixWord ++ tailWord_2350337) baseStart_2350337 baseEnd_2350337 := by
    simpa [prefixWord, tailWord_2350337, baseEnd_2350337] using wordTrace_append hprefix tailTrace_2350337
  have hstable : (prefixWord ++ tailWord_2350337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350337).length < 2 ^ (prefixWord ++ tailWord_2350337).sum := by decide
  have hdescent : baseEnd_2350337 < baseStart_2350337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350367 : List Nat := [1, 1, 2, 4, 4, 2, 2, 7]
def baseStart_2350367 : Nat := 118140960795 + 2350367 * 2 ^ 59
def prefixEnd_2350367 : Nat := 4983230072969 + 3 ^ 40 * 2350367 * 2
def baseEnd_2350367 : Nat := 44698814276522626370495

theorem tailTrace_2350367 : CollatzResearch.WordTrace tailWord_2350367 prefixEnd_2350367 44698814276522626370495 := by
  unfold tailWord_2350367
  simp only [CollatzResearch.WordTrace]
  refine ⟨85724927076029244570769355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57149951384019496380512903 85724927076029244570769355)
  ·
    refine ⟨128587390614043866856154033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85724927076029244570769355 128587390614043866856154033)
    ·
      refine ⟨96440542960532900142115525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128587390614043866856154033 96440542960532900142115525)
      ·
        refine ⟨18082601805099918776646661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96440542960532900142115525 18082601805099918776646661)
        ·
          refine ⟨3390487838456234770621249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18082601805099918776646661 3390487838456234770621249)
          ·
            refine ⟨2542865878842176077965937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3390487838456234770621249 2542865878842176077965937)
            ·
              refine ⟨1907149409131632058474453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542865878842176077965937 1907149409131632058474453)
              ·
                refine ⟨44698814276522626370495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1907149409131632058474453 44698814276522626370495)
                ·
                  rfl

theorem cell23_2350367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 7].length) (baseStart_2350367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350367 prefixEnd_2350367 := by exact prefixLift 2350367
  have htrace : WordTrace (prefixWord ++ tailWord_2350367) baseStart_2350367 baseEnd_2350367 := by
    simpa [prefixWord, tailWord_2350367, baseEnd_2350367] using wordTrace_append hprefix tailTrace_2350367
  have hstable : (prefixWord ++ tailWord_2350367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350367).length < 2 ^ (prefixWord ++ tailWord_2350367).sum := by decide
  have hdescent : baseEnd_2350367 < baseStart_2350367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350378 : List Nat := [3, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2350378 : Nat := 118140960795 + 2350378 * 2 ^ 59
def prefixEnd_2350378 : Nat := 4983230072969 + 3 ^ 40 * 2350378 * 2
def baseEnd_2350378 : Nat := 1206873633753310368965815

theorem tailTrace_2350378 : CollatzResearch.WordTrace tailWord_2350378 prefixEnd_2350378 1206873633753310368965815 := by
  unfold tailWord_2350378
  simp only [CollatzResearch.WordTrace]
  refine ⟨21431332069747348362354947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57150218852659595632946525 21431332069747348362354947)
  ·
    refine ⟨32146998104621022543532421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21431332069747348362354947 32146998104621022543532421)
    ·
      refine ⟨6027562144616441726912329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32146998104621022543532421 6027562144616441726912329)
      ·
        refine ⟨4520671608462331295184247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6027562144616441726912329 4520671608462331295184247)
        ·
          refine ⟨6781007412693496942776371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4520671608462331295184247 6781007412693496942776371)
          ·
            refine ⟨10171511119040245414164557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6781007412693496942776371 10171511119040245414164557)
            ·
              refine ⟨3814316669640092030311709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10171511119040245414164557 3814316669640092030311709)
              ·
                refine ⟨1430368751115034511366891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3814316669640092030311709 1430368751115034511366891)
                ·
                  refine ⟨2145553126672551767050337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430368751115034511366891 2145553126672551767050337)
                  ·
                    refine ⟨1609164845004413825287753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2145553126672551767050337 1609164845004413825287753)
                    ·
                      refine ⟨1206873633753310368965815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609164845004413825287753 1206873633753310368965815)
                      ·
                        rfl

theorem cell23_2350378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2350378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350378 prefixEnd_2350378 := by exact prefixLift 2350378
  have htrace : WordTrace (prefixWord ++ tailWord_2350378) baseStart_2350378 baseEnd_2350378 := by
    simpa [prefixWord, tailWord_2350378, baseEnd_2350378] using wordTrace_append hprefix tailTrace_2350378
  have hstable : (prefixWord ++ tailWord_2350378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350378).length < 2 ^ (prefixWord ++ tailWord_2350378).sum := by decide
  have hdescent : baseEnd_2350378 < baseStart_2350378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350383 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_2350383 : Nat := 118140960795 + 2350383 * 2 ^ 59
def prefixEnd_2350383 : Nat := 4983230072969 + 3 ^ 40 * 2350383 * 2
def baseEnd_2350383 : Nat := 1206876201156582849403291

theorem tailTrace_2350383 : CollatzResearch.WordTrace tailWord_2350383 prefixEnd_2350383 1206876201156582849403291 := by
  unfold tailWord_2350383
  simp only [CollatzResearch.WordTrace]
  refine ⟨85725510643971279303351803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57150340429314186202234535 85725510643971279303351803)
  ·
    refine ⟨128588265965956918955027705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85725510643971279303351803 128588265965956918955027705)
    ·
      refine ⟨96441199474467689216270779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128588265965956918955027705 96441199474467689216270779)
      ·
        refine ⟨144661799211701533824406169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96441199474467689216270779 144661799211701533824406169)
        ·
          refine ⟨108496349408776150368304627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144661799211701533824406169 108496349408776150368304627)
          ·
            refine ⟨162744524113164225552456941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108496349408776150368304627 162744524113164225552456941)
            ·
              refine ⟨61029196542436584582171353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162744524113164225552456941 61029196542436584582171353)
              ·
                refine ⟨45771897406827438436628515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61029196542436584582171353 45771897406827438436628515)
                ·
                  refine ⟨68657846110241157654942773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45771897406827438436628515 68657846110241157654942773)
                  ·
                    refine ⟨6436673072835108530150885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68657846110241157654942773 6436673072835108530150885)
                    ·
                      refine ⟨1206876201156582849403291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6436673072835108530150885 1206876201156582849403291)
                      ·
                        rfl

theorem cell23_2350383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_2350383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350383 prefixEnd_2350383 := by exact prefixLift 2350383
  have htrace : WordTrace (prefixWord ++ tailWord_2350383) baseStart_2350383 baseEnd_2350383 := by
    simpa [prefixWord, tailWord_2350383, baseEnd_2350383] using wordTrace_append hprefix tailTrace_2350383
  have hstable : (prefixWord ++ tailWord_2350383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350383).length < 2 ^ (prefixWord ++ tailWord_2350383).sum := by decide
  have hdescent : baseEnd_2350383 < baseStart_2350383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350403 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 5]
def baseStart_2350403 : Nat := 118140960795 + 2350403 * 2 ^ 59
def prefixEnd_2350403 : Nat := 4983230072969 + 3 ^ 40 * 2350403 * 2
def baseEnd_2350403 : Nat := 1206886470769672771153199

theorem tailTrace_2350403 : CollatzResearch.WordTrace tailWord_2350403 prefixEnd_2350403 1206886470769672771153199 := by
  unfold tailWord_2350403
  simp only [CollatzResearch.WordTrace]
  refine ⟨85726240103898822719079863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57150826735932548479386575 85726240103898822719079863)
  ·
    refine ⟨128589360155848234078619795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85726240103898822719079863 128589360155848234078619795)
    ·
      refine ⟨192884040233772351117929693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128589360155848234078619795 192884040233772351117929693)
      ·
        refine ⟨72331515087664631669223635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192884040233772351117929693 72331515087664631669223635)
        ·
          refine ⟨108497272631496947503835453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72331515087664631669223635 108497272631496947503835453)
          ·
            refine ⟨40686477236811355313938295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108497272631496947503835453 40686477236811355313938295)
            ·
              refine ⟨61029715855217032970907443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40686477236811355313938295 61029715855217032970907443)
              ·
                refine ⟨91544573782825549456361165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61029715855217032970907443 91544573782825549456361165)
                ·
                  refine ⟨34329215168559581046135437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91544573782825549456361165 34329215168559581046135437)
                  ·
                    refine ⟨12873455688209842892300789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34329215168559581046135437 12873455688209842892300789)
                    ·
                      refine ⟨1206886470769672771153199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12873455688209842892300789 1206886470769672771153199)
                      ·
                        rfl

theorem cell23_2350403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_2350403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350403 prefixEnd_2350403 := by exact prefixLift 2350403
  have htrace : WordTrace (prefixWord ++ tailWord_2350403) baseStart_2350403 baseEnd_2350403 := by
    simpa [prefixWord, tailWord_2350403, baseEnd_2350403] using wordTrace_append hprefix tailTrace_2350403
  have hstable : (prefixWord ++ tailWord_2350403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350403).length < 2 ^ (prefixWord ++ tailWord_2350403).sum := by decide
  have hdescent : baseEnd_2350403 < baseStart_2350403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350417 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 1, 4, 2]
def baseStart_2350417 : Nat := 118140960795 + 2350417 * 2 ^ 59
def prefixEnd_2350417 : Nat := 4983230072969 + 3 ^ 40 * 2350417 * 2
def baseEnd_2350417 : Nat := 1206893659498835716378135

theorem tailTrace_2350417 : CollatzResearch.WordTrace tailWord_2350417 prefixEnd_2350417 1206893659498835716378135 := by
  unfold tailWord_2350417
  simp only [CollatzResearch.WordTrace]
  refine ⟨85726750725848103110089505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57151167150565402073393003 85726750725848103110089505)
  ·
    refine ⟨64295063044386077332567129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85726750725848103110089505 64295063044386077332567129)
    ·
      refine ⟨48221297283289557999425347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64295063044386077332567129 48221297283289557999425347)
      ·
        refine ⟨72331945924934336999138021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48221297283289557999425347 72331945924934336999138021)
        ·
          refine ⟨13562239860925188187338379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72331945924934336999138021 13562239860925188187338379)
          ·
            refine ⟨20343359791387782281007569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13562239860925188187338379 20343359791387782281007569)
            ·
              refine ⟨15257519843540836710755677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20343359791387782281007569 15257519843540836710755677)
              ·
                refine ⟨5721569941327813766533379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15257519843540836710755677 5721569941327813766533379)
                ·
                  refine ⟨8582354911991720649800069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5721569941327813766533379 8582354911991720649800069)
                  ·
                    refine ⟨1609191545998447621837513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8582354911991720649800069 1609191545998447621837513)
                    ·
                      refine ⟨1206893659498835716378135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609191545998447621837513 1206893659498835716378135)
                      ·
                        rfl

theorem cell23_2350417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_2350417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350417 prefixEnd_2350417 := by exact prefixLift 2350417
  have htrace : WordTrace (prefixWord ++ tailWord_2350417) baseStart_2350417 baseEnd_2350417 := by
    simpa [prefixWord, tailWord_2350417, baseEnd_2350417] using wordTrace_append hprefix tailTrace_2350417
  have hstable : (prefixWord ++ tailWord_2350417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350417).length < 2 ^ (prefixWord ++ tailWord_2350417).sum := by decide
  have hdescent : baseEnd_2350417 < baseStart_2350417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350420 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2350420 : Nat := 118140960795 + 2350420 * 2 ^ 59
def prefixEnd_2350420 : Nat := 4983230072969 + 3 ^ 40 * 2350420 * 2
def baseEnd_2350420 : Nat := 1206895199940799204640621

theorem tailTrace_2350420 : CollatzResearch.WordTrace tailWord_2350420 prefixEnd_2350420 1206895199940799204640621 := by
  unfold tailWord_2350420
  simp only [CollatzResearch.WordTrace]
  refine ⟨42863430072418617311224357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57151240096558156414965809 42863430072418617311224357)
  ·
    refine ⟨8036893138578490745854567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42863430072418617311224357 8036893138578490745854567)
    ·
      refine ⟨12055339707867736118781851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8036893138578490745854567 12055339707867736118781851)
      ·
        refine ⟨18083009561801604178172777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12055339707867736118781851 18083009561801604178172777)
        ·
          refine ⟨13562257171351203133629583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18083009561801604178172777 13562257171351203133629583)
          ·
            refine ⟨20343385757026804700444375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13562257171351203133629583 20343385757026804700444375)
            ·
              refine ⟨30515078635540207050666563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20343385757026804700444375 30515078635540207050666563)
              ·
                refine ⟨45772617953310310575999845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30515078635540207050666563 45772617953310310575999845)
                ·
                  refine ⟨8582365866245683232999971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45772617953310310575999845 8582365866245683232999971)
                  ·
                    refine ⟨12873548799368524849499957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8582365866245683232999971 12873548799368524849499957)
                    ·
                      refine ⟨1206895199940799204640621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12873548799368524849499957 1206895199940799204640621)
                      ·
                        rfl

theorem cell23_2350420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2350420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350420 prefixEnd_2350420 := by exact prefixLift 2350420
  have htrace : WordTrace (prefixWord ++ tailWord_2350420) baseStart_2350420 baseEnd_2350420 := by
    simpa [prefixWord, tailWord_2350420, baseEnd_2350420] using wordTrace_append hprefix tailTrace_2350420
  have hstable : (prefixWord ++ tailWord_2350420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350420).length < 2 ^ (prefixWord ++ tailWord_2350420).sum := by decide
  have hdescent : baseEnd_2350420 < baseStart_2350420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350421 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 1, 3, 2]
def baseStart_2350421 : Nat := 118140960795 + 2350421 * 2 ^ 59
def prefixEnd_2350421 : Nat := 4983230072969 + 3 ^ 40 * 2350421 * 2
def baseEnd_2350421 : Nat := 1206895713421453700728117

theorem tailTrace_2350421 : CollatzResearch.WordTrace tailWord_2350421 prefixEnd_2350421 1206895713421453700728117 := by
  unfold tailWord_2350421
  simp only [CollatzResearch.WordTrace]
  refine ⟨85726896617833611793235117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57151264411889074528823411 85726896617833611793235117)
  ·
    refine ⟨32147586231687604422463169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85726896617833611793235117 32147586231687604422463169)
    ·
      refine ⟨24110689673765703316847377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32147586231687604422463169 24110689673765703316847377)
      ·
        refine ⟨18083017255324277487635533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24110689673765703316847377 18083017255324277487635533)
        ·
          refine ⟨6781131470746604057863325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18083017255324277487635533 6781131470746604057863325)
          ·
            refine ⟨2542924301529976521698747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6781131470746604057863325 2542924301529976521698747)
            ·
              refine ⟨3814386452294964782548121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542924301529976521698747 3814386452294964782548121)
              ·
                refine ⟨2860789839221223586911091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3814386452294964782548121 2860789839221223586911091)
                ·
                  refine ⟨4291184758831835380366637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2860789839221223586911091 4291184758831835380366637)
                  ·
                    refine ⟨1609194284561938267637489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4291184758831835380366637 1609194284561938267637489)
                    ·
                      refine ⟨1206895713421453700728117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609194284561938267637489 1206895713421453700728117)
                      ·
                        rfl

theorem cell23_2350421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_2350421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350421 prefixEnd_2350421 := by exact prefixLift 2350421
  have htrace : WordTrace (prefixWord ++ tailWord_2350421) baseStart_2350421 baseEnd_2350421 := by
    simpa [prefixWord, tailWord_2350421, baseEnd_2350421] using wordTrace_append hprefix tailTrace_2350421
  have hstable : (prefixWord ++ tailWord_2350421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350421).length < 2 ^ (prefixWord ++ tailWord_2350421).sum := by decide
  have hdescent : baseEnd_2350421 < baseStart_2350421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350434 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_2350434 : Nat := 118140960795 + 2350434 * 2 ^ 59
def prefixEnd_2350434 : Nat := 4983230072969 + 3 ^ 40 * 2350434 * 2
def baseEnd_2350434 : Nat := 1206902388669962149865557

theorem tailTrace_2350434 : CollatzResearch.WordTrace tailWord_2350434 prefixEnd_2350434 1206902388669962149865557 := by
  unfold tailWord_2350434
  simp only [CollatzResearch.WordTrace]
  refine ⟨21431842691696628753364589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57151580511191010008972237 21431842691696628753364589)
  ·
    refine ⟨8036941009386235782511721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21431842691696628753364589 8036941009386235782511721)
    ·
      refine ⟨6027705757039676836883791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8036941009386235782511721 6027705757039676836883791)
      ·
        refine ⟨9041558635559515255325687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6027705757039676836883791 9041558635559515255325687)
        ·
          refine ⟨13562337953339272882988531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9041558635559515255325687 13562337953339272882988531)
          ·
            refine ⟨20343506930008909324482797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13562337953339272882988531 20343506930008909324482797)
            ·
              refine ⟨7628815098753340996681049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20343506930008909324482797 7628815098753340996681049)
              ·
                refine ⟨5721611324065005747510787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7628815098753340996681049 5721611324065005747510787)
                ·
                  refine ⟨8582416986097508621266181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5721611324065005747510787 8582416986097508621266181)
                  ·
                    refine ⟨1609203184893282866487409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8582416986097508621266181 1609203184893282866487409)
                    ·
                      refine ⟨1206902388669962149865557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609203184893282866487409 1206902388669962149865557)
                      ·
                        rfl

theorem cell23_2350434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_2350434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350434 prefixEnd_2350434 := by exact prefixLift 2350434
  have htrace : WordTrace (prefixWord ++ tailWord_2350434) baseStart_2350434 baseEnd_2350434 := by
    simpa [prefixWord, tailWord_2350434, baseEnd_2350434] using wordTrace_append hprefix tailTrace_2350434
  have hstable : (prefixWord ++ tailWord_2350434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350434).length < 2 ^ (prefixWord ++ tailWord_2350434).sum := by decide
  have hdescent : baseEnd_2350434 < baseStart_2350434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350443 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 6]
def baseStart_2350443 : Nat := 118140960795 + 2350443 * 2 ^ 59
def prefixEnd_2350443 : Nat := 4983230072969 + 3 ^ 40 * 2350443 * 2
def baseEnd_2350443 : Nat := 1206907009995852614653015

theorem tailTrace_2350443 : CollatzResearch.WordTrace tailWord_2350443 prefixEnd_2350443 1206907009995852614653015 := by
  unfold tailWord_2350443
  simp only [CollatzResearch.WordTrace]
  refine ⟨85727699023753909550535983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57151799349169273033690655 85727699023753909550535983)
  ·
    refine ⟨128591548535630864325803975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85727699023753909550535983 128591548535630864325803975)
    ·
      refine ⟨192887322803446296488705963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128591548535630864325803975 192887322803446296488705963)
      ·
        refine ⟨289330984205169444733058945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192887322803446296488705963 289330984205169444733058945)
        ·
          refine ⟨216998238153877083549794209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289330984205169444733058945 216998238153877083549794209)
          ·
            refine ⟨162748678615407812662345657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216998238153877083549794209 162748678615407812662345657)
            ·
              refine ⟨122061508961555859496759243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162748678615407812662345657 122061508961555859496759243)
              ·
                refine ⟨183092263442333789245138865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122061508961555859496759243 183092263442333789245138865)
                ·
                  refine ⟨137319197581750341933854149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183092263442333789245138865 137319197581750341933854149)
                  ·
                    refine ⟨25747349546578189112597653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137319197581750341933854149 25747349546578189112597653)
                    ·
                      refine ⟨1206907009995852614653015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25747349546578189112597653 1206907009995852614653015)
                      ·
                        rfl

theorem cell23_2350443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_2350443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350443 prefixEnd_2350443 := by exact prefixLift 2350443
  have htrace : WordTrace (prefixWord ++ tailWord_2350443) baseStart_2350443 baseEnd_2350443 := by
    simpa [prefixWord, tailWord_2350443, baseEnd_2350443] using wordTrace_append hprefix tailTrace_2350443
  have hstable : (prefixWord ++ tailWord_2350443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350443).length < 2 ^ (prefixWord ++ tailWord_2350443).sum := by decide
  have hdescent : baseEnd_2350443 < baseStart_2350443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350467 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 3]
def baseStart_2350467 : Nat := 118140960795 + 2350467 * 2 ^ 59
def prefixEnd_2350467 : Nat := 4983230072969 + 3 ^ 40 * 2350467 * 2
def baseEnd_2350467 : Nat := 1206919333531560520752905

theorem tailTrace_2350467 : CollatzResearch.WordTrace tailWord_2350467 prefixEnd_2350467 1206919333531560520752905 := by
  unfold tailWord_2350467
  simp only [CollatzResearch.WordTrace]
  refine ⟨85728574375666961649409655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57152382917111307766273103 85728574375666961649409655)
  ·
    refine ⟨128592861563500442474114483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85728574375666961649409655 128592861563500442474114483)
    ·
      refine ⟨192889292345250663711171725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128592861563500442474114483 192889292345250663711171725)
      ·
        refine ⟨72333484629468998891689397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192889292345250663711171725 72333484629468998891689397)
        ·
          refine ⟨6781264184012718646095881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72333484629468998891689397 6781264184012718646095881)
          ·
            refine ⟨5085948138009538984571911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6781264184012718646095881 5085948138009538984571911)
            ·
              refine ⟨7628922207014308476857867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5085948138009538984571911 7628922207014308476857867)
              ·
                refine ⟨11443383310521462715286801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7628922207014308476857867 11443383310521462715286801)
                ·
                  refine ⟨8582537482891097036465101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11443383310521462715286801 8582537482891097036465101)
                  ·
                    refine ⟨3218451556084161388674413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8582537482891097036465101 3218451556084161388674413)
                    ·
                      refine ⟨1206919333531560520752905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3218451556084161388674413 1206919333531560520752905)
                      ·
                        rfl

theorem cell23_2350467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_2350467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350467 prefixEnd_2350467 := by exact prefixLift 2350467
  have htrace : WordTrace (prefixWord ++ tailWord_2350467) baseStart_2350467 baseEnd_2350467 := by
    simpa [prefixWord, tailWord_2350467, baseEnd_2350467] using wordTrace_append hprefix tailTrace_2350467
  have hstable : (prefixWord ++ tailWord_2350467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350467).length < 2 ^ (prefixWord ++ tailWord_2350467).sum := by decide
  have hdescent : baseEnd_2350467 < baseStart_2350467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350581 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 6]
def baseStart_2350581 : Nat := 118140960795 + 2350581 * 2 ^ 59
def prefixEnd_2350581 : Nat := 4983230072969 + 3 ^ 40 * 2350581 * 2
def baseEnd_2350581 : Nat := 134108652258463674969709

theorem tailTrace_2350581 : CollatzResearch.WordTrace tailWord_2350581 prefixEnd_2350581 134108652258463674969709 := by
  unfold tailWord_2350581
  simp only [CollatzResearch.WordTrace]
  refine ⟨85732732297253959119059597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57155154864835972746039731 85732732297253959119059597)
  ·
    refine ⟨32149774611470234669647349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85732732297253959119059597 32149774611470234669647349)
    ·
      refine ⟨3014041369825334500279439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32149774611470234669647349 3014041369825334500279439)
      ·
        refine ⟨4521062054738001750419159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014041369825334500279439 4521062054738001750419159)
        ·
          refine ⟨6781593082107002625628739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4521062054738001750419159 6781593082107002625628739)
          ·
            refine ⟨10172389623160503938443109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6781593082107002625628739 10172389623160503938443109)
            ·
              refine ⟨1907323054342594488458083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10172389623160503938443109 1907323054342594488458083)
              ·
                refine ⟨2860984581513891732687125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907323054342594488458083 2860984581513891732687125)
                ·
                  refine ⟨134108652258463674969709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2860984581513891732687125 134108652258463674969709)
                  ·
                    rfl

theorem cell23_2350581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_2350581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350581 prefixEnd_2350581 := by exact prefixLift 2350581
  have htrace : WordTrace (prefixWord ++ tailWord_2350581) baseStart_2350581 baseEnd_2350581 := by
    simpa [prefixWord, tailWord_2350581, baseEnd_2350581] using wordTrace_append hprefix tailTrace_2350581
  have hstable : (prefixWord ++ tailWord_2350581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350581).length < 2 ^ (prefixWord ++ tailWord_2350581).sum := by decide
  have hdescent : baseEnd_2350581 < baseStart_2350581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350617 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 7, 2, 3]
def baseStart_2350617 : Nat := 118140960795 + 2350617 * 2 ^ 59
def prefixEnd_2350617 : Nat := 4983230072969 + 3 ^ 40 * 2350617 * 2
def baseEnd_2350617 : Nat := 1206996355629734933877215

theorem tailTrace_2350617 : CollatzResearch.WordTrace tailWord_2350617 prefixEnd_2350617 1206996355629734933877215 := by
  unfold tailWord_2350617
  simp only [CollatzResearch.WordTrace]
  refine ⟨85734045325123537267370105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57156030216749024844913403 85734045325123537267370105)
  ·
    refine ⟨64300533993842652950527579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85734045325123537267370105 64300533993842652950527579)
    ·
      refine ⟨96450800990763979425791369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64300533993842652950527579 96450800990763979425791369)
      ·
        refine ⟨72338100743072984569343527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96450800990763979425791369 72338100743072984569343527)
        ·
          refine ⟨108507151114609476854015291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72338100743072984569343527 108507151114609476854015291)
          ·
            refine ⟨162760726671914215281022937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108507151114609476854015291 162760726671914215281022937)
            ·
              refine ⟨122070545003935661460767203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162760726671914215281022937 122070545003935661460767203)
              ·
                refine ⟨183105817505903492191150805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122070545003935661460767203 183105817505903492191150805)
                ·
                  refine ⟨4291542597794613098230097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 183105817505903492191150805 4291542597794613098230097)
                  ·
                    refine ⟨3218656948345959823672573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4291542597794613098230097 3218656948345959823672573)
                    ·
                      refine ⟨1206996355629734933877215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3218656948345959823672573 1206996355629734933877215)
                      ·
                        rfl

theorem cell23_2350617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_2350617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350617 prefixEnd_2350617 := by exact prefixLift 2350617
  have htrace : WordTrace (prefixWord ++ tailWord_2350617) baseStart_2350617 baseEnd_2350617 := by
    simpa [prefixWord, tailWord_2350617, baseEnd_2350617] using wordTrace_append hprefix tailTrace_2350617
  have hstable : (prefixWord ++ tailWord_2350617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350617).length < 2 ^ (prefixWord ++ tailWord_2350617).sum := by decide
  have hdescent : baseEnd_2350617 < baseStart_2350617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350625 : List Nat := [1, 2, 3, 2, 2, 4, 2, 2, 1, 1, 3]
def baseStart_2350625 : Nat := 118140960795 + 2350625 * 2 ^ 59
def prefixEnd_2350625 : Nat := 4983230072969 + 3 ^ 40 * 2350625 * 2
def baseEnd_2350625 : Nat := 1207000463474970902577179

theorem tailTrace_2350625 : CollatzResearch.WordTrace tailWord_2350625 prefixEnd_2350625 1207000463474970902577179 := by
  unfold tailWord_2350625
  simp only [CollatzResearch.WordTrace]
  refine ⟨85734337109094554633661329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57156224739396369755774219 85734337109094554633661329)
  ·
    refine ⟨64300752831820915975245997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85734337109094554633661329 64300752831820915975245997)
    ·
      refine ⟨24112782311932843490717249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64300752831820915975245997 24112782311932843490717249)
      ·
        refine ⟨18084586733949632618037937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24112782311932843490717249 18084586733949632618037937)
        ·
          refine ⟨13563440050462224463528453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18084586733949632618037937 13563440050462224463528453)
          ·
            refine ⟨2543145009461667086911585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13563440050462224463528453 2543145009461667086911585)
            ·
              refine ⟨1907358757096250315183689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2543145009461667086911585 1907358757096250315183689)
              ·
                refine ⟨1430519067822187736387767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1907358757096250315183689 1430519067822187736387767)
                ·
                  refine ⟨2145778601733281604581651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430519067822187736387767 2145778601733281604581651)
                  ·
                    refine ⟨3218667902599922406872477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2145778601733281604581651 3218667902599922406872477)
                    ·
                      refine ⟨1207000463474970902577179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3218667902599922406872477 1207000463474970902577179)
                      ·
                        rfl

theorem cell23_2350625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_2350625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350625 prefixEnd_2350625 := by exact prefixLift 2350625
  have htrace : WordTrace (prefixWord ++ tailWord_2350625) baseStart_2350625 baseEnd_2350625 := by
    simpa [prefixWord, tailWord_2350625, baseEnd_2350625] using wordTrace_append hprefix tailTrace_2350625
  have hstable : (prefixWord ++ tailWord_2350625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350625).length < 2 ^ (prefixWord ++ tailWord_2350625).sum := by decide
  have hdescent : baseEnd_2350625 < baseStart_2350625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350634 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2350634 : Nat := 118140960795 + 2350634 * 2 ^ 59
def prefixEnd_2350634 : Nat := 4983230072969 + 3 ^ 40 * 2350634 * 2
def baseEnd_2350634 : Nat := 1207005084800861367364637

theorem tailTrace_2350634 : CollatzResearch.WordTrace tailWord_2350634 prefixEnd_2350634 1207005084800861367364637 := by
  unfold tailWord_2350634
  simp only [CollatzResearch.WordTrace]
  refine ⟨21433666341515487292684739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57156443577374632780492637 21433666341515487292684739)
  ·
    refine ⟨32150499512273230939027109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21433666341515487292684739 32150499512273230939027109)
    ·
      refine ⟨6028218658551230801067583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32150499512273230939027109 6028218658551230801067583)
      ·
        refine ⟨9042327987826846201601375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6028218658551230801067583 9042327987826846201601375)
        ·
          refine ⟨13563491981740269302402063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9042327987826846201601375 13563491981740269302402063)
          ·
            refine ⟨20345237972610403953603095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13563491981740269302402063 20345237972610403953603095)
            ·
              refine ⟨30517856958915605930404643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20345237972610403953603095 30517856958915605930404643)
              ·
                refine ⟨45776785438373408895606965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30517856958915605930404643 45776785438373408895606965)
                ·
                  refine ⟨4291573634847507083963153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45776785438373408895606965 4291573634847507083963153)
                  ·
                    refine ⟨3218680226135630312972365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4291573634847507083963153 3218680226135630312972365)
                    ·
                      refine ⟨1207005084800861367364637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3218680226135630312972365 1207005084800861367364637)
                      ·
                        rfl

theorem cell23_2350634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2350634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350634 prefixEnd_2350634 := by exact prefixLift 2350634
  have htrace : WordTrace (prefixWord ++ tailWord_2350634) baseStart_2350634 baseEnd_2350634 := by
    simpa [prefixWord, tailWord_2350634, baseEnd_2350634] using wordTrace_append hprefix tailTrace_2350634
  have hstable : (prefixWord ++ tailWord_2350634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350634).length < 2 ^ (prefixWord ++ tailWord_2350634).sum := by decide
  have hdescent : baseEnd_2350634 < baseStart_2350634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350662 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_2350662 : Nat := 118140960795 + 2350662 * 2 ^ 59
def prefixEnd_2350662 : Nat := 4983230072969 + 3 ^ 40 * 2350662 * 2
def baseEnd_2350662 : Nat := 402339820753062419271503

theorem tailTrace_2350662 : CollatzResearch.WordTrace tailWord_2350662 prefixEnd_2350662 402339820753062419271503 := by
  unfold tailWord_2350662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679240206561265936023695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57157124406640339968505493 2679240206561265936023695)
  ·
    refine ⟨4018860309841898904035543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2679240206561265936023695 4018860309841898904035543)
    ·
      refine ⟨6028290464762848356053315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4018860309841898904035543 6028290464762848356053315)
      ·
        refine ⟨9042435697144272534079973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6028290464762848356053315 9042435697144272534079973)
        ·
          refine ⟨1695456693214551100139995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9042435697144272534079973 1695456693214551100139995)
          ·
            refine ⟨2543185039821826650209993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695456693214551100139995 2543185039821826650209993)
            ·
              refine ⟨1907388779866369987657495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2543185039821826650209993 1907388779866369987657495)
              ·
                refine ⟨2861083169799554981486243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907388779866369987657495 2861083169799554981486243)
                ·
                  refine ⟨4291624754699332472229365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861083169799554981486243 4291624754699332472229365)
                  ·
                    refine ⟨402339820753062419271503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4291624754699332472229365 402339820753062419271503)
                    ·
                      rfl

theorem cell23_2350662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_2350662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350662 prefixEnd_2350662 := by exact prefixLift 2350662
  have htrace : WordTrace (prefixWord ++ tailWord_2350662) baseStart_2350662 baseEnd_2350662 := by
    simpa [prefixWord, tailWord_2350662, baseEnd_2350662] using wordTrace_append hprefix tailTrace_2350662
  have hstable : (prefixWord ++ tailWord_2350662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350662).length < 2 ^ (prefixWord ++ tailWord_2350662).sum := by decide
  have hdescent : baseEnd_2350662 < baseStart_2350662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350668 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 1, 2, 3]
def baseStart_2350668 : Nat := 118140960795 + 2350668 * 2 ^ 59
def prefixEnd_2350668 : Nat := 4983230072969 + 3 ^ 40 * 2350668 * 2
def baseEnd_2350668 : Nat := 1207022543143114234339481

theorem tailTrace_2350668 : CollatzResearch.WordTrace tailWord_2350668 prefixEnd_2350668 1207022543143114234339481 := by
  unfold tailWord_2350668
  simp only [CollatzResearch.WordTrace]
  refine ⟨42867952723969386488738329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57157270298625848651651105 42867952723969386488738329)
  ·
    refine ⟨32150964542977039866553747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42867952723969386488738329 32150964542977039866553747)
    ·
      refine ⟨48226446814465559799830621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32150964542977039866553747 48226446814465559799830621)
      ·
        refine ⟨18084917555424584924936483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48226446814465559799830621 18084917555424584924936483)
        ·
          refine ⟨27127376333136877387404725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18084917555424584924936483 27127376333136877387404725)
          ·
            refine ⟨2543191531231582255069193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27127376333136877387404725 2543191531231582255069193)
            ·
              refine ⟨1907393648423686691301895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2543191531231582255069193 1907393648423686691301895)
              ·
                refine ⟨2861090472635530036952843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907393648423686691301895 2861090472635530036952843)
                ·
                  refine ⟨4291635708953295055429265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861090472635530036952843 4291635708953295055429265)
                  ·
                    refine ⟨3218726781714971291571949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4291635708953295055429265 3218726781714971291571949)
                    ·
                      refine ⟨1207022543143114234339481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3218726781714971291571949 1207022543143114234339481)
                      ·
                        rfl

theorem cell23_2350668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_2350668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350668 prefixEnd_2350668 := by exact prefixLift 2350668
  have htrace : WordTrace (prefixWord ++ tailWord_2350668) baseStart_2350668 baseEnd_2350668 := by
    simpa [prefixWord, tailWord_2350668, baseEnd_2350668] using wordTrace_append hprefix tailTrace_2350668
  have hstable : (prefixWord ++ tailWord_2350668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350668).length < 2 ^ (prefixWord ++ tailWord_2350668).sum := by decide
  have hdescent : baseEnd_2350668 < baseStart_2350668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350697 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 2, 6]
def baseStart_2350697 : Nat := 118140960795 + 2350697 * 2 ^ 59
def prefixEnd_2350697 : Nat := 4983230072969 + 3 ^ 40 * 2350697 * 2
def baseEnd_2350697 : Nat := 402345811360698206958949

theorem tailTrace_2350697 : CollatzResearch.WordTrace tailWord_2350697 prefixEnd_2350697 402345811360698206958949 := by
  unfold tailWord_2350697
  simp only [CollatzResearch.WordTrace]
  refine ⟨85736963164833710930282345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57157975443222473953521563 85736963164833710930282345)
  ·
    refine ⟨64302722373625283197711759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85736963164833710930282345 64302722373625283197711759)
    ·
      refine ⟨96454083560437924796567639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64302722373625283197711759 96454083560437924796567639)
      ·
        refine ⟨144681125340656887194851459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96454083560437924796567639 144681125340656887194851459)
        ·
          refine ⟨217021688010985330792277189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144681125340656887194851459 217021688010985330792277189)
          ·
            refine ⟨40691566502059749523551973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217021688010985330792277189 40691566502059749523551973)
            ·
              refine ⟨7629668719136203035665995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40691566502059749523551973 7629668719136203035665995)
              ·
                refine ⟨11444503078704304553498993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7629668719136203035665995 11444503078704304553498993)
                ·
                  refine ⟨8583377309028228415124245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11444503078704304553498993 8583377309028228415124245)
                  ·
                    refine ⟨402345811360698206958949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8583377309028228415124245 402345811360698206958949)
                    ·
                      rfl

theorem cell23_2350697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_2350697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350697 prefixEnd_2350697 := by exact prefixLift 2350697
  have htrace : WordTrace (prefixWord ++ tailWord_2350697) baseStart_2350697 baseEnd_2350697 := by
    simpa [prefixWord, tailWord_2350697, baseEnd_2350697] using wordTrace_append hprefix tailTrace_2350697
  have hstable : (prefixWord ++ tailWord_2350697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350697).length < 2 ^ (prefixWord ++ tailWord_2350697).sum := by decide
  have hdescent : baseEnd_2350697 < baseStart_2350697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350707 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 3]
def baseStart_2350707 : Nat := 118140960795 + 2350707 * 2 ^ 59
def prefixEnd_2350707 : Nat := 4983230072969 + 3 ^ 40 * 2350707 * 2
def baseEnd_2350707 : Nat := 1207042568888639581751801

theorem tailTrace_2350707 : CollatzResearch.WordTrace tailWord_2350707 prefixEnd_2350707 1207042568888639581751801 := by
  unfold tailWord_2350707
  simp only [CollatzResearch.WordTrace]
  refine ⟨85737327894797482638146375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57158218596531655092097583 85737327894797482638146375)
  ·
    refine ⟨128605991842196223957219563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85737327894797482638146375 128605991842196223957219563)
    ·
      refine ⟨192908987763294335935829345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128605991842196223957219563 192908987763294335935829345)
      ·
        refine ⟨144681740822470751951872009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192908987763294335935829345 144681740822470751951872009)
        ·
          refine ⟨108511305616853063963904007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144681740822470751951872009 108511305616853063963904007)
          ·
            refine ⟨162766958425279595945856011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108511305616853063963904007 162766958425279595945856011)
            ·
              refine ⟨244150437637919393918784017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162766958425279595945856011 244150437637919393918784017)
              ·
                refine ⟨183112828228439545439088013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244150437637919393918784017 183112828228439545439088013)
                ·
                  refine ⟨68667310585664829539658005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183112828228439545439088013 68667310585664829539658005)
                  ·
                    refine ⟨3218780183703038884671469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68667310585664829539658005 3218780183703038884671469)
                    ·
                      refine ⟨1207042568888639581751801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3218780183703038884671469 1207042568888639581751801)
                      ·
                        rfl

theorem cell23_2350707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 3].length) (baseStart_2350707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350707 prefixEnd_2350707 := by exact prefixLift 2350707
  have htrace : WordTrace (prefixWord ++ tailWord_2350707) baseStart_2350707 baseEnd_2350707 := by
    simpa [prefixWord, tailWord_2350707, baseEnd_2350707] using wordTrace_append hprefix tailTrace_2350707
  have hstable : (prefixWord ++ tailWord_2350707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350707).length < 2 ^ (prefixWord ++ tailWord_2350707).sum := by decide
  have hdescent : baseEnd_2350707 < baseStart_2350707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350744 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 7]
def baseStart_2350744 : Nat := 118140960795 + 2350744 * 2 ^ 59
def prefixEnd_2350744 : Nat := 4983230072969 + 3 ^ 40 * 2350744 * 2
def baseEnd_2350744 : Nat := 134117951963650659665459

theorem tailTrace_2350744 : CollatzResearch.WordTrace tailWord_2350744 prefixEnd_2350744 134117951963650659665459 := by
  unfold tailWord_2350744
  simp only [CollatzResearch.WordTrace]
  refine ⟨42869338697831718978621643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57159118263775625304828857 42869338697831718978621643)
  ·
    refine ⟨64304008046747578467932465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42869338697831718978621643 64304008046747578467932465)
    ·
      refine ⟨48228006035060683850949349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64304008046747578467932465 48228006035060683850949349)
      ·
        refine ⟨9042751131573878222053003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48228006035060683850949349 9042751131573878222053003)
        ·
          refine ⟨13564126697360817333079505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9042751131573878222053003 13564126697360817333079505)
          ·
            refine ⟨10173095023020612999809629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13564126697360817333079505 10173095023020612999809629)
            ·
              refine ⟨3814910633632729874928611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10173095023020612999809629 3814910633632729874928611)
              ·
                refine ⟨5722365950449094812392917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814910633632729874928611 5722365950449094812392917)
                ·
                  refine ⟨134117951963650659665459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5722365950449094812392917 134117951963650659665459)
                  ·
                    rfl

theorem cell23_2350744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 7].length) (baseStart_2350744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350744 prefixEnd_2350744 := by exact prefixLift 2350744
  have htrace : WordTrace (prefixWord ++ tailWord_2350744) baseStart_2350744 baseEnd_2350744 := by
    simpa [prefixWord, tailWord_2350744, baseEnd_2350744] using wordTrace_append hprefix tailTrace_2350744
  have hstable : (prefixWord ++ tailWord_2350744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350744).length < 2 ^ (prefixWord ++ tailWord_2350744).sum := by decide
  have hdescent : baseEnd_2350744 < baseStart_2350744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350757 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_2350757 : Nat := 118140960795 + 2350757 * 2 ^ 59
def prefixEnd_2350757 : Nat := 4983230072969 + 3 ^ 40 * 2350757 * 2
def baseEnd_2350757 : Nat := 402356080973788128708857

theorem tailTrace_2350757 : CollatzResearch.WordTrace tailWord_2350757 prefixEnd_2350757 402356080973788128708857 := by
  unfold tailWord_2350757
  simp only [CollatzResearch.WordTrace]
  refine ⟨85739151544616341177466525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57159434363077560784977683 85739151544616341177466525)
  ·
    refine ⟨32152181829231127941549947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85739151544616341177466525 32152181829231127941549947)
    ·
      refine ⟨48228272743846691912324921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32152181829231127941549947 48228272743846691912324921)
      ·
        refine ⟨36171204557885018934243691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48228272743846691912324921 36171204557885018934243691)
        ·
          refine ⟨54256806836827528401365537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36171204557885018934243691 54256806836827528401365537)
          ·
            refine ⟨40692605127620646301024153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54256806836827528401365537 40692605127620646301024153)
            ·
              refine ⟨30519453845715484725768115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40692605127620646301024153 30519453845715484725768115)
              ·
                refine ⟨45779180768573227088652173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30519453845715484725768115 45779180768573227088652173)
                ·
                  refine ⟨17167192788214960158244565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45779180768573227088652173 17167192788214960158244565)
                  ·
                    refine ⟨402356080973788128708857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17167192788214960158244565 402356080973788128708857)
                    ·
                      rfl

theorem cell23_2350757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_2350757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350757 prefixEnd_2350757 := by exact prefixLift 2350757
  have htrace : WordTrace (prefixWord ++ tailWord_2350757) baseStart_2350757 baseEnd_2350757 := by
    simpa [prefixWord, tailWord_2350757, baseEnd_2350757] using wordTrace_append hprefix tailTrace_2350757
  have hstable : (prefixWord ++ tailWord_2350757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350757).length < 2 ^ (prefixWord ++ tailWord_2350757).sum := by decide
  have hdescent : baseEnd_2350757 < baseStart_2350757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350767 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_2350767 : Nat := 118140960795 + 2350767 * 2 ^ 59
def prefixEnd_2350767 : Nat := 4983230072969 + 3 ^ 40 * 2350767 * 2
def baseEnd_2350767 : Nat := 1207073377727909347001525

theorem tailTrace_2350767 : CollatzResearch.WordTrace tailWord_2350767 prefixEnd_2350767 1207073377727909347001525 := by
  unfold tailWord_2350767
  simp only [CollatzResearch.WordTrace]
  refine ⟨85739516274580112885330555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57159677516386741923553703 85739516274580112885330555)
  ·
    refine ⟨128609274411870169327995833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85739516274580112885330555 128609274411870169327995833)
    ·
      refine ⟨96456955808902626995996875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128609274411870169327995833 96456955808902626995996875)
      ·
        refine ⟨144685433713353940493995313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96456955808902626995996875 144685433713353940493995313)
        ·
          refine ⟨108514075285015455370496485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144685433713353940493995313 108514075285015455370496485)
          ·
            refine ⟨20346389115940397881968091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108514075285015455370496485 20346389115940397881968091)
            ·
              refine ⟨30519583673910596822952137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20346389115940397881968091 30519583673910596822952137)
              ·
                refine ⟨22889687755432947617214103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30519583673910596822952137 22889687755432947617214103)
                ·
                  refine ⟨34334531633149421425821155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22889687755432947617214103 34334531633149421425821155)
                  ·
                    refine ⟨51501797449724132138731733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34334531633149421425821155 51501797449724132138731733)
                    ·
                      refine ⟨1207073377727909347001525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51501797449724132138731733 1207073377727909347001525)
                      ·
                        rfl

theorem cell23_2350767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_2350767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350767 prefixEnd_2350767 := by exact prefixLift 2350767
  have htrace : WordTrace (prefixWord ++ tailWord_2350767) baseStart_2350767 baseEnd_2350767 := by
    simpa [prefixWord, tailWord_2350767, baseEnd_2350767] using wordTrace_append hprefix tailTrace_2350767
  have hstable : (prefixWord ++ tailWord_2350767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350767).length < 2 ^ (prefixWord ++ tailWord_2350767).sum := by decide
  have hdescent : baseEnd_2350767 < baseStart_2350767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350821 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_2350821 : Nat := 118140960795 + 2350821 * 2 ^ 59
def prefixEnd_2350821 : Nat := 4983230072969 + 3 ^ 40 * 2350821 * 2
def baseEnd_2350821 : Nat := 402367035227750711908759

theorem tailTrace_2350821 : CollatzResearch.WordTrace tailWord_2350821 prefixEnd_2350821 402367035227750711908759 := by
  unfold tailWord_2350821
  simp only [CollatzResearch.WordTrace]
  refine ⟨85741485816384480107796317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57160990544256320071864211 85741485816384480107796317)
  ·
    refine ⟨32153057181144180040423619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85741485816384480107796317 32153057181144180040423619)
    ·
      refine ⟨48229585771716270060635429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32153057181144180040423619 48229585771716270060635429)
      ·
        refine ⟨9043047332196800636369143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48229585771716270060635429 9043047332196800636369143)
        ·
          refine ⟨13564570998295200954553715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9043047332196800636369143 13564570998295200954553715)
          ·
            refine ⟨20346856497442801431830573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13564570998295200954553715 20346856497442801431830573)
            ·
              refine ⟨7630071186541050536936465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20346856497442801431830573 7630071186541050536936465)
              ·
                refine ⟨5722553389905787902702349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7630071186541050536936465 5722553389905787902702349)
                ·
                  refine ⟨2145957521214670463513381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5722553389905787902702349 2145957521214670463513381)
                  ·
                    refine ⟨402367035227750711908759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2145957521214670463513381 402367035227750711908759)
                    ·
                      rfl

theorem cell23_2350821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_2350821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350821 prefixEnd_2350821 := by exact prefixLift 2350821
  have htrace : WordTrace (prefixWord ++ tailWord_2350821) baseStart_2350821 baseEnd_2350821 := by
    simpa [prefixWord, tailWord_2350821, baseEnd_2350821] using wordTrace_append hprefix tailTrace_2350821
  have hstable : (prefixWord ++ tailWord_2350821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350821).length < 2 ^ (prefixWord ++ tailWord_2350821).sum := by decide
  have hdescent : baseEnd_2350821 < baseStart_2350821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350834 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 8]
def baseStart_2350834 : Nat := 118140960795 + 2350834 * 2 ^ 59
def prefixEnd_2350834 : Nat := 4983230072969 + 3 ^ 40 * 2350834 * 2
def baseEnd_2350834 : Nat := 134123086770195620540413

theorem tailTrace_2350834 : CollatzResearch.WordTrace tailWord_2350834 prefixEnd_2350834 134123086770195620540413 := by
  unfold tailWord_2350834
  simp only [CollatzResearch.WordTrace]
  refine ⟨21435489991334345832004889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57161306643558255552013037 21435489991334345832004889)
  ·
    refine ⟨16076617493500759374003667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21435489991334345832004889 16076617493500759374003667)
    ·
      refine ⟨24114926240251139061005501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16076617493500759374003667 24114926240251139061005501)
      ·
        refine ⟨9043097340094177147877063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24114926240251139061005501 9043097340094177147877063)
        ·
          refine ⟨13564646010141265721815595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9043097340094177147877063 13564646010141265721815595)
          ·
            refine ⟨20346969015211898582723393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13564646010141265721815595 20346969015211898582723393)
            ·
              refine ⟨15260226761408923937042545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20346969015211898582723393 15260226761408923937042545)
              ·
                refine ⟨11445170071056692952781909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15260226761408923937042545 11445170071056692952781909)
                ·
                  refine ⟨134123086770195620540413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11445170071056692952781909 134123086770195620540413)
                  ·
                    rfl

theorem cell23_2350834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_2350834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350834 prefixEnd_2350834 := by exact prefixLift 2350834
  have htrace : WordTrace (prefixWord ++ tailWord_2350834) baseStart_2350834 baseEnd_2350834 := by
    simpa [prefixWord, tailWord_2350834, baseEnd_2350834] using wordTrace_append hprefix tailTrace_2350834
  have hstable : (prefixWord ++ tailWord_2350834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350834).length < 2 ^ (prefixWord ++ tailWord_2350834).sum := by decide
  have hdescent : baseEnd_2350834 < baseStart_2350834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350881 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 1, 5]
def baseStart_2350881 : Nat := 118140960795 + 2350881 * 2 ^ 59
def prefixEnd_2350881 : Nat := 4983230072969 + 3 ^ 40 * 2350881 * 2
def baseEnd_2350881 : Nat := 402377304840840633658667

theorem tailTrace_2350881 : CollatzResearch.WordTrace tailWord_2350881 prefixEnd_2350881 402377304840840633658667 := by
  unfold tailWord_2350881
  simp only [CollatzResearch.WordTrace]
  refine ⟨85743674196167110354980497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57162449464111406903320331 85743674196167110354980497)
  ·
    refine ⟨64307755647125332766235373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85743674196167110354980497 64307755647125332766235373)
    ·
      refine ⟨24115408367671999787338265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64307755647125332766235373 24115408367671999787338265)
      ·
        refine ⟨18086556275753999840503699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24115408367671999787338265 18086556275753999840503699)
        ·
          refine ⟨27129834413630999760755549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18086556275753999840503699 27129834413630999760755549)
          ·
            refine ⟨10173687905111624910283331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27129834413630999760755549 10173687905111624910283331)
            ·
              refine ⟨15260531857667437365424997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10173687905111624910283331 15260531857667437365424997)
              ·
                refine ⟨2861349723312644506017187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15260531857667437365424997 2861349723312644506017187)
                ·
                  refine ⟨4292024584968966759025781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861349723312644506017187 4292024584968966759025781)
                  ·
                    refine ⟨402377304840840633658667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4292024584968966759025781 402377304840840633658667)
                    ·
                      rfl

theorem cell23_2350881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_2350881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350881 prefixEnd_2350881 := by exact prefixLift 2350881
  have htrace : WordTrace (prefixWord ++ tailWord_2350881) baseStart_2350881 baseEnd_2350881 := by
    simpa [prefixWord, tailWord_2350881, baseEnd_2350881] using wordTrace_append hprefix tailTrace_2350881
  have hstable : (prefixWord ++ tailWord_2350881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350881).length < 2 ^ (prefixWord ++ tailWord_2350881).sum := by decide
  have hdescent : baseEnd_2350881 < baseStart_2350881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350888 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_2350888 : Nat := 118140960795 + 2350888 * 2 ^ 59
def prefixEnd_2350888 : Nat := 4983230072969 + 3 ^ 40 * 2350888 * 2
def baseEnd_2350888 : Nat := 1207135508887103373588469

theorem tailTrace_2350888 : CollatzResearch.WordTrace tailWord_2350888 prefixEnd_2350888 1207135508887103373588469 := by
  unfold tailWord_2350888
  simp only [CollatzResearch.WordTrace]
  refine ⟨42871964753570875275242659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57162619671427833700323545 42871964753570875275242659)
  ·
    refine ⟨64307947130356312912863989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42871964753570875275242659 64307947130356312912863989)
    ·
      refine ⟨6028870043470904335580999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64307947130356312912863989 6028870043470904335580999)
      ·
        refine ⟨9043305065206356503371499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6028870043470904335580999 9043305065206356503371499)
        ·
          refine ⟨13564957597809534755057249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9043305065206356503371499 13564957597809534755057249)
          ·
            refine ⟨10173718198357151066292937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13564957597809534755057249 10173718198357151066292937)
            ·
              refine ⟨7630288648767863299719703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10173718198357151066292937 7630288648767863299719703)
              ·
                refine ⟨11445432973151794949579555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7630288648767863299719703 11445432973151794949579555)
                ·
                  refine ⟨17168149459727692424369333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11445432973151794949579555 17168149459727692424369333)
                  ·
                    refine ⟨1609514011849471164784625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17168149459727692424369333 1609514011849471164784625)
                    ·
                      refine ⟨1207135508887103373588469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609514011849471164784625 1207135508887103373588469)
                      ·
                        rfl

theorem cell23_2350888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_2350888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350888 prefixEnd_2350888 := by exact prefixLift 2350888
  have htrace : WordTrace (prefixWord ++ tailWord_2350888) baseStart_2350888 baseEnd_2350888 := by
    simpa [prefixWord, tailWord_2350888, baseEnd_2350888] using wordTrace_append hprefix tailTrace_2350888
  have hstable : (prefixWord ++ tailWord_2350888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350888).length < 2 ^ (prefixWord ++ tailWord_2350888).sum := by decide
  have hdescent : baseEnd_2350888 < baseStart_2350888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350921 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 3, 2, 3]
def baseStart_2350921 : Nat := 118140960795 + 2350921 * 2 ^ 59
def prefixEnd_2350921 : Nat := 4983230072969 + 3 ^ 40 * 2350921 * 2
def baseEnd_2350921 : Nat := 1207152453748701744475817

theorem tailTrace_2350921 : CollatzResearch.WordTrace tailWord_2350921 prefixEnd_2350921 1207152453748701744475817 := by
  unfold tailWord_2350921
  simp only [CollatzResearch.WordTrace]
  refine ⟨85745133116022197186436617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57163422077348131457624411 85745133116022197186436617)
  ·
    refine ⟨64308849837016647889827463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85745133116022197186436617 64308849837016647889827463)
    ·
      refine ⟨96463274755524971834741195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64308849837016647889827463 96463274755524971834741195)
      ·
        refine ⟨144694912133287457752111793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96463274755524971834741195 144694912133287457752111793)
        ·
          refine ⟨108521184099965593314083845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144694912133287457752111793 108521184099965593314083845)
          ·
            refine ⟨20347722018743548746390721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108521184099965593314083845 20347722018743548746390721)
            ·
              refine ⟨15260791514057661559793041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20347722018743548746390721 15260791514057661559793041)
              ·
                refine ⟨11445593635543246169844781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15260791514057661559793041 11445593635543246169844781)
                ·
                  refine ⟨4292097613328717313691793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11445593635543246169844781 4292097613328717313691793)
                  ·
                    refine ⟨3219073209996537985268845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4292097613328717313691793 3219073209996537985268845)
                    ·
                      refine ⟨1207152453748701744475817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3219073209996537985268845 1207152453748701744475817)
                      ·
                        rfl

theorem cell23_2350921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2, 3].length) (baseStart_2350921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350921 prefixEnd_2350921 := by exact prefixLift 2350921
  have htrace : WordTrace (prefixWord ++ tailWord_2350921) baseStart_2350921 baseEnd_2350921 := by
    simpa [prefixWord, tailWord_2350921, baseEnd_2350921] using wordTrace_append hprefix tailTrace_2350921
  have hstable : (prefixWord ++ tailWord_2350921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350921).length < 2 ^ (prefixWord ++ tailWord_2350921).sum := by decide
  have hdescent : baseEnd_2350921 < baseStart_2350921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350935 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 4]
def baseStart_2350935 : Nat := 118140960795 + 2350935 * 2 ^ 59
def prefixEnd_2350935 : Nat := 4983230072969 + 3 ^ 40 * 2350935 * 2
def baseEnd_2350935 : Nat := 1207159642477864689700753

theorem tailTrace_2350935 : CollatzResearch.WordTrace tailWord_2350935 prefixEnd_2350935 1207159642477864689700753 := by
  unfold tailWord_2350935
  simp only [CollatzResearch.WordTrace]
  refine ⟨85745643737971477577446259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57163762491980985051630839 85745643737971477577446259)
  ·
    refine ⟨128618465606957216366169389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85745643737971477577446259 128618465606957216366169389)
    ·
      refine ⟨48231924602608956137313521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128618465606957216366169389 48231924602608956137313521)
      ·
        refine ⟨36173943451956717102985141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48231924602608956137313521 36173943451956717102985141)
        ·
          refine ⟨3391307198620942228404857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36173943451956717102985141 3391307198620942228404857)
          ·
            refine ⟨2543480398965706671303643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3391307198620942228404857 2543480398965706671303643)
            ·
              refine ⟨3815220598448560006955465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543480398965706671303643 3815220598448560006955465)
              ·
                refine ⟨2861415448836420005216599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3815220598448560006955465 2861415448836420005216599)
                ·
                  refine ⟨4292123173254630007824899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861415448836420005216599 4292123173254630007824899)
                  ·
                    refine ⟨6438184759881945011737349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4292123173254630007824899 6438184759881945011737349)
                    ·
                      refine ⟨1207159642477864689700753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6438184759881945011737349 1207159642477864689700753)
                      ·
                        rfl

theorem cell23_2350935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_2350935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350935 prefixEnd_2350935 := by exact prefixLift 2350935
  have htrace : WordTrace (prefixWord ++ tailWord_2350935) baseStart_2350935 baseEnd_2350935 := by
    simpa [prefixWord, tailWord_2350935, baseEnd_2350935] using wordTrace_append hprefix tailTrace_2350935
  have hstable : (prefixWord ++ tailWord_2350935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350935).length < 2 ^ (prefixWord ++ tailWord_2350935).sum := by decide
  have hdescent : baseEnd_2350935 < baseStart_2350935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350948 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_2350948 : Nat := 118140960795 + 2350948 * 2 ^ 59
def prefixEnd_2350948 : Nat := 4983230072969 + 3 ^ 40 * 2350948 * 2
def baseEnd_2350948 : Nat := 1207166317726373138838193

theorem tailTrace_2350948 : CollatzResearch.WordTrace tailWord_2350948 prefixEnd_2350948 1207166317726373138838193 := by
  unfold tailWord_2350948
  simp only [CollatzResearch.WordTrace]
  refine ⟨42873058943462190398834749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57164078591282920531779665 42873058943462190398834749)
  ·
    refine ⟨16077397103798321399563031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42873058943462190398834749 16077397103798321399563031)
    ·
      refine ⟨24116095655697482099344547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16077397103798321399563031 24116095655697482099344547)
      ·
        refine ⟨36174143483546223149016821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24116095655697482099344547 36174143483546223149016821)
        ·
          refine ⟨3391325951582458420220327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36174143483546223149016821 3391325951582458420220327)
          ·
            refine ⟨5086988927373687630330491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3391325951582458420220327 5086988927373687630330491)
            ·
              refine ⟨7630483391060531445495737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086988927373687630330491 7630483391060531445495737)
              ·
                refine ⟨5722862543295398584121803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7630483391060531445495737 5722862543295398584121803)
                ·
                  refine ⟨8584293814943097876182705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5722862543295398584121803 8584293814943097876182705)
                  ·
                    refine ⟨6438220361207323407137029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8584293814943097876182705 6438220361207323407137029)
                    ·
                      refine ⟨1207166317726373138838193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6438220361207323407137029 1207166317726373138838193)
                      ·
                        rfl

theorem cell23_2350948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_2350948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350948 prefixEnd_2350948 := by exact prefixLift 2350948
  have htrace : WordTrace (prefixWord ++ tailWord_2350948) baseStart_2350948 baseEnd_2350948 := by
    simpa [prefixWord, tailWord_2350948, baseEnd_2350948] using wordTrace_append hprefix tailTrace_2350948
  have hstable : (prefixWord ++ tailWord_2350948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350948).length < 2 ^ (prefixWord ++ tailWord_2350948).sum := by decide
  have hdescent : baseEnd_2350948 < baseStart_2350948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350952 : List Nat := [2, 1, 4, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_2350952 : Nat := 118140960795 + 2350952 * 2 ^ 59
def prefixEnd_2350952 : Nat := 4983230072969 + 3 ^ 40 * 2350952 * 2
def baseEnd_2350952 : Nat := 1207168371648991123188175

theorem tailTrace_2350952 : CollatzResearch.WordTrace tailWord_2350952 prefixEnd_2350952 1207168371648991123188175 := by
  unfold tailWord_2350952
  simp only [CollatzResearch.WordTrace]
  refine ⟨42873131889454944740407555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57164175852606592987210073 42873131889454944740407555)
  ·
    refine ⟨64309697834182417110611333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42873131889454944740407555 64309697834182417110611333)
    ·
      refine ⟨12058068343909203208239625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64309697834182417110611333 12058068343909203208239625)
      ·
        refine ⟨9043551257931902406179719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12058068343909203208239625 9043551257931902406179719)
        ·
          refine ⟨13565326886897853609269579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9043551257931902406179719 13565326886897853609269579)
          ·
            refine ⟨20347990330346780413904369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13565326886897853609269579 20347990330346780413904369)
            ·
              refine ⟨15260992747760085310428277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20347990330346780413904369 15260992747760085310428277)
              ·
                refine ⟨1430718070102507997852651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15260992747760085310428277 1430718070102507997852651)
                ·
                  refine ⟨2146077105153761996778977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430718070102507997852651 2146077105153761996778977)
                  ·
                    refine ⟨1609557828865321497584233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2146077105153761996778977 1609557828865321497584233)
                    ·
                      refine ⟨1207168371648991123188175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609557828865321497584233 1207168371648991123188175)
                      ·
                        rfl

theorem cell23_2350952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_2350952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2350952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2350952 prefixEnd_2350952 := by exact prefixLift 2350952
  have htrace : WordTrace (prefixWord ++ tailWord_2350952) baseStart_2350952 baseEnd_2350952 := by
    simpa [prefixWord, tailWord_2350952, baseEnd_2350952] using wordTrace_append hprefix tailTrace_2350952
  have hstable : (prefixWord ++ tailWord_2350952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350952).length < 2 ^ (prefixWord ++ tailWord_2350952).sum := by decide
  have hdescent : baseEnd_2350952 < baseStart_2350952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351006 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2351006 : Nat := 118140960795 + 2351006 * 2 ^ 59
def prefixEnd_2351006 : Nat := 4983230072969 + 3 ^ 40 * 2351006 * 2
def baseEnd_2351006 : Nat := 1207196099604333911912927

theorem tailTrace_2351006 : CollatzResearch.WordTrace tailWord_2351006 prefixEnd_2351006 1207196099604333911912927 := by
  unfold tailWord_2351006
  simp only [CollatzResearch.WordTrace]
  refine ⟨10718529165089282087910109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57165488880476171135520581 10718529165089282087910109)
  ·
    refine ⟨4019448436908480782966291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10718529165089282087910109 4019448436908480782966291)
    ·
      refine ⟨6029172655362721174449437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4019448436908480782966291 6029172655362721174449437)
      ·
        refine ⟨2260939745761020440418539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6029172655362721174449437 2260939745761020440418539)
        ·
          refine ⟨3391409618641530660627809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260939745761020440418539 3391409618641530660627809)
          ·
            refine ⟨2543557213981147995470857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3391409618641530660627809 2543557213981147995470857)
            ·
              refine ⟨1907667910485860996603143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2543557213981147995470857 1907667910485860996603143)
              ·
                refine ⟨2861501865728791494904715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907667910485860996603143 2861501865728791494904715)
                ·
                  refine ⟨4292252798593187242357073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861501865728791494904715 4292252798593187242357073)
                  ·
                    refine ⟨3219189598944890431767805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4292252798593187242357073 3219189598944890431767805)
                    ·
                      refine ⟨1207196099604333911912927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3219189598944890431767805 1207196099604333911912927)
                      ·
                        rfl

theorem cell23_2351006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2351006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351006 prefixEnd_2351006 := by exact prefixLift 2351006
  have htrace : WordTrace (prefixWord ++ tailWord_2351006) baseStart_2351006 baseEnd_2351006 := by
    simpa [prefixWord, tailWord_2351006, baseEnd_2351006] using wordTrace_append hprefix tailTrace_2351006
  have hstable : (prefixWord ++ tailWord_2351006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351006).length < 2 ^ (prefixWord ++ tailWord_2351006).sum := by decide
  have hdescent : baseEnd_2351006 < baseStart_2351006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351012 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 1, 3, 2]
def baseStart_2351012 : Nat := 118140960795 + 2351012 * 2 ^ 59
def prefixEnd_2351012 : Nat := 4983230072969 + 3 ^ 40 * 2351012 * 2
def baseEnd_2351012 : Nat := 1207199180488260888437899

theorem tailTrace_2351012 : CollatzResearch.WordTrace tailWord_2351012 prefixEnd_2351012 1207199180488260888437899 := by
  unfold tailWord_2351012
  simp only [CollatzResearch.WordTrace]
  refine ⟨42874226079346259863999645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57165634772461679818666193 42874226079346259863999645)
  ·
    refine ⟨16077834779754847448999867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42874226079346259863999645 16077834779754847448999867)
    ·
      refine ⟨24116752169632271173499801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16077834779754847448999867 24116752169632271173499801)
      ·
        refine ⟨18087564127224203380124851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24116752169632271173499801 18087564127224203380124851)
        ·
          refine ⟨27131346190836305070187277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18087564127224203380124851 27131346190836305070187277)
          ·
            refine ⟨10174254821563614401320229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27131346190836305070187277 10174254821563614401320229)
            ·
              refine ⟨1907672779043177700247543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10174254821563614401320229 1907672779043177700247543)
              ·
                refine ⟨2861509168564766550371315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907672779043177700247543 2861509168564766550371315)
                ·
                  refine ⟨4292263752847149825556973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861509168564766550371315 4292263752847149825556973)
                  ·
                    refine ⟨1609598907317681184583865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4292263752847149825556973 1609598907317681184583865)
                    ·
                      refine ⟨1207199180488260888437899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609598907317681184583865 1207199180488260888437899)
                      ·
                        rfl

theorem cell23_2351012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_2351012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351012 prefixEnd_2351012 := by exact prefixLift 2351012
  have htrace : WordTrace (prefixWord ++ tailWord_2351012) baseStart_2351012 baseEnd_2351012 := by
    simpa [prefixWord, tailWord_2351012, baseEnd_2351012] using wordTrace_append hprefix tailTrace_2351012
  have hstable : (prefixWord ++ tailWord_2351012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351012).length < 2 ^ (prefixWord ++ tailWord_2351012).sum := by decide
  have hdescent : baseEnd_2351012 < baseStart_2351012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351038 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_2351038 : Nat := 118140960795 + 2351038 * 2 ^ 59
def prefixEnd_2351038 : Nat := 4983230072969 + 3 ^ 40 * 2351038 * 2
def baseEnd_2351038 : Nat := 1207212530985277786712779

theorem tailTrace_2351038 : CollatzResearch.WordTrace tailWord_2351038 prefixEnd_2351038 1207212530985277786712779 := by
  unfold tailWord_2351038
  simp only [CollatzResearch.WordTrace]
  refine ⟨10718675057074790771055721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57166266971065550778963845 10718675057074790771055721)
  ·
    refine ⟨8039006292806093078291791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10718675057074790771055721 8039006292806093078291791)
    ·
      refine ⟨12058509439209139617437687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8039006292806093078291791 12058509439209139617437687)
      ·
        refine ⟨18087764158813709426156531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12058509439209139617437687 18087764158813709426156531)
        ·
          refine ⟨27131646238220564139234797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18087764158813709426156531 27131646238220564139234797)
          ·
            refine ⟨10174367339332711552213049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27131646238220564139234797 10174367339332711552213049)
            ·
              refine ⟨7630775504499533664159787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10174367339332711552213049 7630775504499533664159787)
              ·
                refine ⟨11446163256749300496239681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7630775504499533664159787 11446163256749300496239681)
                ·
                  refine ⟨8584622442561975372179761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11446163256749300496239681 8584622442561975372179761)
                  ·
                    refine ⟨6438466831921481529134821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8584622442561975372179761 6438466831921481529134821)
                    ·
                      refine ⟨1207212530985277786712779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6438466831921481529134821 1207212530985277786712779)
                      ·
                        rfl

theorem cell23_2351038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_2351038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351038 prefixEnd_2351038 := by exact prefixLift 2351038
  have htrace : WordTrace (prefixWord ++ tailWord_2351038) baseStart_2351038 baseEnd_2351038 := by
    simpa [prefixWord, tailWord_2351038, baseEnd_2351038] using wordTrace_append hprefix tailTrace_2351038
  have hstable : (prefixWord ++ tailWord_2351038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351038).length < 2 ^ (prefixWord ++ tailWord_2351038).sum := by decide
  have hdescent : baseEnd_2351038 < baseStart_2351038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351168 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 3, 5]
def baseStart_2351168 : Nat := 118140960795 + 2351168 * 2 ^ 59
def prefixEnd_2351168 : Nat := 4983230072969 + 3 ^ 40 * 2351168 * 2
def baseEnd_2351168 : Nat := 402426427823454092695727

theorem tailTrace_2351168 : CollatzResearch.WordTrace tailWord_2351168 prefixEnd_2351168 402426427823454092695727 := by
  unfold tailWord_2351168
  simp only [CollatzResearch.WordTrace]
  refine ⟨42877070973063679185339079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57169427964084905580452105 42877070973063679185339079)
  ·
    refine ⟨64315606459595518778008619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42877070973063679185339079 64315606459595518778008619)
    ·
      refine ⟨96473409689393278167012929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64315606459595518778008619 96473409689393278167012929)
      ·
        refine ⟨72355057267044958625259697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96473409689393278167012929 72355057267044958625259697)
        ·
          refine ⟨54266292950283718968944773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72355057267044958625259697 54266292950283718968944773)
          ·
            refine ⟨10174929928178197306677145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54266292950283718968944773 10174929928178197306677145)
            ·
              refine ⟨7631197446133647980007859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10174929928178197306677145 7631197446133647980007859)
              ·
                refine ⟨11446796169200471970011789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7631197446133647980007859 11446796169200471970011789)
                ·
                  refine ⟨4292548563450176988754421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11446796169200471970011789 4292548563450176988754421)
                  ·
                    refine ⟨402426427823454092695727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4292548563450176988754421 402426427823454092695727)
                    ·
                      rfl

theorem cell23_2351168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_2351168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351168 prefixEnd_2351168 := by exact prefixLift 2351168
  have htrace : WordTrace (prefixWord ++ tailWord_2351168) baseStart_2351168 baseEnd_2351168 := by
    simpa [prefixWord, tailWord_2351168, baseEnd_2351168] using wordTrace_append hprefix tailTrace_2351168
  have hstable : (prefixWord ++ tailWord_2351168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351168).length < 2 ^ (prefixWord ++ tailWord_2351168).sum := by decide
  have hdescent : baseEnd_2351168 < baseStart_2351168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351175 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 1, 5, 2]
def baseStart_2351175 : Nat := 118140960795 + 2351175 * 2 ^ 59
def prefixEnd_2351175 : Nat := 4983230072969 + 3 ^ 40 * 2351175 * 2
def baseEnd_2351175 : Nat := 1207282877834943750699649

theorem tailTrace_2351175 : CollatzResearch.WordTrace tailWord_2351175 prefixEnd_2351175 1207282877834943750699649 := by
  unfold tailWord_2351175
  simp only [CollatzResearch.WordTrace]
  refine ⟨85754397257101998566182979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57169598171401332377455319 85754397257101998566182979)
  ·
    refine ⟨128631595885652997849274469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85754397257101998566182979 128631595885652997849274469)
    ·
      refine ⟨24118424228559937096738963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128631595885652997849274469 24118424228559937096738963)
      ·
        refine ⟨36177636342839905645108445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24118424228559937096738963 36177636342839905645108445)
        ·
          refine ⟨13566613628564964616915667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36177636342839905645108445 13566613628564964616915667)
          ·
            refine ⟨20349920442847446925373501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13566613628564964616915667 20349920442847446925373501)
            ·
              refine ⟨7631220166067792597015063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20349920442847446925373501 7631220166067792597015063)
              ·
                refine ⟨11446830249101688895522595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7631220166067792597015063 11446830249101688895522595)
                ·
                  refine ⟨17170245373652533343283893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11446830249101688895522595 17170245373652533343283893)
                  ·
                    refine ⟨1609710503779925000932865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17170245373652533343283893 1609710503779925000932865)
                    ·
                      refine ⟨1207282877834943750699649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609710503779925000932865 1207282877834943750699649)
                      ·
                        rfl

theorem cell23_2351175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_2351175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351175 prefixEnd_2351175 := by exact prefixLift 2351175
  have htrace : WordTrace (prefixWord ++ tailWord_2351175) baseStart_2351175 baseEnd_2351175 := by
    simpa [prefixWord, tailWord_2351175, baseEnd_2351175] using wordTrace_append hprefix tailTrace_2351175
  have hstable : (prefixWord ++ tailWord_2351175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351175).length < 2 ^ (prefixWord ++ tailWord_2351175).sum := by decide
  have hdescent : baseEnd_2351175 < baseStart_2351175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351215 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 1, 6]
def baseStart_2351215 : Nat := 118140960795 + 2351215 * 2 ^ 59
def prefixEnd_2351215 : Nat := 4983230072969 + 3 ^ 40 * 2351215 * 2
def baseEnd_2351215 : Nat := 402434472353707864733155

theorem tailTrace_2351215 : CollatzResearch.WordTrace tailWord_2351215 prefixEnd_2351215 402434472353707864733155 := by
  unfold tailWord_2351215
  simp only [CollatzResearch.WordTrace]
  refine ⟨85755856176957085397639099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57170570784638056931759399 85755856176957085397639099)
  ·
    refine ⟨128633784265435628096458649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85755856176957085397639099 128633784265435628096458649)
    ·
      refine ⟨96475338199076721072343987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128633784265435628096458649 96475338199076721072343987)
      ·
        refine ⟨144713007298615081608515981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96475338199076721072343987 144713007298615081608515981)
        ·
          refine ⟨54267377736980655603193493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144713007298615081608515981 54267377736980655603193493)
          ·
            refine ⟨2543783331420968231399695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54267377736980655603193493 2543783331420968231399695)
            ·
              refine ⟨3815674997131452347099543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543783331420968231399695 3815674997131452347099543)
              ·
                refine ⟨5723512495697178520649315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3815674997131452347099543 5723512495697178520649315)
                ·
                  refine ⟨8585268743545767780973973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5723512495697178520649315 8585268743545767780973973)
                  ·
                    refine ⟨402434472353707864733155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8585268743545767780973973 402434472353707864733155)
                    ·
                      rfl

theorem cell23_2351215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 6].length) (baseStart_2351215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351215 prefixEnd_2351215 := by exact prefixLift 2351215
  have htrace : WordTrace (prefixWord ++ tailWord_2351215) baseStart_2351215 baseEnd_2351215 := by
    simpa [prefixWord, tailWord_2351215, baseEnd_2351215] using wordTrace_append hprefix tailTrace_2351215
  have hstable : (prefixWord ++ tailWord_2351215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351215).length < 2 ^ (prefixWord ++ tailWord_2351215).sum := by decide
  have hdescent : baseEnd_2351215 < baseStart_2351215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351222 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2351222 : Nat := 118140960795 + 2351222 * 2 ^ 59
def prefixEnd_2351222 : Nat := 4983230072969 + 3 ^ 40 * 2351222 * 2
def baseEnd_2351222 : Nat := 1207307011425705066811933

theorem tailTrace_2351222 : CollatzResearch.WordTrace tailWord_2351222 prefixEnd_2351222 1207307011425705066811933 := by
  unfold tailWord_2351222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5359756967995732849571495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57170740991954483728762613 5359756967995732849571495)
  ·
    refine ⟨8039635451993599274357243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5359756967995732849571495 8039635451993599274357243)
    ·
      refine ⟨12059453177990398911535865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8039635451993599274357243 12059453177990398911535865)
      ·
        refine ⟨9044589883492799183651899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12059453177990398911535865 9044589883492799183651899)
        ·
          refine ⟨13566884825239198775477849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9044589883492799183651899 13566884825239198775477849)
          ·
            refine ⟨10175163618929399081608387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13566884825239198775477849 10175163618929399081608387)
            ·
              refine ⟨15262745428394098622412581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10175163618929399081608387 15262745428394098622412581)
              ·
                refine ⟨2861764767823893491702359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15262745428394098622412581 2861764767823893491702359)
                ·
                  refine ⟨4292647151735840237553539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861764767823893491702359 4292647151735840237553539)
                  ·
                    refine ⟨6438970727603760356330309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4292647151735840237553539 6438970727603760356330309)
                    ·
                      refine ⟨1207307011425705066811933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6438970727603760356330309 1207307011425705066811933)
                      ·
                        rfl

theorem cell23_2351222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2351222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351222 prefixEnd_2351222 := by exact prefixLift 2351222
  have htrace : WordTrace (prefixWord ++ tailWord_2351222) baseStart_2351222 baseEnd_2351222 := by
    simpa [prefixWord, tailWord_2351222, baseEnd_2351222] using wordTrace_append hprefix tailTrace_2351222
  have hstable : (prefixWord ++ tailWord_2351222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351222).length < 2 ^ (prefixWord ++ tailWord_2351222).sum := by decide
  have hdescent : baseEnd_2351222 < baseStart_2351222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351228 : List Nat := [2, 2, 2, 1, 1, 5, 1, 9]
def baseStart_2351228 : Nat := 118140960795 + 2351228 * 2 ^ 59
def prefixEnd_2351228 : Nat := 4983230072969 + 3 ^ 40 * 2351228 * 2
def baseEnd_2351228 : Nat := 44715188604060446049515

theorem tailTrace_2351228 : CollatzResearch.WordTrace tailWord_2351228 prefixEnd_2351228 44715188604060446049515 := by
  unfold tailWord_2351228
  simp only [CollatzResearch.WordTrace]
  refine ⟨42878165162954994308931169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57170886883939992411908225 42878165162954994308931169)
  ·
    refine ⟨32158623872216245731698377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42878165162954994308931169 32158623872216245731698377)
    ·
      refine ⟨24118967904162184298773783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32158623872216245731698377 24118967904162184298773783)
      ·
        refine ⟨36178451856243276448160675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24118967904162184298773783 36178451856243276448160675)
        ·
          refine ⟨54267677784364914672241013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36178451856243276448160675 54267677784364914672241013)
          ·
            refine ⟨5087594792284210750522595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54267677784364914672241013 5087594792284210750522595)
            ·
              refine ⟨7631392188426316125783893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5087594792284210750522595 7631392188426316125783893)
              ·
                refine ⟨44715188604060446049515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7631392188426316125783893 44715188604060446049515)
                ·
                  rfl

theorem cell23_2351228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 9].length) (baseStart_2351228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351228 prefixEnd_2351228 := by exact prefixLift 2351228
  have htrace : WordTrace (prefixWord ++ tailWord_2351228) baseStart_2351228 baseEnd_2351228 := by
    simpa [prefixWord, tailWord_2351228, baseEnd_2351228] using wordTrace_append hprefix tailTrace_2351228
  have hstable : (prefixWord ++ tailWord_2351228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351228).length < 2 ^ (prefixWord ++ tailWord_2351228).sum := by decide
  have hdescent : baseEnd_2351228 < baseStart_2351228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351233 : List Nat := [1, 2, 4, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_2351233 : Nat := 118140960795 + 2351233 * 2 ^ 59
def prefixEnd_2351233 : Nat := 4983230072969 + 3 ^ 40 * 2351233 * 2
def baseEnd_2351233 : Nat := 1207312659712904523774383

theorem tailTrace_2351233 : CollatzResearch.WordTrace tailWord_2351233 prefixEnd_2351233 1207312659712904523774383 := by
  unfold tailWord_2351233
  simp only [CollatzResearch.WordTrace]
  refine ⟨85756512690891874471794353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57171008460594582981196235 85756512690891874471794353)
  ·
    refine ⟨64317384518168905853845765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85756512690891874471794353 64317384518168905853845765)
    ·
      refine ⟨12059509597156669847596081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64317384518168905853845765 12059509597156669847596081)
      ·
        refine ⟨9044632197867502385697061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12059509597156669847596081 9044632197867502385697061)
        ·
          refine ⟨1695868537100156697318199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9044632197867502385697061 1695868537100156697318199)
          ·
            refine ⟨2543802805650235045977299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695868537100156697318199 2543802805650235045977299)
            ·
              refine ⟨3815704208475352568965949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543802805650235045977299 3815704208475352568965949)
              ·
                refine ⟨1430889078178257213362231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3815704208475352568965949 1430889078178257213362231)
                ·
                  refine ⟨2146333617267385820043347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430889078178257213362231 2146333617267385820043347)
                  ·
                    refine ⟨3219500425901078730065021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2146333617267385820043347 3219500425901078730065021)
                    ·
                      refine ⟨1207312659712904523774383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3219500425901078730065021 1207312659712904523774383)
                      ·
                        rfl

theorem cell23_2351233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_2351233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351233 prefixEnd_2351233 := by exact prefixLift 2351233
  have htrace : WordTrace (prefixWord ++ tailWord_2351233) baseStart_2351233 baseEnd_2351233 := by
    simpa [prefixWord, tailWord_2351233, baseEnd_2351233] using wordTrace_append hprefix tailTrace_2351233
  have hstable : (prefixWord ++ tailWord_2351233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351233).length < 2 ^ (prefixWord ++ tailWord_2351233).sum := by decide
  have hdescent : baseEnd_2351233 < baseStart_2351233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351242 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_2351242 : Nat := 118140960795 + 2351242 * 2 ^ 59
def prefixEnd_2351242 : Nat := 4983230072969 + 3 ^ 40 * 2351242 * 2
def baseEnd_2351242 : Nat := 1207317281038794988561841

theorem tailTrace_2351242 : CollatzResearch.WordTrace tailWord_2351242 prefixEnd_2351242 1207317281038794988561841 := by
  unfold tailWord_2351242
  simp only [CollatzResearch.WordTrace]
  refine ⟨21439210236964817252217995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57171227298572846005914653 21439210236964817252217995)
  ·
    refine ⟨32158815355447225878326993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21439210236964817252217995 32158815355447225878326993)
    ·
      refine ⟨24119111516585419408745245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32158815355447225878326993 24119111516585419408745245)
      ·
        refine ⟨9044666818719532278279467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24119111516585419408745245 9044666818719532278279467)
        ·
          refine ⟨13567000228079298417419201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9044666818719532278279467 13567000228079298417419201)
          ·
            refine ⟨10175250171059473813064401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13567000228079298417419201 10175250171059473813064401)
            ·
              refine ⟨7631437628294605359798301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10175250171059473813064401 7631437628294605359798301)
              ·
                refine ⟨2861789110610477009924363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7631437628294605359798301 2861789110610477009924363)
                ·
                  refine ⟨4292683665915715514886545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861789110610477009924363 4292683665915715514886545)
                  ·
                    refine ⟨3219512749436786636164909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4292683665915715514886545 3219512749436786636164909)
                    ·
                      refine ⟨1207317281038794988561841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3219512749436786636164909 1207317281038794988561841)
                      ·
                        rfl

theorem cell23_2351242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_2351242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351242 prefixEnd_2351242 := by exact prefixLift 2351242
  have htrace : WordTrace (prefixWord ++ tailWord_2351242) baseStart_2351242 baseEnd_2351242 := by
    simpa [prefixWord, tailWord_2351242, baseEnd_2351242] using wordTrace_append hprefix tailTrace_2351242
  have hstable : (prefixWord ++ tailWord_2351242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351242).length < 2 ^ (prefixWord ++ tailWord_2351242).sum := by decide
  have hdescent : baseEnd_2351242 < baseStart_2351242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351256 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 3, 2, 2]
def baseStart_2351256 : Nat := 118140960795 + 2351256 * 2 ^ 59
def prefixEnd_2351256 : Nat := 4983230072969 + 3 ^ 40 * 2351256 * 2
def baseEnd_2351256 : Nat := 1207324469767957933786777

theorem tailTrace_2351256 : CollatzResearch.WordTrace tailWord_2351256 prefixEnd_2351256 1207324469767957933786777 := by
  unfold tailWord_2351256
  simp only [CollatzResearch.WordTrace]
  refine ⟨42878675784904274699940811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57171567713205699599921081 42878675784904274699940811)
  ·
    refine ⟨64318013677356412049911217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42878675784904274699940811 64318013677356412049911217)
    ·
      refine ⟨48238510258017309037433413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64318013677356412049911217 48238510258017309037433413)
      ·
        refine ⟨9044720673378245444518765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48238510258017309037433413 9044720673378245444518765)
        ·
          refine ⟨3391770252516842041694537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9044720673378245444518765 3391770252516842041694537)
          ·
            refine ⟨2543827689387631531270903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3391770252516842041694537 2543827689387631531270903)
            ·
              refine ⟨3815741534081447296906355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543827689387631531270903 3815741534081447296906355)
              ·
                refine ⟨5723612301122170945359533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3815741534081447296906355 5723612301122170945359533)
                ·
                  refine ⟨2146354612920814104509825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5723612301122170945359533 2146354612920814104509825)
                  ·
                    refine ⟨1609765959690610578382369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2146354612920814104509825 1609765959690610578382369)
                    ·
                      refine ⟨1207324469767957933786777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609765959690610578382369 1207324469767957933786777)
                      ·
                        rfl

theorem cell23_2351256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_2351256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351256 prefixEnd_2351256 := by exact prefixLift 2351256
  have htrace : WordTrace (prefixWord ++ tailWord_2351256) baseStart_2351256 baseEnd_2351256 := by
    simpa [prefixWord, tailWord_2351256, baseEnd_2351256] using wordTrace_append hprefix tailTrace_2351256
  have hstable : (prefixWord ++ tailWord_2351256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351256).length < 2 ^ (prefixWord ++ tailWord_2351256).sum := by decide
  have hdescent : baseEnd_2351256 < baseStart_2351256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351262 : List Nat := [4, 3, 1, 1, 3, 1, 2, 8]
def baseStart_2351262 : Nat := 118140960795 + 2351262 * 2 ^ 59
def prefixEnd_2351262 : Nat := 4983230072969 + 3 ^ 40 * 2351262 * 2
def baseEnd_2351262 : Nat := 44715835209329070752287

theorem tailTrace_2351262 : CollatzResearch.WordTrace tailWord_2351262 prefixEnd_2351262 44715835209329070752287 := by
  unfold tailWord_2351262
  simp only [CollatzResearch.WordTrace]
  refine ⟨10719696300973351553075005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57171713605191208283066693 10719696300973351553075005)
  ·
    refine ⟨4019886112865006832403127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10719696300973351553075005 4019886112865006832403127)
    ·
      refine ⟨6029829169297510248604691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4019886112865006832403127 6029829169297510248604691)
      ·
        refine ⟨9044743753946265372907037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6029829169297510248604691 9044743753946265372907037)
        ·
          refine ⟨3391778907729849514840139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9044743753946265372907037 3391778907729849514840139)
          ·
            refine ⟨5087668361594774272260209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3391778907729849514840139 5087668361594774272260209)
            ·
              refine ⟨3815751271196080704195157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5087668361594774272260209 3815751271196080704195157)
              ·
                refine ⟨44715835209329070752287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3815751271196080704195157 44715835209329070752287)
                ·
                  rfl

theorem cell23_2351262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_2351262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351262 prefixEnd_2351262 := by exact prefixLift 2351262
  have htrace : WordTrace (prefixWord ++ tailWord_2351262) baseStart_2351262 baseEnd_2351262 := by
    simpa [prefixWord, tailWord_2351262, baseEnd_2351262] using wordTrace_append hprefix tailTrace_2351262
  have hstable : (prefixWord ++ tailWord_2351262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351262).length < 2 ^ (prefixWord ++ tailWord_2351262).sum := by decide
  have hdescent : baseEnd_2351262 < baseStart_2351262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351266 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2351266 : Nat := 118140960795 + 2351266 * 2 ^ 59
def prefixEnd_2351266 : Nat := 4983230072969 + 3 ^ 40 * 2351266 * 2
def baseEnd_2351266 : Nat := 402443201524834298220577

theorem tailTrace_2351266 : CollatzResearch.WordTrace tailWord_2351266 prefixEnd_2351266 402443201524834298220577 := by
  unfold tailWord_2351266
  simp only [CollatzResearch.WordTrace]
  refine ⟨21439429074943080276936413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57171810866514880738497101 21439429074943080276936413)
  ·
    refine ⟨8039785903103655103851155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21439429074943080276936413 8039785903103655103851155)
    ·
      refine ⟨12059678854655482655776733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8039785903103655103851155 12059678854655482655776733)
      ·
        refine ⟨4522379570495805995916275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12059678854655482655776733 4522379570495805995916275)
        ·
          refine ⟨6783569355743708993874413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4522379570495805995916275 6783569355743708993874413)
          ·
            refine ⟨2543838508403890872702905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6783569355743708993874413 2543838508403890872702905)
            ·
              refine ⟨1907878881302918154527179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2543838508403890872702905 1907878881302918154527179)
              ·
                refine ⟨2861818321954377231790769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907878881302918154527179 2861818321954377231790769)
                ·
                  refine ⟨2146363741465782923843077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2861818321954377231790769 2146363741465782923843077)
                  ·
                    refine ⟨402443201524834298220577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2146363741465782923843077 402443201524834298220577)
                    ·
                      rfl

theorem cell23_2351266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2351266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351266 prefixEnd_2351266 := by exact prefixLift 2351266
  have htrace : WordTrace (prefixWord ++ tailWord_2351266) baseStart_2351266 baseEnd_2351266 := by
    simpa [prefixWord, tailWord_2351266, baseEnd_2351266] using wordTrace_append hprefix tailTrace_2351266
  have hstable : (prefixWord ++ tailWord_2351266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351266).length < 2 ^ (prefixWord ++ tailWord_2351266).sum := by decide
  have hdescent : baseEnd_2351266 < baseStart_2351266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351282 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2]
def baseStart_2351282 : Nat := 118140960795 + 2351282 * 2 ^ 59
def prefixEnd_2351282 : Nat := 4983230072969 + 3 ^ 40 * 2351282 * 2
def baseEnd_2351282 : Nat := 1207337820264974832061657

theorem tailTrace_2351282 : CollatzResearch.WordTrace tailWord_2351282 prefixEnd_2351282 1207337820264974832061657 := by
  unfold tailWord_2351282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21439574966928588960082025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57172199911809570560218733 21439574966928588960082025)
  ·
    refine ⟨16079681225196441720061519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21439574966928588960082025 16079681225196441720061519)
    ·
      refine ⟨24119521837794662580092279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16079681225196441720061519 24119521837794662580092279)
      ·
        refine ⟨36179282756691993870138419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24119521837794662580092279 36179282756691993870138419)
        ·
          refine ⟨54268924135037990805207629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36179282756691993870138419 54268924135037990805207629)
          ·
            refine ⟨20350846550639246551952861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54268924135037990805207629 20350846550639246551952861)
            ·
              refine ⟨7631567456489717456982323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20350846550639246551952861 7631567456489717456982323)
              ·
                refine ⟨11447351184734576185473485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7631567456489717456982323 11447351184734576185473485)
                ·
                  refine ⟨4292756694275466069552557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11447351184734576185473485 4292756694275466069552557)
                  ·
                    refine ⟨1609783760353299776082209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4292756694275466069552557 1609783760353299776082209)
                    ·
                      refine ⟨1207337820264974832061657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609783760353299776082209 1207337820264974832061657)
                      ·
                        rfl

theorem cell23_2351282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_2351282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351282 prefixEnd_2351282 := by exact prefixLift 2351282
  have htrace : WordTrace (prefixWord ++ tailWord_2351282) baseStart_2351282 baseEnd_2351282 := by
    simpa [prefixWord, tailWord_2351282, baseEnd_2351282] using wordTrace_append hprefix tailTrace_2351282
  have hstable : (prefixWord ++ tailWord_2351282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351282).length < 2 ^ (prefixWord ++ tailWord_2351282).sum := by decide
  have hdescent : baseEnd_2351282 < baseStart_2351282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351329 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 2, 2, 2]
def baseStart_2351329 : Nat := 118140960795 + 2351329 * 2 ^ 59
def prefixEnd_2351329 : Nat := 4983230072969 + 3 ^ 40 * 2351329 * 2
def baseEnd_2351329 : Nat := 1207361953855736148173941

theorem tailTrace_2351329 : CollatzResearch.WordTrace tailWord_2351329 prefixEnd_2351329 1207361953855736148173941 := by
  unfold tailWord_2351329
  simp only [CollatzResearch.WordTrace]
  refine ⟨85760014098544082867289041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57173342732362721911526027 85760014098544082867289041)
  ·
    refine ⟨64320010573908062150466781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85760014098544082867289041 64320010573908062150466781)
    ·
      refine ⟨24120003965215523306425043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64320010573908062150466781 24120003965215523306425043)
      ·
        refine ⟨36180005947823284959637565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24120003965215523306425043 36180005947823284959637565)
        ·
          refine ⟨13567502230433731859864087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36180005947823284959637565 13567502230433731859864087)
          ·
            refine ⟨20351253345650597789796131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13567502230433731859864087 20351253345650597789796131)
            ·
              refine ⟨30526880018475896684694197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20351253345650597789796131 30526880018475896684694197)
              ·
                refine ⟨2861895001732115314190081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30526880018475896684694197 2861895001732115314190081)
                ·
                  refine ⟨2146421251299086485642561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2861895001732115314190081 2146421251299086485642561)
                  ·
                    refine ⟨1609815938474314864231921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2146421251299086485642561 1609815938474314864231921)
                    ·
                      refine ⟨1207361953855736148173941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609815938474314864231921 1207361953855736148173941)
                      ·
                        rfl

theorem cell23_2351329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_2351329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351329 prefixEnd_2351329 := by exact prefixLift 2351329
  have htrace : WordTrace (prefixWord ++ tailWord_2351329) baseStart_2351329 baseEnd_2351329 := by
    simpa [prefixWord, tailWord_2351329, baseEnd_2351329] using wordTrace_append hprefix tailTrace_2351329
  have hstable : (prefixWord ++ tailWord_2351329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351329).length < 2 ^ (prefixWord ++ tailWord_2351329).sum := by decide
  have hdescent : baseEnd_2351329 < baseStart_2351329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351335 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 9]
def baseStart_2351335 : Nat := 118140960795 + 2351335 * 2 ^ 59
def prefixEnd_2351335 : Nat := 4983230072969 + 3 ^ 40 * 2351335 * 2
def baseEnd_2351335 : Nat := 134151670526629236077657

theorem tailTrace_2351335 : CollatzResearch.WordTrace tailWord_2351335 prefixEnd_2351335 134151670526629236077657 := by
  unfold tailWord_2351335
  simp only [CollatzResearch.WordTrace]
  refine ⟨85760232936522345892007459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57173488624348230594671639 85760232936522345892007459)
  ·
    refine ⟨128640349404783518838011189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85760232936522345892007459 128640349404783518838011189)
    ·
      refine ⟨12060032756698454891063549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128640349404783518838011189 12060032756698454891063549)
      ·
        refine ⟨4522512283761920584148831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12060032756698454891063549 4522512283761920584148831)
        ·
          refine ⟨6783768425642880876223247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4522512283761920584148831 6783768425642880876223247)
          ·
            refine ⟨10175652638464321314334871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6783768425642880876223247 10175652638464321314334871)
            ·
              refine ⟨15263478957696481971502307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10175652638464321314334871 15263478957696481971502307)
              ·
                refine ⟨22895218436544722957253461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15263478957696481971502307 22895218436544722957253461)
                ·
                  refine ⟨134151670526629236077657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22895218436544722957253461 134151670526629236077657)
                  ·
                    rfl

theorem cell23_2351335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 9].length) (baseStart_2351335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351335 prefixEnd_2351335 := by exact prefixLift 2351335
  have htrace : WordTrace (prefixWord ++ tailWord_2351335) baseStart_2351335 baseEnd_2351335 := by
    simpa [prefixWord, tailWord_2351335, baseEnd_2351335] using wordTrace_append hprefix tailTrace_2351335
  have hstable : (prefixWord ++ tailWord_2351335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351335).length < 2 ^ (prefixWord ++ tailWord_2351335).sum := by decide
  have hdescent : baseEnd_2351335 < baseStart_2351335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351435 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 3]
def baseStart_2351435 : Nat := 118140960795 + 2351435 * 2 ^ 59
def prefixEnd_2351435 : Nat := 4983230072969 + 3 ^ 40 * 2351435 * 2
def baseEnd_2351435 : Nat := 1207416382805112733448453

theorem tailTrace_2351435 : CollatzResearch.WordTrace tailWord_2351435 prefixEnd_2351435 1207416382805112733448453 := by
  unfold tailWord_2351435
  simp only [CollatzResearch.WordTrace]
  refine ⟨85763880236160062970647759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57175920157440041980431839 85763880236160062970647759)
  ·
    refine ⟨128645820354240094455971639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85763880236160062970647759 128645820354240094455971639)
    ·
      refine ⟨192968730531360141683957459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128645820354240094455971639 192968730531360141683957459)
      ·
        refine ⟨289453095797040212525936189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192968730531360141683957459 289453095797040212525936189)
        ·
          refine ⟨108544910923890079697226071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289453095797040212525936189 108544910923890079697226071)
          ·
            refine ⟨162817366385835119545839107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108544910923890079697226071 162817366385835119545839107)
            ·
              refine ⟨244226049578752679318758661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162817366385835119545839107 244226049578752679318758661)
              ·
                refine ⟨45792384296016127372267249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244226049578752679318758661 45792384296016127372267249)
                ·
                  refine ⟨34344288222012095529200437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45792384296016127372267249 34344288222012095529200437)
                  ·
                    refine ⟨3219777020813633955862541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34344288222012095529200437 3219777020813633955862541)
                    ·
                      refine ⟨1207416382805112733448453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3219777020813633955862541 1207416382805112733448453)
                      ·
                        rfl

theorem cell23_2351435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 3].length) (baseStart_2351435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351435 prefixEnd_2351435 := by exact prefixLift 2351435
  have htrace : WordTrace (prefixWord ++ tailWord_2351435) baseStart_2351435 baseEnd_2351435 := by
    simpa [prefixWord, tailWord_2351435, baseEnd_2351435] using wordTrace_append hprefix tailTrace_2351435
  have hstable : (prefixWord ++ tailWord_2351435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351435).length < 2 ^ (prefixWord ++ tailWord_2351435).sum := by decide
  have hdescent : baseEnd_2351435 < baseStart_2351435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351492 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_2351492 : Nat := 118140960795 + 2351492 * 2 ^ 59
def prefixEnd_2351492 : Nat := 4983230072969 + 3 ^ 40 * 2351492 * 2
def baseEnd_2351492 : Nat := 1207445651202419010435691

theorem tailTrace_2351492 : CollatzResearch.WordTrace tailWord_2351492 prefixEnd_2351492 1207445651202419010435691 := by
  unfold tailWord_2351492
  simp only [CollatzResearch.WordTrace]
  refine ⟨42882979598476780852736365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57177306131302374470315153 42882979598476780852736365)
  ·
    refine ⟨16081117349428792819776137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42882979598476780852736365 16081117349428792819776137)
    ·
      refine ⟨12060838012071594614832103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16081117349428792819776137 12060838012071594614832103)
      ·
        refine ⟨18091257018107391922248155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12060838012071594614832103 18091257018107391922248155)
        ·
          refine ⟨27136885527161087883372233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18091257018107391922248155 27136885527161087883372233)
          ·
            refine ⟨20352664145370815912529175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27136885527161087883372233 20352664145370815912529175)
            ·
              refine ⟨30528996218056223868793763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20352664145370815912529175 30528996218056223868793763)
              ·
                refine ⟨45793494327084335803190645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30528996218056223868793763 45793494327084335803190645)
                ·
                  refine ⟨4293140093164156481549123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45793494327084335803190645 4293140093164156481549123)
                  ·
                    refine ⟨6439710139746234722323685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4293140093164156481549123 6439710139746234722323685)
                    ·
                      refine ⟨1207445651202419010435691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6439710139746234722323685 1207445651202419010435691)
                      ·
                        rfl

theorem cell23_2351492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_2351492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351492 prefixEnd_2351492 := by exact prefixLift 2351492
  have htrace : WordTrace (prefixWord ++ tailWord_2351492) baseStart_2351492 baseEnd_2351492 := by
    simpa [prefixWord, tailWord_2351492, baseEnd_2351492] using wordTrace_append hprefix tailTrace_2351492
  have hstable : (prefixWord ++ tailWord_2351492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351492).length < 2 ^ (prefixWord ++ tailWord_2351492).sum := by decide
  have hdescent : baseEnd_2351492 < baseStart_2351492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351535 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_2351535 : Nat := 118140960795 + 2351535 * 2 ^ 59
def prefixEnd_2351535 : Nat := 4983230072969 + 3 ^ 40 * 2351535 * 2
def baseEnd_2351535 : Nat := 1207467730870562342197993

theorem tailTrace_2351535 : CollatzResearch.WordTrace tailWord_2351535 prefixEnd_2351535 1207467730870562342197993 := by
  unfold tailWord_2351535
  simp only [CollatzResearch.WordTrace]
  refine ⟨85767527535797780049288059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57178351690531853366192039 85767527535797780049288059)
  ·
    refine ⟨128651291303696670073932089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85767527535797780049288059 128651291303696670073932089)
    ·
      refine ⟨96488468477772502555449067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128651291303696670073932089 96488468477772502555449067)
      ·
        refine ⟨144732702716658753833173601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96488468477772502555449067 144732702716658753833173601)
        ·
          refine ⟨108549527037494065374880201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144732702716658753833173601 108549527037494065374880201)
          ·
            refine ⟨81412145278120549031160151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108549527037494065374880201 81412145278120549031160151)
            ·
              refine ⟨122118217917180823546740227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81412145278120549031160151 122118217917180823546740227)
              ·
                refine ⟨183177326875771235320110341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122118217917180823546740227 183177326875771235320110341)
                ·
                  refine ⟨34345748789207106622520689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183177326875771235320110341 34345748789207106622520689)
                  ·
                    refine ⟨25759311591905329966890517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34345748789207106622520689 25759311591905329966890517)
                    ·
                      refine ⟨1207467730870562342197993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25759311591905329966890517 1207467730870562342197993)
                      ·
                        rfl

theorem cell23_2351535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_2351535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351535 prefixEnd_2351535 := by exact prefixLift 2351535
  have htrace : WordTrace (prefixWord ++ tailWord_2351535) baseStart_2351535 baseEnd_2351535 := by
    simpa [prefixWord, tailWord_2351535, baseEnd_2351535] using wordTrace_append hprefix tailTrace_2351535
  have hstable : (prefixWord ++ tailWord_2351535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351535).length < 2 ^ (prefixWord ++ tailWord_2351535).sum := by decide
  have hdescent : baseEnd_2351535 < baseStart_2351535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351543 : List Nat := [1, 1, 3, 1, 3, 3, 2, 4, 1, 2, 2]
def baseStart_2351543 : Nat := 118140960795 + 2351543 * 2 ^ 59
def prefixEnd_2351543 : Nat := 4983230072969 + 3 ^ 40 * 2351543 * 2
def baseEnd_2351543 : Nat := 1207471838715798310897957

theorem tailTrace_2351543 : CollatzResearch.WordTrace tailWord_2351543 prefixEnd_2351543 1207471838715798310897957 := by
  unfold tailWord_2351543
  simp only [CollatzResearch.WordTrace]
  refine ⟨85767819319768797415579283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57178546213179198277052855 85767819319768797415579283)
  ·
    refine ⟨128651728979653196123368925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85767819319768797415579283 128651728979653196123368925)
    ·
      refine ⟨48244398367369948546263347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128651728979653196123368925 48244398367369948546263347)
      ·
        refine ⟨72366597551054922819395021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48244398367369948546263347 72366597551054922819395021)
        ·
          refine ⟨27137474081645596057273133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72366597551054922819395021 27137474081645596057273133)
          ·
            refine ⟨10176552780617098521477425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27137474081645596057273133 10176552780617098521477425)
            ·
              refine ⟨7632414585462823891108069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10176552780617098521477425 7632414585462823891108069)
              ·
                refine ⟨1431077734774279479582763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7632414585462823891108069 1431077734774279479582763)
                ·
                  refine ⟨2146616602161419219374145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431077734774279479582763 2146616602161419219374145)
                  ·
                    refine ⟨1609962451621064414530609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2146616602161419219374145 1609962451621064414530609)
                    ·
                      refine ⟨1207471838715798310897957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609962451621064414530609 1207471838715798310897957)
                      ·
                        rfl

theorem cell23_2351543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 1, 2, 2].length) (baseStart_2351543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351543 prefixEnd_2351543 := by exact prefixLift 2351543
  have htrace : WordTrace (prefixWord ++ tailWord_2351543) baseStart_2351543 baseEnd_2351543 := by
    simpa [prefixWord, tailWord_2351543, baseEnd_2351543] using wordTrace_append hprefix tailTrace_2351543
  have hstable : (prefixWord ++ tailWord_2351543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351543).length < 2 ^ (prefixWord ++ tailWord_2351543).sum := by decide
  have hdescent : baseEnd_2351543 < baseStart_2351543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351559 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_2351559 : Nat := 118140960795 + 2351559 * 2 ^ 59
def prefixEnd_2351559 : Nat := 4983230072969 + 3 ^ 40 * 2351559 * 2
def baseEnd_2351559 : Nat := 1207480054406270248297883

theorem tailTrace_2351559 : CollatzResearch.WordTrace tailWord_2351559 prefixEnd_2351559 1207480054406270248297883 := by
  unfold tailWord_2351559
  simp only [CollatzResearch.WordTrace]
  refine ⟨85768402887710832148161731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57178935258473888098774487 85768402887710832148161731)
  ·
    refine ⟨128652604331566248222242597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85768402887710832148161731 128652604331566248222242597)
    ·
      refine ⟨24122363312168671541670487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128652604331566248222242597 24122363312168671541670487)
      ·
        refine ⟨36183544968253007312505731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24122363312168671541670487 36183544968253007312505731)
        ·
          refine ⟨54275317452379510968758597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36183544968253007312505731 54275317452379510968758597)
          ·
            refine ⟨10176622022321158306642237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54275317452379510968758597 10176622022321158306642237)
            ·
              refine ⟨3816233258370434364990839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10176622022321158306642237 3816233258370434364990839)
              ·
                refine ⟨5724349887555651547486259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3816233258370434364990839 5724349887555651547486259)
                ·
                  refine ⟨8586524831333477321229389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5724349887555651547486259 8586524831333477321229389)
                  ·
                    refine ⟨3219946811750053995461021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8586524831333477321229389 3219946811750053995461021)
                    ·
                      refine ⟨1207480054406270248297883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3219946811750053995461021 1207480054406270248297883)
                      ·
                        rfl

theorem cell23_2351559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_2351559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351559 prefixEnd_2351559 := by exact prefixLift 2351559
  have htrace : WordTrace (prefixWord ++ tailWord_2351559) baseStart_2351559 baseEnd_2351559 := by
    simpa [prefixWord, tailWord_2351559, baseEnd_2351559] using wordTrace_append hprefix tailTrace_2351559
  have hstable : (prefixWord ++ tailWord_2351559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351559).length < 2 ^ (prefixWord ++ tailWord_2351559).sum := by decide
  have hdescent : baseEnd_2351559 < baseStart_2351559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351569 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 3, 3, 2]
def baseStart_2351569 : Nat := 118140960795 + 2351569 * 2 ^ 59
def prefixEnd_2351569 : Nat := 4983230072969 + 3 ^ 40 * 2351569 * 2
def baseEnd_2351569 : Nat := 1207485189212815209172837

theorem tailTrace_2351569 : CollatzResearch.WordTrace tailWord_2351569 prefixEnd_2351569 1207485189212815209172837 := by
  unfold tailWord_2351569
  simp only [CollatzResearch.WordTrace]
  refine ⟨85768767617674603856025761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57179178411783069237350507 85768767617674603856025761)
  ·
    refine ⟨64326575713255952892019321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85768767617674603856025761 64326575713255952892019321)
    ·
      refine ⟨48244931784941964669014491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64326575713255952892019321 48244931784941964669014491)
      ·
        refine ⟨72367397677412947003521737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48244931784941964669014491 72367397677412947003521737)
        ·
          refine ⟨54275548258059710252641303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72367397677412947003521737 54275548258059710252641303)
          ·
            refine ⟨81413322387089565378961955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54275548258059710252641303 81413322387089565378961955)
            ·
              refine ⟨122119983580634348068442933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81413322387089565378961955 122119983580634348068442933)
              ·
                refine ⟨11448748460684470131416525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122119983580634348068442933 11448748460684470131416525)
                ·
                  refine ⟨4293280672756676299281197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11448748460684470131416525 4293280672756676299281197)
                  ·
                    refine ⟨1609980252283753612230449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4293280672756676299281197 1609980252283753612230449)
                    ·
                      refine ⟨1207485189212815209172837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1609980252283753612230449 1207485189212815209172837)
                      ·
                        rfl

theorem cell23_2351569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_2351569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351569 prefixEnd_2351569 := by exact prefixLift 2351569
  have htrace : WordTrace (prefixWord ++ tailWord_2351569) baseStart_2351569 baseEnd_2351569 := by
    simpa [prefixWord, tailWord_2351569, baseEnd_2351569] using wordTrace_append hprefix tailTrace_2351569
  have hstable : (prefixWord ++ tailWord_2351569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351569).length < 2 ^ (prefixWord ++ tailWord_2351569).sum := by decide
  have hdescent : baseEnd_2351569 < baseStart_2351569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351612 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_2351612 : Nat := 118140960795 + 2351612 * 2 ^ 59
def prefixEnd_2351612 : Nat := 4983230072969 + 3 ^ 40 * 2351612 * 2
def baseEnd_2351612 : Nat := 1207507268880958540935139

theorem tailTrace_2351612 : CollatzResearch.WordTrace tailWord_2351612 prefixEnd_2351612 1207507268880958540935139 := by
  unfold tailWord_2351612
  simp only [CollatzResearch.WordTrace]
  refine ⟨42885167978259411099920545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57180223971012548133227393 42885167978259411099920545)
  ·
    refine ⟨32163875983694558324940409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42885167978259411099920545 32163875983694558324940409)
    ·
      refine ⟨24122906987770918743705307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32163875983694558324940409 24122906987770918743705307)
      ·
        refine ⟨36184360481656378115557961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24122906987770918743705307 36184360481656378115557961)
        ·
          refine ⟨27138270361242283586668471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36184360481656378115557961 27138270361242283586668471)
          ·
            refine ⟨40707405541863425380002707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27138270361242283586668471 40707405541863425380002707)
            ·
              refine ⟨61061108312795138070004061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40707405541863425380002707 61061108312795138070004061)
              ·
                refine ⟨22897915617298176776251523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61061108312795138070004061 22897915617298176776251523)
                ·
                  refine ⟨34346873425947265164377285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22897915617298176776251523 34346873425947265164377285)
                  ·
                    refine ⟨6440038767365112218320741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34346873425947265164377285 6440038767365112218320741)
                    ·
                      refine ⟨1207507268880958540935139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6440038767365112218320741 1207507268880958540935139)
                      ·
                        rfl

theorem cell23_2351612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_2351612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351612 prefixEnd_2351612 := by exact prefixLift 2351612
  have htrace : WordTrace (prefixWord ++ tailWord_2351612) baseStart_2351612 baseEnd_2351612 := by
    simpa [prefixWord, tailWord_2351612, baseEnd_2351612] using wordTrace_append hprefix tailTrace_2351612
  have hstable : (prefixWord ++ tailWord_2351612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351612).length < 2 ^ (prefixWord ++ tailWord_2351612).sum := by decide
  have hdescent : baseEnd_2351612 < baseStart_2351612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351620 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_2351620 : Nat := 118140960795 + 2351620 * 2 ^ 59
def prefixEnd_2351620 : Nat := 4983230072969 + 3 ^ 40 * 2351620 * 2
def baseEnd_2351620 : Nat := 1207511376726194509635103

theorem tailTrace_2351620 : CollatzResearch.WordTrace tailWord_2351620 prefixEnd_2351620 1207511376726194509635103 := by
  unfold tailWord_2351620
  simp only [CollatzResearch.WordTrace]
  refine ⟨42885313870244919783066157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57180418493659893044088209 42885313870244919783066157)
  ·
    refine ⟨16081992701341844918649809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42885313870244919783066157 16081992701341844918649809)
    ·
      refine ⟨12061494526006383688987357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16081992701341844918649809 12061494526006383688987357)
      ·
        refine ⟨4523060447252393883370259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12061494526006383688987357 4523060447252393883370259)
        ·
          refine ⟨6784590670878590825055389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523060447252393883370259 6784590670878590825055389)
          ·
            refine ⟨2544221501579471559395771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6784590670878590825055389 2544221501579471559395771)
            ·
              refine ⟨3816332252369207339093657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544221501579471559395771 3816332252369207339093657)
              ·
                refine ⟨2862249189276905504320243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3816332252369207339093657 2862249189276905504320243)
                ·
                  refine ⟨4293373783915358256480365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862249189276905504320243 4293373783915358256480365)
                  ·
                    refine ⟨1610015168968259346180137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4293373783915358256480365 1610015168968259346180137)
                    ·
                      refine ⟨1207511376726194509635103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1610015168968259346180137 1207511376726194509635103)
                      ·
                        rfl

theorem cell23_2351620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_2351620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351620 prefixEnd_2351620 := by exact prefixLift 2351620
  have htrace : WordTrace (prefixWord ++ tailWord_2351620) baseStart_2351620 baseEnd_2351620 := by
    simpa [prefixWord, tailWord_2351620, baseEnd_2351620] using wordTrace_append hprefix tailTrace_2351620
  have hstable : (prefixWord ++ tailWord_2351620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351620).length < 2 ^ (prefixWord ++ tailWord_2351620).sum := by decide
  have hdescent : baseEnd_2351620 < baseStart_2351620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351636 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2351636 : Nat := 118140960795 + 2351636 * 2 ^ 59
def prefixEnd_2351636 : Nat := 4983230072969 + 3 ^ 40 * 2351636 * 2
def baseEnd_2351636 : Nat := 1207519592416666447035029

theorem tailTrace_2351636 : CollatzResearch.WordTrace tailWord_2351636 prefixEnd_2351636 1207519592416666447035029 := by
  unfold tailWord_2351636
  simp only [CollatzResearch.WordTrace]
  refine ⟨42885605654215937149357381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57180807538954582865809841 42885605654215937149357381)
  ·
    refine ⟨8041051060165488215504509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42885605654215937149357381 8041051060165488215504509)
    ·
      refine ⟨3015394147562058080814191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8041051060165488215504509 3015394147562058080814191)
      ·
        refine ⟨4523091221343087121221287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015394147562058080814191 4523091221343087121221287)
        ·
          refine ⟨6784636832014630681831931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523091221343087121221287 6784636832014630681831931)
          ·
            refine ⟨10176955248021946022747897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6784636832014630681831931 10176955248021946022747897)
            ·
              refine ⟨7632716436016459517060923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10176955248021946022747897 7632716436016459517060923)
              ·
                refine ⟨11449074654024689275591385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7632716436016459517060923 11449074654024689275591385)
                ·
                  refine ⟨8586805990518516956693539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11449074654024689275591385 8586805990518516956693539)
                  ·
                    refine ⟨12880208985777775435040309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8586805990518516956693539 12880208985777775435040309)
                    ·
                      refine ⟨1207519592416666447035029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12880208985777775435040309 1207519592416666447035029)
                      ·
                        rfl

theorem cell23_2351636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2351636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351636 prefixEnd_2351636 := by exact prefixLift 2351636
  have htrace : WordTrace (prefixWord ++ tailWord_2351636) baseStart_2351636 baseEnd_2351636 := by
    simpa [prefixWord, tailWord_2351636, baseEnd_2351636] using wordTrace_append hprefix tailTrace_2351636
  have hstable : (prefixWord ++ tailWord_2351636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351636).length < 2 ^ (prefixWord ++ tailWord_2351636).sum := by decide
  have hdescent : baseEnd_2351636 < baseStart_2351636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351649 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_2351649 : Nat := 118140960795 + 2351649 * 2 ^ 59
def prefixEnd_2351649 : Nat := 4983230072969 + 3 ^ 40 * 2351649 * 2
def baseEnd_2351649 : Nat := 1207526267665174896172469

theorem tailTrace_2351649 : CollatzResearch.WordTrace tailWord_2351649 prefixEnd_2351649 1207526267665174896172469 := by
  unfold tailWord_2351649
  simp only [CollatzResearch.WordTrace]
  refine ⟨85771685457384777518938001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57181123638256518345958667 85771685457384777518938001)
  ·
    refine ⟨64328764093038583139203501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85771685457384777518938001 64328764093038583139203501)
    ·
      refine ⟨24123286534889468677201313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64328764093038583139203501 24123286534889468677201313)
      ·
        refine ⟨18092464901167101507900985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24123286534889468677201313 18092464901167101507900985)
        ·
          refine ⟨13569348675875326130925739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18092464901167101507900985 13569348675875326130925739)
          ·
            refine ⟨20354023013812989196388609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13569348675875326130925739 20354023013812989196388609)
            ·
              refine ⟨15265517260359741897291457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20354023013812989196388609 15265517260359741897291457)
              ·
                refine ⟨11449137945269806422968593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15265517260359741897291457 11449137945269806422968593)
                ·
                  refine ⟨8586853458952354817226445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11449137945269806422968593 8586853458952354817226445)
                  ·
                    refine ⟨3220070047107133056459917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8586853458952354817226445 3220070047107133056459917)
                    ·
                      refine ⟨1207526267665174896172469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3220070047107133056459917 1207526267665174896172469)
                      ·
                        rfl

theorem cell23_2351649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_2351649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351649 prefixEnd_2351649 := by exact prefixLift 2351649
  have htrace : WordTrace (prefixWord ++ tailWord_2351649) baseStart_2351649 baseEnd_2351649 := by
    simpa [prefixWord, tailWord_2351649, baseEnd_2351649] using wordTrace_append hprefix tailTrace_2351649
  have hstable : (prefixWord ++ tailWord_2351649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351649).length < 2 ^ (prefixWord ++ tailWord_2351649).sum := by decide
  have hdescent : baseEnd_2351649 < baseStart_2351649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351716 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_2351716 : Nat := 118140960795 + 2351716 * 2 ^ 59
def prefixEnd_2351716 : Nat := 4983230072969 + 3 ^ 40 * 2351716 * 2
def baseEnd_2351716 : Nat := 402520223623008711344887

theorem tailTrace_2351716 : CollatzResearch.WordTrace tailWord_2351716 prefixEnd_2351716 402520223623008711344887 := by
  unfold tailWord_2351716
  simp only [CollatzResearch.WordTrace]
  refine ⟨42887064574071023980813501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57182752765428031974418001 42887064574071023980813501)
  ·
    refine ⟨16082649215276633992805063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42887064574071023980813501 16082649215276633992805063)
    ·
      refine ⟨24123973822914950989207595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16082649215276633992805063 24123973822914950989207595)
      ·
        refine ⟨36185960734372426483811393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24123973822914950989207595 36185960734372426483811393)
        ·
          refine ⟨27139470550779319862858545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36185960734372426483811393 27139470550779319862858545)
          ·
            refine ⟨20354602913084489897143909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27139470550779319862858545 20354602913084489897143909)
            ·
              refine ⟨3816488046203341855714483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20354602913084489897143909 3816488046203341855714483)
              ·
                refine ⟨5724732069305012783571725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3816488046203341855714483 5724732069305012783571725)
                ·
                  refine ⟨2146774525989379793839397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5724732069305012783571725 2146774525989379793839397)
                  ·
                    refine ⟨402520223623008711344887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2146774525989379793839397 402520223623008711344887)
                    ·
                      rfl

theorem cell23_2351716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_2351716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351716 prefixEnd_2351716 := by exact prefixLift 2351716
  have htrace : WordTrace (prefixWord ++ tailWord_2351716) baseStart_2351716 baseEnd_2351716 := by
    simpa [prefixWord, tailWord_2351716, baseEnd_2351716] using wordTrace_append hprefix tailTrace_2351716
  have hstable : (prefixWord ++ tailWord_2351716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351716).length < 2 ^ (prefixWord ++ tailWord_2351716).sum := by decide
  have hdescent : baseEnd_2351716 < baseStart_2351716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351726 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2351726 : Nat := 118140960795 + 2351726 * 2 ^ 59
def prefixEnd_2351726 : Nat := 4983230072969 + 3 ^ 40 * 2351726 * 2
def baseEnd_2351726 : Nat := 1207565805675571094909615

theorem tailTrace_2351726 : CollatzResearch.WordTrace tailWord_2351726 prefixEnd_2351726 1207565805675571094909615 := by
  unfold tailWord_2351726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10721811734763227458686379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57182995918737213112994021 10721811734763227458686379)
  ·
    refine ⟨16082717602144841188029569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10721811734763227458686379 16082717602144841188029569)
    ·
      refine ⟨12062038201608630891022177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16082717602144841188029569 12062038201608630891022177)
      ·
        refine ⟨9046528651206473168266633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12062038201608630891022177 9046528651206473168266633)
        ·
          refine ⟨6784896488404854876199975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9046528651206473168266633 6784896488404854876199975)
          ·
            refine ⟨10177344732607282314299963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6784896488404854876199975 10177344732607282314299963)
            ·
              refine ⟨15266017098910923471449945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10177344732607282314299963 15266017098910923471449945)
              ·
                refine ⟨11449512824183192603587459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15266017098910923471449945 11449512824183192603587459)
                ·
                  refine ⟨17174269236274788905381189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11449512824183192603587459 17174269236274788905381189)
                  ·
                    refine ⟨3220175481801522919758973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17174269236274788905381189 3220175481801522919758973)
                    ·
                      refine ⟨1207565805675571094909615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3220175481801522919758973 1207565805675571094909615)
                      ·
                        rfl

theorem cell23_2351726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2351726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351726 prefixEnd_2351726 := by exact prefixLift 2351726
  have htrace : WordTrace (prefixWord ++ tailWord_2351726) baseStart_2351726 baseEnd_2351726 := by
    simpa [prefixWord, tailWord_2351726, baseEnd_2351726] using wordTrace_append hprefix tailTrace_2351726
  have hstable : (prefixWord ++ tailWord_2351726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351726).length < 2 ^ (prefixWord ++ tailWord_2351726).sum := by decide
  have hdescent : baseEnd_2351726 < baseStart_2351726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351773 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_2351773 : Nat := 118140960795 + 2351773 * 2 ^ 59
def prefixEnd_2351773 : Nat := 4983230072969 + 3 ^ 40 * 2351773 * 2
def baseEnd_2351773 : Nat := 1207589939266332411021899

theorem tailTrace_2351773 : CollatzResearch.WordTrace tailWord_2351773 prefixEnd_2351773 1207589939266332411021899 := by
  unfold tailWord_2351773
  simp only [CollatzResearch.WordTrace]
  refine ⟨85776208108935546696451973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57184138739290364464301315 85776208108935546696451973)
  ·
    refine ⟨16083039020425415005584745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85776208108935546696451973 16083039020425415005584745)
    ·
      refine ⟨12062279265319061254188559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16083039020425415005584745 12062279265319061254188559)
      ·
        refine ⟨18093418897978591881282839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12062279265319061254188559 18093418897978591881282839)
        ·
          refine ⟨27140128346967887821924259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18093418897978591881282839 27140128346967887821924259)
          ·
            refine ⟨40710192520451831732886389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27140128346967887821924259 40710192520451831732886389)
            ·
              refine ⟨3816580548792359224958099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40710192520451831732886389 3816580548792359224958099)
              ·
                refine ⟨5724870823188538837437149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3816580548792359224958099 5724870823188538837437149)
                ·
                  refine ⟨2146826558695702064038931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5724870823188538837437149 2146826558695702064038931)
                  ·
                    refine ⟨3220239838043553096058397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2146826558695702064038931 3220239838043553096058397)
                    ·
                      refine ⟨1207589939266332411021899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3220239838043553096058397 1207589939266332411021899)
                      ·
                        rfl

theorem cell23_2351773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_2351773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351773 prefixEnd_2351773 := by exact prefixLift 2351773
  have htrace : WordTrace (prefixWord ++ tailWord_2351773) baseStart_2351773 baseEnd_2351773 := by
    simpa [prefixWord, tailWord_2351773, baseEnd_2351773] using wordTrace_append hprefix tailTrace_2351773
  have hstable : (prefixWord ++ tailWord_2351773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351773).length < 2 ^ (prefixWord ++ tailWord_2351773).sum := by decide
  have hdescent : baseEnd_2351773 < baseStart_2351773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351793 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 3, 5]
def baseStart_2351793 : Nat := 118140960795 + 2351793 * 2 ^ 59
def prefixEnd_2351793 : Nat := 4983230072969 + 3 ^ 40 * 2351793 * 2
def baseEnd_2351793 : Nat := 402533402959807444257269

theorem tailTrace_2351793 : CollatzResearch.WordTrace tailWord_2351793 prefixEnd_2351793 402533402959807444257269 := by
  unfold tailWord_2351793
  simp only [CollatzResearch.WordTrace]
  refine ⟨85776937568863090112180033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57184625045908726741453355 85776937568863090112180033)
  ·
    refine ⟨64332703176647317584135025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85776937568863090112180033 64332703176647317584135025)
    ·
      refine ⟨48249527382485488188101269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64332703176647317584135025 48249527382485488188101269)
      ·
        refine ⟨2261696596054007258817247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48249527382485488188101269 2261696596054007258817247)
        ·
          refine ⟨3392544894081010888225871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261696596054007258817247 3392544894081010888225871)
          ·
            refine ⟨5088817341121516332338807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3392544894081010888225871 5088817341121516332338807)
            ·
              refine ⟨7633226011682274498508211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5088817341121516332338807 7633226011682274498508211)
              ·
                refine ⟨11449839017523411747762317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7633226011682274498508211 11449839017523411747762317)
                ·
                  refine ⟨4293689631571279405410869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11449839017523411747762317 4293689631571279405410869)
                  ·
                    refine ⟨402533402959807444257269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4293689631571279405410869 402533402959807444257269)
                    ·
                      rfl

theorem cell23_2351793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_2351793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351793 prefixEnd_2351793 := by exact prefixLift 2351793
  have htrace : WordTrace (prefixWord ++ tailWord_2351793) baseStart_2351793 baseEnd_2351793 := by
    simpa [prefixWord, tailWord_2351793, baseEnd_2351793] using wordTrace_append hprefix tailTrace_2351793
  have hstable : (prefixWord ++ tailWord_2351793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351793).length < 2 ^ (prefixWord ++ tailWord_2351793).sum := by decide
  have hdescent : baseEnd_2351793 < baseStart_2351793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351806 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2351806 : Nat := 118140960795 + 2351806 * 2 ^ 59
def prefixEnd_2351806 : Nat := 4983230072969 + 3 ^ 40 * 2351806 * 2
def baseEnd_2351806 : Nat := 402535628042643593969749

theorem tailTrace_2351806 : CollatzResearch.WordTrace tailWord_2351806 prefixEnd_2351806 402535628042643593969749 := by
  unfold tailWord_2351806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10722176464726999166550409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57184941145210662221602181 10722176464726999166550409)
  ·
    refine ⟨8041632348545249374912807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10722176464726999166550409 8041632348545249374912807)
    ·
      refine ⟨12062448522817874062369211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8041632348545249374912807 12062448522817874062369211)
      ·
        refine ⟨18093672784226811093553817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12062448522817874062369211 18093672784226811093553817)
        ·
          refine ⟨13570254588170108320165363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18093672784226811093553817 13570254588170108320165363)
          ·
            refine ⟨20355381882255162480248045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13570254588170108320165363 20355381882255162480248045)
            ·
              refine ⟨7633268205845685930093017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20355381882255162480248045 7633268205845685930093017)
              ·
                refine ⟨5724951154384264447569763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7633268205845685930093017 5724951154384264447569763)
                ·
                  refine ⟨8587426731576396671354645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5724951154384264447569763 8587426731576396671354645)
                  ·
                    refine ⟨402535628042643593969749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8587426731576396671354645 402535628042643593969749)
                    ·
                      rfl

theorem cell23_2351806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2351806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351806 prefixEnd_2351806 := by exact prefixLift 2351806
  have htrace : WordTrace (prefixWord ++ tailWord_2351806) baseStart_2351806 baseEnd_2351806 := by
    simpa [prefixWord, tailWord_2351806, baseEnd_2351806] using wordTrace_append hprefix tailTrace_2351806
  have hstable : (prefixWord ++ tailWord_2351806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351806).length < 2 ^ (prefixWord ++ tailWord_2351806).sum := by decide
  have hdescent : baseEnd_2351806 < baseStart_2351806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351816 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_2351816 : Nat := 118140960795 + 2351816 * 2 ^ 59
def prefixEnd_2351816 : Nat := 4983230072969 + 3 ^ 40 * 2351816 * 2
def baseEnd_2351816 : Nat := 1207612018934475742784201

theorem tailTrace_2351816 : CollatzResearch.WordTrace tailWord_2351816 prefixEnd_2351816 1207612018934475742784201 := by
  unfold tailWord_2351816
  simp only [CollatzResearch.WordTrace]
  refine ⟨42888888223889882520133651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57185184298519843360178201 42888888223889882520133651)
  ·
    refine ⟨64333332335834823780200477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42888888223889882520133651 64333332335834823780200477)
    ·
      refine ⟨24124999625938058917575179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64333332335834823780200477 24124999625938058917575179)
      ·
        refine ⟨36187499438907088376362769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24124999625938058917575179 36187499438907088376362769)
        ·
          refine ⟨27140624579180316282272077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36187499438907088376362769 27140624579180316282272077)
          ·
            refine ⟨10177734217192618605852029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27140624579180316282272077 10177734217192618605852029)
            ·
              refine ⟨3816650331447231977194511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10177734217192618605852029 3816650331447231977194511)
              ·
                refine ⟨5724975497170847965791767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3816650331447231977194511 5724975497170847965791767)
                ·
                  refine ⟨8587463245756271948687651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5724975497170847965791767 8587463245756271948687651)
                  ·
                    refine ⟨12881194868634407923031477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8587463245756271948687651 12881194868634407923031477)
                    ·
                      refine ⟨1207612018934475742784201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12881194868634407923031477 1207612018934475742784201)
                      ·
                        rfl

theorem cell23_2351816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_2351816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351816 prefixEnd_2351816 := by exact prefixLift 2351816
  have htrace : WordTrace (prefixWord ++ tailWord_2351816) baseStart_2351816 baseEnd_2351816 := by
    simpa [prefixWord, tailWord_2351816, baseEnd_2351816] using wordTrace_append hprefix tailTrace_2351816
  have hstable : (prefixWord ++ tailWord_2351816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351816).length < 2 ^ (prefixWord ++ tailWord_2351816).sum := by decide
  have hdescent : baseEnd_2351816 < baseStart_2351816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351843 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2351843 : Nat := 118140960795 + 2351843 * 2 ^ 59
def prefixEnd_2351843 : Nat := 4983230072969 + 3 ^ 40 * 2351843 * 2
def baseEnd_2351843 : Nat := 1207625882912147137146577

theorem tailTrace_2351843 : CollatzResearch.WordTrace tailWord_2351843 prefixEnd_2351843 1207625882912147137146577 := by
  unfold tailWord_2351843
  simp only [CollatzResearch.WordTrace]
  refine ⟨85778761218681948651500183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57185840812454632434333455 85778761218681948651500183)
  ·
    refine ⟨128668141828022922977250275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85778761218681948651500183 128668141828022922977250275)
    ·
      refine ⟨193002212742034384465875413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128668141828022922977250275 193002212742034384465875413)
      ·
        refine ⟨4523489361141430885918955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 193002212742034384465875413 4523489361141430885918955)
        ·
          refine ⟨6785234041712146328878433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523489361141430885918955 6785234041712146328878433)
          ·
            refine ⟨5088925531284109746658825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6785234041712146328878433 5088925531284109746658825)
            ·
              refine ⟨3816694148463082309994119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5088925531284109746658825 3816694148463082309994119)
              ·
                refine ⟨5725041222694623464991179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3816694148463082309994119 5725041222694623464991179)
                ·
                  refine ⟨8587561834041935197486769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5725041222694623464991179 8587561834041935197486769)
                  ·
                    refine ⟨6440671375531451398115077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8587561834041935197486769 6440671375531451398115077)
                    ·
                      refine ⟨1207625882912147137146577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6440671375531451398115077 1207625882912147137146577)
                      ·
                        rfl

theorem cell23_2351843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2351843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351843 prefixEnd_2351843 := by exact prefixLift 2351843
  have htrace : WordTrace (prefixWord ++ tailWord_2351843) baseStart_2351843 baseEnd_2351843 := by
    simpa [prefixWord, tailWord_2351843, baseEnd_2351843] using wordTrace_append hprefix tailTrace_2351843
  have hstable : (prefixWord ++ tailWord_2351843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351843).length < 2 ^ (prefixWord ++ tailWord_2351843).sum := by decide
  have hdescent : baseEnd_2351843 < baseStart_2351843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351859 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 5]
def baseStart_2351859 : Nat := 118140960795 + 2351859 * 2 ^ 59
def prefixEnd_2351859 : Nat := 4983230072969 + 3 ^ 40 * 2351859 * 2
def baseEnd_2351859 : Nat := 1207634098602619074546503

theorem tailTrace_2351859 : CollatzResearch.WordTrace tailWord_2351859 prefixEnd_2351859 1207634098602619074546503 := by
  unfold tailWord_2351859
  simp only [CollatzResearch.WordTrace]
  refine ⟨85779344786623983384082631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57186229857749322256055087 85779344786623983384082631)
  ·
    refine ⟨128669017179935975076123947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85779344786623983384082631 128669017179935975076123947)
    ·
      refine ⟨193003525769903962614185921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128669017179935975076123947 193003525769903962614185921)
      ·
        refine ⟨144752644327427971960639441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193003525769903962614185921 144752644327427971960639441)
        ·
          refine ⟨108564483245570978970479581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144752644327427971960639441 108564483245570978970479581)
          ·
            refine ⟨40711681217089117113929843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108564483245570978970479581 40711681217089117113929843)
            ·
              refine ⟨61067521825633675670894765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40711681217089117113929843 61067521825633675670894765)
              ·
                refine ⟨22900320684612628376585537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61067521825633675670894765 22900320684612628376585537)
                ·
                  refine ⟨17175240513459471282439153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22900320684612628376585537 17175240513459471282439153)
                  ·
                    refine ⟨12881430385094603461829365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17175240513459471282439153 12881430385094603461829365)
                    ·
                      refine ⟨1207634098602619074546503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12881430385094603461829365 1207634098602619074546503)
                      ·
                        rfl

theorem cell23_2351859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_2351859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351859 prefixEnd_2351859 := by exact prefixLift 2351859
  have htrace : WordTrace (prefixWord ++ tailWord_2351859) baseStart_2351859 baseEnd_2351859 := by
    simpa [prefixWord, tailWord_2351859, baseEnd_2351859] using wordTrace_append hprefix tailTrace_2351859
  have hstable : (prefixWord ++ tailWord_2351859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351859).length < 2 ^ (prefixWord ++ tailWord_2351859).sum := by decide
  have hdescent : baseEnd_2351859 < baseStart_2351859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351861 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2351861 : Nat := 118140960795 + 2351861 * 2 ^ 59
def prefixEnd_2351861 : Nat := 4983230072969 + 3 ^ 40 * 2351861 * 2
def baseEnd_2351861 : Nat := 402545041854642688907165

theorem tailTrace_2351861 : CollatzResearch.WordTrace tailWord_2351861 prefixEnd_2351861 402545041854642688907165 := by
  unfold tailWord_2351861
  simp only [CollatzResearch.WordTrace]
  refine ⟨85779417732616737725655437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57186278488411158483770291 85779417732616737725655437)
  ·
    refine ⟨32167281649731276647120789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85779417732616737725655437 32167281649731276647120789)
    ·
      refine ⟨1507841327331153592833787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32167281649731276647120789 1507841327331153592833787)
      ·
        refine ⟨2261761990996730389250681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507841327331153592833787 2261761990996730389250681)
        ·
          refine ⟨1696321493247547791938011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2261761990996730389250681 1696321493247547791938011)
          ·
            refine ⟨2544482239871321687907017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696321493247547791938011 2544482239871321687907017)
            ·
              refine ⟨1908361679903491265930263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2544482239871321687907017 1908361679903491265930263)
              ·
                refine ⟨2862542519855236898895395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908361679903491265930263 2862542519855236898895395)
                ·
                  refine ⟨4293813779782855348343093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862542519855236898895395 4293813779782855348343093)
                  ·
                    refine ⟨402545041854642688907165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4293813779782855348343093 402545041854642688907165)
                    ·
                      rfl

theorem cell23_2351861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2351861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351861 prefixEnd_2351861 := by exact prefixLift 2351861
  have htrace : WordTrace (prefixWord ++ tailWord_2351861) baseStart_2351861 baseEnd_2351861 := by
    simpa [prefixWord, tailWord_2351861, baseEnd_2351861] using wordTrace_append hprefix tailTrace_2351861
  have hstable : (prefixWord ++ tailWord_2351861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351861).length < 2 ^ (prefixWord ++ tailWord_2351861).sum := by decide
  have hdescent : baseEnd_2351861 < baseStart_2351861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351880 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_2351880 : Nat := 118140960795 + 2351880 * 2 ^ 59
def prefixEnd_2351880 : Nat := 4983230072969 + 3 ^ 40 * 2351880 * 2
def baseEnd_2351880 : Nat := 1207644881696363492383907

theorem tailTrace_2351880 : CollatzResearch.WordTrace tailWord_2351880 prefixEnd_2351880 1207644881696363492383907 := by
  unfold tailWord_2351880
  simp only [CollatzResearch.WordTrace]
  refine ⟨42890055359773951985298547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57186740479698602647064729 42890055359773951985298547)
  ·
    refine ⟨64335083039660927977947821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42890055359773951985298547 64335083039660927977947821)
    ·
      refine ⟨24125656139872847991730433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64335083039660927977947821 24125656139872847991730433)
      ·
        refine ⟨18094242104904635993797825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24125656139872847991730433 18094242104904635993797825)
        ·
          refine ⟨13570681578678476995348369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18094242104904635993797825 13570681578678476995348369)
          ·
            refine ⟨10178011184008857746511277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13570681578678476995348369 10178011184008857746511277)
            ·
              refine ⟨3816754194003321654941729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10178011184008857746511277 3816754194003321654941729)
              ·
                refine ⟨2862565645502491241206297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3816754194003321654941729 2862565645502491241206297)
                ·
                  refine ⟨2146924234126868430904723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2862565645502491241206297 2146924234126868430904723)
                  ·
                    refine ⟨3220386351190302646357085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2146924234126868430904723 3220386351190302646357085)
                    ·
                      refine ⟨1207644881696363492383907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3220386351190302646357085 1207644881696363492383907)
                      ·
                        rfl

theorem cell23_2351880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_2351880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351880 prefixEnd_2351880 := by exact prefixLift 2351880
  have htrace : WordTrace (prefixWord ++ tailWord_2351880) baseStart_2351880 baseEnd_2351880 := by
    simpa [prefixWord, tailWord_2351880, baseEnd_2351880] using wordTrace_append hprefix tailTrace_2351880
  have hstable : (prefixWord ++ tailWord_2351880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351880).length < 2 ^ (prefixWord ++ tailWord_2351880).sum := by decide
  have hdescent : baseEnd_2351880 < baseStart_2351880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351919 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_2351919 : Nat := 118140960795 + 2351919 * 2 ^ 59
def prefixEnd_2351919 : Nat := 4983230072969 + 3 ^ 40 * 2351919 * 2
def baseEnd_2351919 : Nat := 1207664907441888839796227

theorem tailTrace_2351919 : CollatzResearch.WordTrace tailWord_2351919 prefixEnd_2351919 1207664907441888839796227 := by
  unfold tailWord_2351919
  simp only [CollatzResearch.WordTrace]
  refine ⟨85781533166406613631266811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57187688777604409087511207 85781533166406613631266811)
  ·
    refine ⟨128672299749609920446900217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85781533166406613631266811 128672299749609920446900217)
    ·
      refine ⟨96504224812207440335175163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128672299749609920446900217 96504224812207440335175163)
      ·
        refine ⟨144756337218311160502762745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96504224812207440335175163 144756337218311160502762745)
        ·
          refine ⟨108567252913733370377072059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144756337218311160502762745 108567252913733370377072059)
          ·
            refine ⟨162850879370600055565608089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108567252913733370377072059 162850879370600055565608089)
            ·
              refine ⟨122138159527950041674206067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162850879370600055565608089 122138159527950041674206067)
              ·
                refine ⟨183207239291925062511309101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122138159527950041674206067 183207239291925062511309101)
                ·
                  refine ⟨68702714734471898441740913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183207239291925062511309101 68702714734471898441740913)
                  ·
                    refine ⟨51527036050853923831305685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68702714734471898441740913 51527036050853923831305685)
                    ·
                      refine ⟨1207664907441888839796227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51527036050853923831305685 1207664907441888839796227)
                      ·
                        rfl

theorem cell23_2351919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_2351919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351919 prefixEnd_2351919 := by exact prefixLift 2351919
  have htrace : WordTrace (prefixWord ++ tailWord_2351919) baseStart_2351919 baseEnd_2351919 := by
    simpa [prefixWord, tailWord_2351919, baseEnd_2351919] using wordTrace_append hprefix tailTrace_2351919
  have hstable : (prefixWord ++ tailWord_2351919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351919).length < 2 ^ (prefixWord ++ tailWord_2351919).sum := by decide
  have hdescent : baseEnd_2351919 < baseStart_2351919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351936 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3]
def baseStart_2351936 : Nat := 118140960795 + 2351936 * 2 ^ 59
def prefixEnd_2351936 : Nat := 4983230072969 + 3 ^ 40 * 2351936 * 2
def baseEnd_2351936 : Nat := 1207673636613015273283649

theorem tailTrace_2351936 : CollatzResearch.WordTrace tailWord_2351936 prefixEnd_2351936 1207673636613015273283649 := by
  unfold tailWord_2351936
  simp only [CollatzResearch.WordTrace]
  refine ⟨42891076603672512767317831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57188102138230017023090441 42891076603672512767317831)
  ·
    refine ⟨64336614905508769150976747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42891076603672512767317831 64336614905508769150976747)
    ·
      refine ⟨96504922358263153726465121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64336614905508769150976747 96504922358263153726465121)
      ·
        refine ⟨72378691768697365294848841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96504922358263153726465121 72378691768697365294848841)
        ·
          refine ⟨54284018826523023971136631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72378691768697365294848841 54284018826523023971136631)
          ·
            refine ⟨81426028239784535956704947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54284018826523023971136631 81426028239784535956704947)
            ·
              refine ⟨122139042359676803935057421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81426028239784535956704947 122139042359676803935057421)
              ·
                refine ⟨45802140884878801475646533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122139042359676803935057421 45802140884878801475646533)
                ·
                  refine ⟨8587901415914775276683725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45802140884878801475646533 8587901415914775276683725)
                  ·
                    refine ⟨3220463030968040728756397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8587901415914775276683725 3220463030968040728756397)
                    ·
                      refine ⟨1207673636613015273283649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3220463030968040728756397 1207673636613015273283649)
                      ·
                        rfl

theorem cell23_2351936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_2351936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351936 prefixEnd_2351936 := by exact prefixLift 2351936
  have htrace : WordTrace (prefixWord ++ tailWord_2351936) baseStart_2351936 baseEnd_2351936 := by
    simpa [prefixWord, tailWord_2351936, baseEnd_2351936] using wordTrace_append hprefix tailTrace_2351936
  have hstable : (prefixWord ++ tailWord_2351936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351936).length < 2 ^ (prefixWord ++ tailWord_2351936).sum := by decide
  have hdescent : baseEnd_2351936 < baseStart_2351936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351990 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_2351990 : Nat := 118140960795 + 2351990 * 2 ^ 59
def prefixEnd_2351990 : Nat := 4983230072969 + 3 ^ 40 * 2351990 * 2
def baseEnd_2351990 : Nat := 402567121522786020669467

theorem tailTrace_2351990 : CollatzResearch.WordTrace tailWord_2351990 prefixEnd_2351990 402567121522786020669467 := by
  unfold tailWord_2351990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361507671821837047318839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57189415166099595171400949 5361507671821837047318839)
  ·
    refine ⟨8042261507732755570978259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5361507671821837047318839 8042261507732755570978259)
    ·
      refine ⟨12063392261599133356467389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8042261507732755570978259 12063392261599133356467389)
      ·
        refine ⟨4523772098099675008675271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12063392261599133356467389 4523772098099675008675271)
        ·
          refine ⟨6785658147149512513012907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523772098099675008675271 6785658147149512513012907)
          ·
            refine ⟨10178487220724268769519361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6785658147149512513012907 10178487220724268769519361)
            ·
              refine ⟨7633865415543201577139521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10178487220724268769519361 7633865415543201577139521)
              ·
                refine ⟨5725399061657401182854641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7633865415543201577139521 5725399061657401182854641)
                ·
                  refine ⟨4294049296243050887140981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5725399061657401182854641 4294049296243050887140981)
                  ·
                    refine ⟨402567121522786020669467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4294049296243050887140981 402567121522786020669467)
                    ·
                      rfl

theorem cell23_2351990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_2351990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351990 prefixEnd_2351990 := by exact prefixLift 2351990
  have htrace : WordTrace (prefixWord ++ tailWord_2351990) baseStart_2351990 baseEnd_2351990 := by
    simpa [prefixWord, tailWord_2351990, baseEnd_2351990] using wordTrace_append hprefix tailTrace_2351990
  have hstable : (prefixWord ++ tailWord_2351990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351990).length < 2 ^ (prefixWord ++ tailWord_2351990).sum := by decide
  have hdescent : baseEnd_2351990 < baseStart_2351990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351993 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 4]
def baseStart_2351993 : Nat := 118140960795 + 2351993 * 2 ^ 59
def prefixEnd_2351993 : Nat := 4983230072969 + 3 ^ 40 * 2351993 * 2
def baseEnd_2351993 : Nat := 1207702905010321550270887

theorem tailTrace_2351993 : CollatzResearch.WordTrace tailWord_2351993 prefixEnd_2351993 1207702905010321550270887 := by
  unfold tailWord_2351993
  simp only [CollatzResearch.WordTrace]
  refine ⟨85784232168138524269460633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57189488112092349512973755 85784232168138524269460633)
  ·
    refine ⟨64338174126103893202095475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85784232168138524269460633 64338174126103893202095475)
    ·
      refine ⟨96507261189155839803143213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64338174126103893202095475 96507261189155839803143213)
      ·
        refine ⟨36190222945933439926178705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96507261189155839803143213 36190222945933439926178705)
        ·
          refine ⟨27142667209450079944634029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36190222945933439926178705 27142667209450079944634029)
          ·
            refine ⟨10178500203543779979237761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27142667209450079944634029 10178500203543779979237761)
            ·
              refine ⟨7633875152657834984428321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10178500203543779979237761 7633875152657834984428321)
              ·
                refine ⟨5725406364493376238321241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7633875152657834984428321 5725406364493376238321241)
                ·
                  refine ⟨4294054773370032178740931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5725406364493376238321241 4294054773370032178740931)
                  ·
                    refine ⟨6441082160055048268111397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4294054773370032178740931 6441082160055048268111397)
                    ·
                      refine ⟨1207702905010321550270887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6441082160055048268111397 1207702905010321550270887)
                      ·
                        rfl

theorem cell23_2351993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_2351993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2351993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2351993 prefixEnd_2351993 := by exact prefixLift 2351993
  have htrace : WordTrace (prefixWord ++ tailWord_2351993) baseStart_2351993 baseEnd_2351993 := by
    simpa [prefixWord, tailWord_2351993, baseEnd_2351993] using wordTrace_append hprefix tailTrace_2351993
  have hstable : (prefixWord ++ tailWord_2351993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351993).length < 2 ^ (prefixWord ++ tailWord_2351993).sum := by decide
  have hdescent : baseEnd_2351993 < baseStart_2351993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352003 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 3, 4]
def baseStart_2352003 : Nat := 118140960795 + 2352003 * 2 ^ 59
def prefixEnd_2352003 : Nat := 4983230072969 + 3 ^ 40 * 2352003 * 2
def baseEnd_2352003 : Nat := 402569346605622170381947

theorem tailTrace_2352003 : CollatzResearch.WordTrace tailWord_2352003 prefixEnd_2352003 402569346605622170381947 := by
  unfold tailWord_2352003
  simp only [CollatzResearch.WordTrace]
  refine ⟨85784596898102295977324663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57189731265401530651549775 85784596898102295977324663)
  ·
    refine ⟨128676895347153443965986995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85784596898102295977324663 128676895347153443965986995)
    ·
      refine ⟨193015343020730165948980493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128676895347153443965986995 193015343020730165948980493)
      ·
        refine ⟨72380753632773812230867685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193015343020730165948980493 72380753632773812230867685)
        ·
          refine ⟨13571391306145089793287691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72380753632773812230867685 13571391306145089793287691)
          ·
            refine ⟨20357086959217634689931537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13571391306145089793287691 20357086959217634689931537)
            ·
              refine ⟨15267815219413226017448653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20357086959217634689931537 15267815219413226017448653)
              ·
                refine ⟨5725430707279959756543245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15267815219413226017448653 5725430707279959756543245)
                ·
                  refine ⟨2147036515229984908703717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5725430707279959756543245 2147036515229984908703717)
                  ·
                    refine ⟨402569346605622170381947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2147036515229984908703717 402569346605622170381947)
                    ·
                      rfl

theorem cell23_2352003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 4].length) (baseStart_2352003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352003 prefixEnd_2352003 := by exact prefixLift 2352003
  have htrace : WordTrace (prefixWord ++ tailWord_2352003) baseStart_2352003 baseEnd_2352003 := by
    simpa [prefixWord, tailWord_2352003, baseEnd_2352003] using wordTrace_append hprefix tailTrace_2352003
  have hstable : (prefixWord ++ tailWord_2352003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352003).length < 2 ^ (prefixWord ++ tailWord_2352003).sum := by decide
  have hdescent : baseEnd_2352003 < baseStart_2352003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352010 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2]
def baseStart_2352010 : Nat := 118140960795 + 2352010 * 2 ^ 59
def prefixEnd_2352010 : Nat := 4983230072969 + 3 ^ 40 * 2352010 * 2
def baseEnd_2352010 : Nat := 1207711634181447983758309

theorem tailTrace_2352010 : CollatzResearch.WordTrace tailWord_2352010 prefixEnd_2352010 1207711634181447983758309 := by
  unfold tailWord_2352010
  simp only [CollatzResearch.WordTrace]
  refine ⟨21446213052269234043207371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57189901472717957448552989 21446213052269234043207371)
  ·
    refine ⟨32169319578403851064811057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21446213052269234043207371 32169319578403851064811057)
    ·
      refine ⟨24126989683802888298608293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32169319578403851064811057 24126989683802888298608293)
      ·
        refine ⟨4523810565713041555989055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24126989683802888298608293 4523810565713041555989055)
        ·
          refine ⟨6785715848569562333983583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523810565713041555989055 6785715848569562333983583)
          ·
            refine ⟨10178573772854343500975375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6785715848569562333983583 10178573772854343500975375)
            ·
              refine ⟨15267860659281515251463063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10178573772854343500975375 15267860659281515251463063)
              ·
                refine ⟨22901790988922272877194595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15267860659281515251463063 22901790988922272877194595)
                ·
                  refine ⟨34352686483383409315791893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22901790988922272877194595 34352686483383409315791893)
                  ·
                    refine ⟨1610282178908597311677745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34352686483383409315791893 1610282178908597311677745)
                    ·
                      refine ⟨1207711634181447983758309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1610282178908597311677745 1207711634181447983758309)
                      ·
                        rfl

theorem cell23_2352010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_2352010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352010 prefixEnd_2352010 := by exact prefixLift 2352010
  have htrace : WordTrace (prefixWord ++ tailWord_2352010) baseStart_2352010 baseEnd_2352010 := by
    simpa [prefixWord, tailWord_2352010, baseEnd_2352010] using wordTrace_append hprefix tailTrace_2352010
  have hstable : (prefixWord ++ tailWord_2352010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352010).length < 2 ^ (prefixWord ++ tailWord_2352010).sum := by decide
  have hdescent : baseEnd_2352010 < baseStart_2352010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352020 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2352020 : Nat := 118140960795 + 2352020 * 2 ^ 59
def prefixEnd_2352020 : Nat := 4983230072969 + 3 ^ 40 * 2352020 * 2
def baseEnd_2352020 : Nat := 402572256329330981544421

theorem tailTrace_2352020 : CollatzResearch.WordTrace tailWord_2352020 prefixEnd_2352020 402572256329330981544421 := by
  unfold tailWord_2352020
  simp only [CollatzResearch.WordTrace]
  refine ⟨42892608469520353940346757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57190144626027138587129009 42892608469520353940346757)
  ·
    refine ⟨8042364088035066363815017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42892608469520353940346757 8042364088035066363815017)
    ·
      refine ⟨6031773066026299772861263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8042364088035066363815017 6031773066026299772861263)
      ·
        refine ⟨9047659599039449659291895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6031773066026299772861263 9047659599039449659291895)
        ·
          refine ⟨13571489398559174488937843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9047659599039449659291895 13571489398559174488937843)
          ·
            refine ⟨20357234097838761733406765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13571489398559174488937843 20357234097838761733406765)
            ·
              refine ⟨7633962786689535650027537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20357234097838761733406765 7633962786689535650027537)
              ·
                refine ⟨5725472090017151737520653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7633962786689535650027537 5725472090017151737520653)
                ·
                  refine ⟨2147052033756431901570245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5725472090017151737520653 2147052033756431901570245)
                  ·
                    refine ⟨402572256329330981544421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2147052033756431901570245 402572256329330981544421)
                    ·
                      rfl

theorem cell23_2352020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2352020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352020 prefixEnd_2352020 := by exact prefixLift 2352020
  have htrace : WordTrace (prefixWord ++ tailWord_2352020) baseStart_2352020 baseEnd_2352020 := by
    simpa [prefixWord, tailWord_2352020, baseEnd_2352020] using wordTrace_append hprefix tailTrace_2352020
  have hstable : (prefixWord ++ tailWord_2352020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352020).length < 2 ^ (prefixWord ++ tailWord_2352020).sum := by decide
  have hdescent : baseEnd_2352020 < baseStart_2352020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352113 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_2352113 : Nat := 118140960795 + 2352113 * 2 ^ 59
def prefixEnd_2352113 : Nat := 4983230072969 + 3 ^ 40 * 2352113 * 2
def baseEnd_2352113 : Nat := 1207764522688861080770335

theorem tailTrace_2352113 : CollatzResearch.WordTrace tailWord_2352113 prefixEnd_2352113 1207764522688861080770335 := by
  unfold tailWord_2352113
  simp only [CollatzResearch.WordTrace]
  refine ⟨85788608927703784763828993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57192405951802523175885995 85788608927703784763828993)
  ·
    refine ⟨64341456695777838572871745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85788608927703784763828993 64341456695777838572871745)
    ·
      refine ⟨48256092521833378929653809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64341456695777838572871745 48256092521833378929653809)
      ·
        refine ⟨36192069391375034197240357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48256092521833378929653809 36192069391375034197240357)
        ·
          refine ⟨6786013010882818911982567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36192069391375034197240357 6786013010882818911982567)
          ·
            refine ⟨10179019516324228367973851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6786013010882818911982567 10179019516324228367973851)
            ·
              refine ⟨15268529274486342551960777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10179019516324228367973851 15268529274486342551960777)
              ·
                refine ⟨11451396955864756913970583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15268529274486342551960777 11451396955864756913970583)
                ·
                  refine ⟨17177095433797135370955875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11451396955864756913970583 17177095433797135370955875)
                  ·
                    refine ⟨25765643150695703056433813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17177095433797135370955875 25765643150695703056433813)
                    ·
                      refine ⟨1207764522688861080770335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25765643150695703056433813 1207764522688861080770335)
                      ·
                        rfl

theorem cell23_2352113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_2352113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352113 prefixEnd_2352113 := by exact prefixLift 2352113
  have htrace : WordTrace (prefixWord ++ tailWord_2352113) baseStart_2352113 baseEnd_2352113 := by
    simpa [prefixWord, tailWord_2352113, baseEnd_2352113] using wordTrace_append hprefix tailTrace_2352113
  have hstable : (prefixWord ++ tailWord_2352113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352113).length < 2 ^ (prefixWord ++ tailWord_2352113).sum := by decide
  have hdescent : baseEnd_2352113 < baseStart_2352113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352203 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 4]
def baseStart_2352203 : Nat := 118140960795 + 2352203 * 2 ^ 59
def prefixEnd_2352203 : Nat := 4983230072969 + 3 ^ 40 * 2352203 * 2
def baseEnd_2352203 : Nat := 1207810735947765728644921

theorem tailTrace_2352203 : CollatzResearch.WordTrace tailWord_2352203 prefixEnd_2352203 1207810735947765728644921 := by
  unfold tailWord_2352203
  simp only [CollatzResearch.WordTrace]
  refine ⟨85791891497377730134605263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57194594331585153423070175 85791891497377730134605263)
  ·
    refine ⟨128687837246066595201907895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85791891497377730134605263 128687837246066595201907895)
    ·
      refine ⟨193031755869099892802861843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128687837246066595201907895 193031755869099892802861843)
      ·
        refine ⟨289547633803649839204292765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193031755869099892802861843 289547633803649839204292765)
        ·
          refine ⟨108580362676368689701609787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289547633803649839204292765 108580362676368689701609787)
          ·
            refine ⟨162870544014553034552414681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108580362676368689701609787 162870544014553034552414681)
            ·
              refine ⟨122152908010914775914311011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162870544014553034552414681 122152908010914775914311011)
              ·
                refine ⟨183229362016372163871466517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122152908010914775914311011 183229362016372163871466517)
                ·
                  refine ⟨8588876344517445181474993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 183229362016372163871466517 8588876344517445181474993)
                  ·
                    refine ⟨6441657258388083886106245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8588876344517445181474993 6441657258388083886106245)
                    ·
                      refine ⟨1207810735947765728644921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6441657258388083886106245 1207810735947765728644921)
                      ·
                        rfl

theorem cell23_2352203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 4].length) (baseStart_2352203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352203 prefixEnd_2352203 := by exact prefixLift 2352203
  have htrace : WordTrace (prefixWord ++ tailWord_2352203) baseStart_2352203 baseEnd_2352203 := by
    simpa [prefixWord, tailWord_2352203, baseEnd_2352203] using wordTrace_append hprefix tailTrace_2352203
  have hstable : (prefixWord ++ tailWord_2352203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352203).length < 2 ^ (prefixWord ++ tailWord_2352203).sum := by decide
  have hdescent : baseEnd_2352203 < baseStart_2352203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352213 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 9]
def baseStart_2352213 : Nat := 118140960795 + 2352213 * 2 ^ 59
def prefixEnd_2352213 : Nat := 4983230072969 + 3 ^ 40 * 2352213 * 2
def baseEnd_2352213 : Nat := 134201763417145632168875

theorem tailTrace_2352213 : CollatzResearch.WordTrace tailWord_2352213 prefixEnd_2352213 134201763417145632168875 := by
  unfold tailWord_2352213
  simp only [CollatzResearch.WordTrace]
  refine ⟨85792256227341501842469293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57194837484894334561646195 85792256227341501842469293)
  ·
    refine ⟨32172096085253063190925985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85792256227341501842469293 32172096085253063190925985)
    ·
      refine ⟨24129072063939797393194489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32172096085253063190925985 24129072063939797393194489)
      ·
        refine ⟨18096804047954848044895867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24129072063939797393194489 18096804047954848044895867)
        ·
          refine ⟨27145206071932272067343801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18096804047954848044895867 27145206071932272067343801)
          ·
            refine ⟨20358904553949204050507851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27145206071932272067343801 20358904553949204050507851)
            ·
              refine ⟨30538356830923806075761777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20358904553949204050507851 30538356830923806075761777)
              ·
                refine ⟨22903767623192854556821333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30538356830923806075761777 22903767623192854556821333)
                ·
                  refine ⟨134201763417145632168875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22903767623192854556821333 134201763417145632168875)
                  ·
                    rfl

theorem cell23_2352213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_2352213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352213 prefixEnd_2352213 := by exact prefixLift 2352213
  have htrace : WordTrace (prefixWord ++ tailWord_2352213) baseStart_2352213 baseEnd_2352213 := by
    simpa [prefixWord, tailWord_2352213, baseEnd_2352213] using wordTrace_append hprefix tailTrace_2352213
  have hstable : (prefixWord ++ tailWord_2352213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352213).length < 2 ^ (prefixWord ++ tailWord_2352213).sum := by decide
  have hdescent : baseEnd_2352213 < baseStart_2352213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352220 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2352220 : Nat := 118140960795 + 2352220 * 2 ^ 59
def prefixEnd_2352220 : Nat := 4983230072969 + 3 ^ 40 * 2352220 * 2
def baseEnd_2352220 : Nat := 1207819465118892162132343

theorem tailTrace_2352220 : CollatzResearch.WordTrace tailWord_2352220 prefixEnd_2352220 1207819465118892162132343 := by
  unfold tailWord_2352220
  simp only [CollatzResearch.WordTrace]
  refine ⟨42896255769158071018987057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57195007692210761358649409 42896255769158071018987057)
  ·
    refine ⟨32172191826868553264240293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42896255769158071018987057 32172191826868553264240293)
    ·
      refine ⟨6032285967537853737045055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32172191826868553264240293 6032285967537853737045055)
      ·
        refine ⟨9048428951306780605567583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6032285967537853737045055 9048428951306780605567583)
        ·
          refine ⟨13572643426960170908351375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9048428951306780605567583 13572643426960170908351375)
          ·
            refine ⟨20358965140440256362527063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13572643426960170908351375 20358965140440256362527063)
            ·
              refine ⟨30538447710660384543790595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20358965140440256362527063 30538447710660384543790595)
              ·
                refine ⟨45807671565990576815685893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30538447710660384543790595 45807671565990576815685893)
                ·
                  refine ⟨8588938418623233152941105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45807671565990576815685893 8588938418623233152941105)
                  ·
                    refine ⟨6441703813967424864705829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8588938418623233152941105 6441703813967424864705829)
                    ·
                      refine ⟨1207819465118892162132343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6441703813967424864705829 1207819465118892162132343)
                      ·
                        rfl

theorem cell23_2352220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2352220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352220 prefixEnd_2352220 := by exact prefixLift 2352220
  have htrace : WordTrace (prefixWord ++ tailWord_2352220) baseStart_2352220 baseEnd_2352220 := by
    simpa [prefixWord, tailWord_2352220, baseEnd_2352220] using wordTrace_append hprefix tailTrace_2352220
  have hstable : (prefixWord ++ tailWord_2352220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352220).length < 2 ^ (prefixWord ++ tailWord_2352220).sum := by decide
  have hdescent : baseEnd_2352220 < baseStart_2352220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352240 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 3]
def baseStart_2352240 : Nat := 118140960795 + 2352240 * 2 ^ 59
def prefixEnd_2352240 : Nat := 4983230072969 + 3 ^ 40 * 2352240 * 2
def baseEnd_2352240 : Nat := 1207829734731982083882251

theorem tailTrace_2352240 : CollatzResearch.WordTrace tailWord_2352240 prefixEnd_2352240 1207829734731982083882251 := by
  unfold tailWord_2352240
  simp only [CollatzResearch.WordTrace]
  refine ⟨42896620499121842726851087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57195493998829123635801449 42896620499121842726851087)
  ·
    refine ⟨64344930748682764090276631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42896620499121842726851087 64344930748682764090276631)
    ·
      refine ⟨96517396123024146135414947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64344930748682764090276631 96517396123024146135414947)
      ·
        refine ⟨144776094184536219203122421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96517396123024146135414947 144776094184536219203122421)
        ·
          refine ⟨13572758829800270550292727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144776094184536219203122421 13572758829800270550292727)
          ·
            refine ⟨20359138244700405825439091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13572758829800270550292727 20359138244700405825439091)
            ·
              refine ⟨30538707367050608738158637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20359138244700405825439091 30538707367050608738158637)
              ·
                refine ⟨11452015262643978276809489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30538707367050608738158637 11452015262643978276809489)
                ·
                  refine ⟨8589011446982983707607117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11452015262643978276809489 8589011446982983707607117)
                  ·
                    refine ⟨3220879292618618890352669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8589011446982983707607117 3220879292618618890352669)
                    ·
                      refine ⟨1207829734731982083882251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3220879292618618890352669 1207829734731982083882251)
                      ·
                        rfl

theorem cell23_2352240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 3].length) (baseStart_2352240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352240 prefixEnd_2352240 := by exact prefixLift 2352240
  have htrace : WordTrace (prefixWord ++ tailWord_2352240) baseStart_2352240 baseEnd_2352240 := by
    simpa [prefixWord, tailWord_2352240, baseEnd_2352240] using wordTrace_append hprefix tailTrace_2352240
  have hstable : (prefixWord ++ tailWord_2352240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352240).length < 2 ^ (prefixWord ++ tailWord_2352240).sum := by decide
  have hdescent : baseEnd_2352240 < baseStart_2352240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352260 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_2352260 : Nat := 118140960795 + 2352260 * 2 ^ 59
def prefixEnd_2352260 : Nat := 4983230072969 + 3 ^ 40 * 2352260 * 2
def baseEnd_2352260 : Nat := 402613334781690668544053

theorem tailTrace_2352260 : CollatzResearch.WordTrace tailWord_2352260 prefixEnd_2352260 402613334781690668544053 := by
  unfold tailWord_2352260
  simp only [CollatzResearch.WordTrace]
  refine ⟨42896985229085614434715117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57195980305447485912953489 42896985229085614434715117)
  ·
    refine ⟨16086369460907105413018169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42896985229085614434715117 16086369460907105413018169)
    ·
      refine ⟨12064777095680329059763627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16086369460907105413018169 12064777095680329059763627)
      ·
        refine ⟨18097165643520493589645441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12064777095680329059763627 18097165643520493589645441)
        ·
          refine ⟨13572874232640370192234081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18097165643520493589645441 13572874232640370192234081)
          ·
            refine ⟨10179655674480277644175561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13572874232640370192234081 10179655674480277644175561)
            ·
              refine ⟨7634741755860208233131671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10179655674480277644175561 7634741755860208233131671)
              ·
                refine ⟨11452112633790312349697507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7634741755860208233131671 11452112633790312349697507)
                ·
                  refine ⟨17178168950685468524546261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11452112633790312349697507 17178168950685468524546261)
                  ·
                    refine ⟨402613334781690668544053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17178168950685468524546261 402613334781690668544053)
                    ·
                      rfl

theorem cell23_2352260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_2352260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352260 prefixEnd_2352260 := by exact prefixLift 2352260
  have htrace : WordTrace (prefixWord ++ tailWord_2352260) baseStart_2352260 baseEnd_2352260 := by
    simpa [prefixWord, tailWord_2352260, baseEnd_2352260] using wordTrace_append hprefix tailTrace_2352260
  have hstable : (prefixWord ++ tailWord_2352260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352260).length < 2 ^ (prefixWord ++ tailWord_2352260).sum := by decide
  have hdescent : baseEnd_2352260 < baseStart_2352260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352287 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2352287 : Nat := 118140960795 + 2352287 * 2 ^ 59
def prefixEnd_2352287 : Nat := 4983230072969 + 3 ^ 40 * 2352287 * 2
def baseEnd_2352287 : Nat := 1207853868322743399994535

theorem tailTrace_2352287 : CollatzResearch.WordTrace tailWord_2352287 prefixEnd_2352287 1207853868322743399994535 := by
  unfold tailWord_2352287
  simp only [CollatzResearch.WordTrace]
  refine ⟨85794955229073412480663115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57196636819382274987108743 85794955229073412480663115)
  ·
    refine ⟨128692432843610118720994673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85794955229073412480663115 128692432843610118720994673)
    ·
      refine ⟨96519324632707589040746005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128692432843610118720994673 96519324632707589040746005)
      ·
        refine ⟨4524343342158168236284969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96519324632707589040746005 4524343342158168236284969)
        ·
          refine ⟨3393257506618626177213727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4524343342158168236284969 3393257506618626177213727)
          ·
            refine ⟨5089886259927939265820591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393257506618626177213727 5089886259927939265820591)
            ·
              refine ⟨7634829389891908898730887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5089886259927939265820591 7634829389891908898730887)
              ·
                refine ⟨11452244084837863348096331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7634829389891908898730887 11452244084837863348096331)
                ·
                  refine ⟨17178366127256795022144497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11452244084837863348096331 17178366127256795022144497)
                  ·
                    refine ⟨12883774595442596266608373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17178366127256795022144497 12883774595442596266608373)
                    ·
                      refine ⟨1207853868322743399994535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12883774595442596266608373 1207853868322743399994535)
                      ·
                        rfl

theorem cell23_2352287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2352287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352287 prefixEnd_2352287 := by exact prefixLift 2352287
  have htrace : WordTrace (prefixWord ++ tailWord_2352287) baseStart_2352287 baseEnd_2352287 := by
    simpa [prefixWord, tailWord_2352287, baseEnd_2352287] using wordTrace_append hprefix tailTrace_2352287
  have hstable : (prefixWord ++ tailWord_2352287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352287).length < 2 ^ (prefixWord ++ tailWord_2352287).sum := by decide
  have hdescent : baseEnd_2352287 < baseStart_2352287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352300 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 3]
def baseStart_2352300 : Nat := 118140960795 + 2352300 * 2 ^ 59
def prefixEnd_2352300 : Nat := 4983230072969 + 3 ^ 40 * 2352300 * 2
def baseEnd_2352300 : Nat := 1207860543571251849131975

theorem tailTrace_2352300 : CollatzResearch.WordTrace tailWord_2352300 prefixEnd_2352300 1207860543571251849131975 := by
  unfold tailWord_2352300
  simp only [CollatzResearch.WordTrace]
  refine ⟨42897714689013157850443177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57196952918684210467257569 42897714689013157850443177)
  ·
    refine ⟨32173286016759868387832383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42897714689013157850443177 32173286016759868387832383)
    ·
      refine ⟨48259929025139802581748575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32173286016759868387832383 48259929025139802581748575)
      ·
        refine ⟨72389893537709703872622863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48259929025139802581748575 72389893537709703872622863)
        ·
          refine ⟨108584840306564555808934295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72389893537709703872622863 108584840306564555808934295)
          ·
            refine ⟨162877260459846833713401443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108584840306564555808934295 162877260459846833713401443)
            ·
              refine ⟨244315890689770250570102165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162877260459846833713401443 244315890689770250570102165)
              ·
                refine ⟨11452307376082980495473539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 244315890689770250570102165 11452307376082980495473539)
                ·
                  refine ⟨17178461064124470743210309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11452307376082980495473539 17178461064124470743210309)
                  ·
                    refine ⟨3220961449523338264351933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17178461064124470743210309 3220961449523338264351933)
                    ·
                      refine ⟨1207860543571251849131975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3220961449523338264351933 1207860543571251849131975)
                      ·
                        rfl

theorem cell23_2352300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_2352300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352300 prefixEnd_2352300 := by exact prefixLift 2352300
  have htrace : WordTrace (prefixWord ++ tailWord_2352300) baseStart_2352300 baseEnd_2352300 := by
    simpa [prefixWord, tailWord_2352300, baseEnd_2352300] using wordTrace_append hprefix tailTrace_2352300
  have hstable : (prefixWord ++ tailWord_2352300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352300).length < 2 ^ (prefixWord ++ tailWord_2352300).sum := by decide
  have hdescent : baseEnd_2352300 < baseStart_2352300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352317 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_2352317 : Nat := 118140960795 + 2352317 * 2 ^ 59
def prefixEnd_2352317 : Nat := 4983230072969 + 3 ^ 40 * 2352317 * 2
def baseEnd_2352317 : Nat := 1207869272742378282619397

theorem tailTrace_2352317 : CollatzResearch.WordTrace tailWord_2352317 prefixEnd_2352317 1207869272742378282619397 := by
  unfold tailWord_2352317
  simp only [CollatzResearch.WordTrace]
  refine ⟨85796049418964727604255205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57197366279309818402836803 85796049418964727604255205)
  ·
    refine ⟨16086759266055886425797851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85796049418964727604255205 16086759266055886425797851)
    ·
      refine ⟨24130138899083829638696777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16086759266055886425797851 24130138899083829638696777)
      ·
        refine ⟨18097604174312872229022583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24130138899083829638696777 18097604174312872229022583)
        ·
          refine ⟨27146406261469308343533875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18097604174312872229022583 27146406261469308343533875)
          ·
            refine ⟨40719609392203962515300813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27146406261469308343533875 40719609392203962515300813)
            ·
              refine ⟨15269853522076485943237805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40719609392203962515300813 15269853522076485943237805)
              ·
                refine ⟨5726195070778682228714177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15269853522076485943237805 5726195070778682228714177)
                ·
                  refine ⟨4294646303084011671535633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5726195070778682228714177 4294646303084011671535633)
                  ·
                    refine ⟨3220984727313008753651725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4294646303084011671535633 3220984727313008753651725)
                    ·
                      refine ⟨1207869272742378282619397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3220984727313008753651725 1207869272742378282619397)
                      ·
                        rfl

theorem cell23_2352317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_2352317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352317 prefixEnd_2352317 := by exact prefixLift 2352317
  have htrace : WordTrace (prefixWord ++ tailWord_2352317) baseStart_2352317 baseEnd_2352317 := by
    simpa [prefixWord, tailWord_2352317, baseEnd_2352317] using wordTrace_append hprefix tailTrace_2352317
  have hstable : (prefixWord ++ tailWord_2352317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352317).length < 2 ^ (prefixWord ++ tailWord_2352317).sum := by decide
  have hdescent : baseEnd_2352317 < baseStart_2352317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352341 : List Nat := [1, 3, 2, 4, 1, 2, 1, 4, 1, 4]
def baseStart_2352341 : Nat := 118140960795 + 2352341 * 2 ^ 59
def prefixEnd_2352341 : Nat := 4983230072969 + 3 ^ 40 * 2352341 * 2
def baseEnd_2352341 : Nat := 402627198759362062906429

theorem tailTrace_2352341 : CollatzResearch.WordTrace tailWord_2352341 prefixEnd_2352341 402627198759362062906429 := by
  unfold tailWord_2352341
  simp only [CollatzResearch.WordTrace]
  refine ⟨85796924770877779703128877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57197949847251853135419251 85796924770877779703128877)
  ·
    refine ⟨32173846789079167388673329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85796924770877779703128877 32173846789079167388673329)
    ·
      refine ⟨24130385091809375541504997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32173846789079167388673329 24130385091809375541504997)
      ·
        refine ⟨4524447204714257914032187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24130385091809375541504997 4524447204714257914032187)
        ·
          refine ⟨6786670807071386871048281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524447204714257914032187 6786670807071386871048281)
          ·
            refine ⟨5090003105303540153286211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6786670807071386871048281 5090003105303540153286211)
            ·
              refine ⟨7635004657955310229929317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090003105303540153286211 7635004657955310229929317)
              ·
                refine ⟨1431563373366620668111747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7635004657955310229929317 1431563373366620668111747)
                ·
                  refine ⟨2147345060049931002167621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431563373366620668111747 2147345060049931002167621)
                  ·
                    refine ⟨402627198759362062906429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2147345060049931002167621 402627198759362062906429)
                    ·
                      rfl

theorem cell23_2352341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_2352341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352341 prefixEnd_2352341 := by exact prefixLift 2352341
  have htrace : WordTrace (prefixWord ++ tailWord_2352341) baseStart_2352341 baseEnd_2352341 := by
    simpa [prefixWord, tailWord_2352341, baseEnd_2352341] using wordTrace_append hprefix tailTrace_2352341
  have hstable : (prefixWord ++ tailWord_2352341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352341).length < 2 ^ (prefixWord ++ tailWord_2352341).sum := by decide
  have hdescent : baseEnd_2352341 < baseStart_2352341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352360 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_2352360 : Nat := 118140960795 + 2352360 * 2 ^ 59
def prefixEnd_2352360 : Nat := 4983230072969 + 3 ^ 40 * 2352360 * 2
def baseEnd_2352360 : Nat := 1207891352410521614381699

theorem tailTrace_2352360 : CollatzResearch.WordTrace tailWord_2352360 prefixEnd_2352360 1207891352410521614381699 := by
  unfold tailWord_2352360
  simp only [CollatzResearch.WordTrace]
  refine ⟨42898808878904472974035267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57198411838539297298713689 42898808878904472974035267)
  ·
    refine ⟨64348213318356709461052901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42898808878904472974035267 64348213318356709461052901)
    ·
      refine ⟨12065289997191883023947419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64348213318356709461052901 12065289997191883023947419)
      ·
        refine ⟨18097934995787824535921129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12065289997191883023947419 18097934995787824535921129)
        ·
          refine ⟨13573451246840868401940847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18097934995787824535921129 13573451246840868401940847)
          ·
            refine ⟨20360176870261302602911271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13573451246840868401940847 20360176870261302602911271)
            ·
              refine ⟨30540265305391953904366907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20360176870261302602911271 30540265305391953904366907)
              ·
                refine ⟨45810397958087930856550361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30540265305391953904366907 45810397958087930856550361)
                ·
                  refine ⟨34357798468565948142412771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45810397958087930856550361 34357798468565948142412771)
                  ·
                    refine ⟨51536697702848922213619157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34357798468565948142412771 51536697702848922213619157)
                    ·
                      refine ⟨1207891352410521614381699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51536697702848922213619157 1207891352410521614381699)
                      ·
                        rfl

theorem cell23_2352360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_2352360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352360 prefixEnd_2352360 := by exact prefixLift 2352360
  have htrace : WordTrace (prefixWord ++ tailWord_2352360) baseStart_2352360 baseEnd_2352360 := by
    simpa [prefixWord, tailWord_2352360, baseEnd_2352360] using wordTrace_append hprefix tailTrace_2352360
  have hstable : (prefixWord ++ tailWord_2352360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352360).length < 2 ^ (prefixWord ++ tailWord_2352360).sum := by decide
  have hdescent : baseEnd_2352360 < baseStart_2352360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352364 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 3]
def baseStart_2352364 : Nat := 118140960795 + 2352364 * 2 ^ 59
def prefixEnd_2352364 : Nat := 4983230072969 + 3 ^ 40 * 2352364 * 2
def baseEnd_2352364 : Nat := 1207893406333139598731681

theorem tailTrace_2352364 : CollatzResearch.WordTrace tailWord_2352364 prefixEnd_2352364 1207893406333139598731681 := by
  unfold tailWord_2352364
  simp only [CollatzResearch.WordTrace]
  refine ⟨42898881824897227315608073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57198509099862969754144097 42898881824897227315608073)
  ·
    refine ⟨32174161368672920486706055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42898881824897227315608073 32174161368672920486706055)
    ·
      refine ⟨48261242053009380730059083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32174161368672920486706055 48261242053009380730059083)
      ·
        refine ⟨72391863079514071095088625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48261242053009380730059083 72391863079514071095088625)
        ·
          refine ⟨54293897309635553321316469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72391863079514071095088625 54293897309635553321316469)
          ·
            refine ⟨5090052872778333123873419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54293897309635553321316469 5090052872778333123873419)
            ·
              refine ⟨7635079309167499685810129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090052872778333123873419 7635079309167499685810129)
              ·
                refine ⟨5726309481875624764357597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7635079309167499685810129 5726309481875624764357597)
                ·
                  refine ⟨2147366055703359286634099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5726309481875624764357597 2147366055703359286634099)
                  ·
                    refine ⟨3221049083555038929951149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2147366055703359286634099 3221049083555038929951149)
                    ·
                      refine ⟨1207893406333139598731681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3221049083555038929951149 1207893406333139598731681)
                      ·
                        rfl

theorem cell23_2352364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_2352364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352364 prefixEnd_2352364 := by exact prefixLift 2352364
  have htrace : WordTrace (prefixWord ++ tailWord_2352364) baseStart_2352364 baseEnd_2352364 := by
    simpa [prefixWord, tailWord_2352364, baseEnd_2352364] using wordTrace_append hprefix tailTrace_2352364
  have hstable : (prefixWord ++ tailWord_2352364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352364).length < 2 ^ (prefixWord ++ tailWord_2352364).sum := by decide
  have hdescent : baseEnd_2352364 < baseStart_2352364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352407 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2352407 : Nat := 118140960795 + 2352407 * 2 ^ 59
def prefixEnd_2352407 : Nat := 4983230072969 + 3 ^ 40 * 2352407 * 2
def baseEnd_2352407 : Nat := 1207915486001282930493983

theorem tailTrace_2352407 : CollatzResearch.WordTrace tailWord_2352407 prefixEnd_2352407 1207915486001282930493983 := by
  unfold tailWord_2352407
  simp only [CollatzResearch.WordTrace]
  refine ⟨85799331988638672975031475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57199554659092448650020983 85799331988638672975031475)
  ·
    refine ⟨128698997982958009462547213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85799331988638672975031475 128698997982958009462547213)
    ·
      refine ⟨48262124243609253548455205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128698997982958009462547213 48262124243609253548455205)
      ·
        refine ⟨9049148295676735040335351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48262124243609253548455205 9049148295676735040335351)
        ·
          refine ⟨13573722443515102560503027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9049148295676735040335351 13573722443515102560503027)
          ·
            refine ⟨20360583665272653840754541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13573722443515102560503027 20360583665272653840754541)
            ·
              refine ⟨7635218874477245190282953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20360583665272653840754541 7635218874477245190282953)
              ·
                refine ⟨5726414155857933892712215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7635218874477245190282953 5726414155857933892712215)
                ·
                  refine ⟨8589621233786900839068323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5726414155857933892712215 8589621233786900839068323)
                  ·
                    refine ⟨12884431850680351258602485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8589621233786900839068323 12884431850680351258602485)
                    ·
                      refine ⟨1207915486001282930493983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12884431850680351258602485 1207915486001282930493983)
                      ·
                        rfl

theorem cell23_2352407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2352407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352407 prefixEnd_2352407 := by exact prefixLift 2352407
  have htrace : WordTrace (prefixWord ++ tailWord_2352407) baseStart_2352407 baseEnd_2352407 := by
    simpa [prefixWord, tailWord_2352407, baseEnd_2352407] using wordTrace_append hprefix tailTrace_2352407
  have hstable : (prefixWord ++ tailWord_2352407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352407).length < 2 ^ (prefixWord ++ tailWord_2352407).sum := by decide
  have hdescent : baseEnd_2352407 < baseStart_2352407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352421 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 3, 2, 2]
def baseStart_2352421 : Nat := 118140960795 + 2352421 * 2 ^ 59
def prefixEnd_2352421 : Nat := 4983230072969 + 3 ^ 40 * 2352421 * 2
def baseEnd_2352421 : Nat := 1207922674730445875718919

theorem tailTrace_2352421 : CollatzResearch.WordTrace tailWord_2352421 prefixEnd_2352421 1207922674730445875718919 := by
  unfold tailWord_2352421
  simp only [CollatzResearch.WordTrace]
  refine ⟨85799842610587953366041117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57199895073725302244027411 85799842610587953366041117)
  ·
    refine ⟨32174940978970482512265419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85799842610587953366041117 32174940978970482512265419)
    ·
      refine ⟨48262411468455723768398129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32174940978970482512265419 48262411468455723768398129)
      ·
        refine ⟨36196808601341792826298597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48262411468455723768398129 36196808601341792826298597)
        ·
          refine ⟨6786901612751586154930987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36196808601341792826298597 6786901612751586154930987)
          ·
            refine ⟨10180352419127379232396481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6786901612751586154930987 10180352419127379232396481)
            ·
              refine ⟨7635264314345534424297361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10180352419127379232396481 7635264314345534424297361)
              ·
                refine ⟨5726448235759150818223021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7635264314345534424297361 5726448235759150818223021)
                ·
                  refine ⟨2147418088409681556833633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5726448235759150818223021 2147418088409681556833633)
                  ·
                    refine ⟨1610563566307261167625225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2147418088409681556833633 1610563566307261167625225)
                    ·
                      refine ⟨1207922674730445875718919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1610563566307261167625225 1207922674730445875718919)
                      ·
                        rfl

theorem cell23_2352421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_2352421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352421 prefixEnd_2352421 := by exact prefixLift 2352421
  have htrace : WordTrace (prefixWord ++ tailWord_2352421) baseStart_2352421 baseEnd_2352421 := by
    simpa [prefixWord, tailWord_2352421, baseEnd_2352421] using wordTrace_append hprefix tailTrace_2352421
  have hstable : (prefixWord ++ tailWord_2352421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352421).length < 2 ^ (prefixWord ++ tailWord_2352421).sum := by decide
  have hdescent : baseEnd_2352421 < baseStart_2352421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352440 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 1, 9]
def baseStart_2352440 : Nat := 118140960795 + 2352440 * 2 ^ 59
def prefixEnd_2352440 : Nat := 4983230072969 + 3 ^ 40 * 2352440 * 2
def baseEnd_2352440 : Nat := 402644143620960433793777

theorem tailTrace_2352440 : CollatzResearch.WordTrace tailWord_2352440 prefixEnd_2352440 402644143620960433793777 := by
  unfold tailWord_2352440
  simp only [CollatzResearch.WordTrace]
  refine ⟨42900267798759559805491387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57200357065012746407321849 42900267798759559805491387)
  ·
    refine ⟨64350401698139339708237081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42900267798759559805491387 64350401698139339708237081)
    ·
      refine ⟨48262801273604504781177811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64350401698139339708237081 48262801273604504781177811)
      ·
        refine ⟨72394201910406757171766717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48262801273604504781177811 72394201910406757171766717)
        ·
          refine ⟨27147825716402533939412519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72394201910406757171766717 27147825716402533939412519)
          ·
            refine ⟨40721738574603800909118779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27147825716402533939412519 40721738574603800909118779)
            ·
              refine ⟨61082607861905701363678169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40721738574603800909118779 61082607861905701363678169)
              ·
                refine ⟨45811955896429276022758627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61082607861905701363678169 45811955896429276022758627)
                ·
                  refine ⟨68717933844643914034137941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45811955896429276022758627 68717933844643914034137941)
                  ·
                    refine ⟨402644143620960433793777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 68717933844643914034137941 402644143620960433793777)
                    ·
                      rfl

theorem cell23_2352440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_2352440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352440 prefixEnd_2352440 := by exact prefixLift 2352440
  have htrace : WordTrace (prefixWord ++ tailWord_2352440) baseStart_2352440 baseEnd_2352440 := by
    simpa [prefixWord, tailWord_2352440, baseEnd_2352440] using wordTrace_append hprefix tailTrace_2352440
  have hstable : (prefixWord ++ tailWord_2352440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352440).length < 2 ^ (prefixWord ++ tailWord_2352440).sum := by decide
  have hdescent : baseEnd_2352440 < baseStart_2352440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352455 : List Nat := [1, 1, 4, 1, 2, 4, 3, 2, 1, 2, 2]
def baseStart_2352455 : Nat := 118140960795 + 2352455 * 2 ^ 59
def prefixEnd_2352455 : Nat := 4983230072969 + 3 ^ 40 * 2352455 * 2
def baseEnd_2352455 : Nat := 1207940133072698742693763

theorem tailTrace_2352455 : CollatzResearch.WordTrace tailWord_2352455 prefixEnd_2352455 1207940133072698742693763 := by
  unfold tailWord_2352455
  simp only [CollatzResearch.WordTrace]
  refine ⟨85801082692464777172778819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57200721794976518115185879 85801082692464777172778819)
  ·
    refine ⟨128701624038697165759168229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85801082692464777172778819 128701624038697165759168229)
    ·
      refine ⟨24131554507255718579844043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128701624038697165759168229 24131554507255718579844043)
      ·
        refine ⟨36197331760883577869766065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24131554507255718579844043 36197331760883577869766065)
        ·
          refine ⟨27147998820662683402324549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36197331760883577869766065 27147998820662683402324549)
          ·
            refine ⟨5090249778874253137935853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27147998820662683402324549 5090249778874253137935853)
            ·
              refine ⟨1908843667077844926725945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5090249778874253137935853 1908843667077844926725945)
              ·
                refine ⟨1431632750308383695044459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1908843667077844926725945 1431632750308383695044459)
                ·
                  refine ⟨2147449125462575542566689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431632750308383695044459 2147449125462575542566689)
                  ·
                    refine ⟨1610586844096931656925017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2147449125462575542566689 1610586844096931656925017)
                    ·
                      refine ⟨1207940133072698742693763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1610586844096931656925017 1207940133072698742693763)
                      ·
                        rfl

theorem cell23_2352455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_2352455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352455 prefixEnd_2352455 := by exact prefixLift 2352455
  have htrace : WordTrace (prefixWord ++ tailWord_2352455) baseStart_2352455 baseEnd_2352455 := by
    simpa [prefixWord, tailWord_2352455, baseEnd_2352455] using wordTrace_append hprefix tailTrace_2352455
  have hstable : (prefixWord ++ tailWord_2352455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352455).length < 2 ^ (prefixWord ++ tailWord_2352455).sum := by decide
  have hdescent : baseEnd_2352455 < baseStart_2352455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352461 : List Nat := [1, 6, 1, 3, 1, 1, 2, 8]
def baseStart_2352461 : Nat := 118140960795 + 2352461 * 2 ^ 59
def prefixEnd_2352461 : Nat := 4983230072969 + 3 ^ 40 * 2352461 * 2
def baseEnd_2352461 : Nat := 44738637553949100711805

theorem tailTrace_2352461 : CollatzResearch.WordTrace tailWord_2352461 prefixEnd_2352461 44738637553949100711805 := by
  unfold tailWord_2352461
  simp only [CollatzResearch.WordTrace]
  refine ⟨85801301530443040197497237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57200867686962026798331491 85801301530443040197497237)
  ·
    refine ⟨4021936009239517509257683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85801301530443040197497237 4021936009239517509257683)
    ·
      refine ⟨6032904013859276263886525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4021936009239517509257683 6032904013859276263886525)
      ·
        refine ⟨2262339005197228598957447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6032904013859276263886525 2262339005197228598957447)
        ·
          refine ⟨3393508507795842898436171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262339005197228598957447 3393508507795842898436171)
          ·
            refine ⟨5090262761693764347654257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393508507795842898436171 5090262761693764347654257)
            ·
              refine ⟨3817697071270323260740693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5090262761693764347654257 3817697071270323260740693)
              ·
                refine ⟨44738637553949100711805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3817697071270323260740693 44738637553949100711805)
                ·
                  rfl

theorem cell23_2352461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 8].length) (baseStart_2352461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352461 prefixEnd_2352461 := by exact prefixLift 2352461
  have htrace : WordTrace (prefixWord ++ tailWord_2352461) baseStart_2352461 baseEnd_2352461 := by
    simpa [prefixWord, tailWord_2352461, baseEnd_2352461] using wordTrace_append hprefix tailTrace_2352461
  have hstable : (prefixWord ++ tailWord_2352461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352461).length < 2 ^ (prefixWord ++ tailWord_2352461).sum := by decide
  have hdescent : baseEnd_2352461 < baseStart_2352461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352464 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 3, 3, 2]
def baseStart_2352464 : Nat := 118140960795 + 2352464 * 2 ^ 59
def prefixEnd_2352464 : Nat := 4983230072969 + 3 ^ 40 * 2352464 * 2
def baseEnd_2352464 : Nat := 1207944754398589207481221

theorem tailTrace_2352464 : CollatzResearch.WordTrace tailWord_2352464 prefixEnd_2352464 1207944754398589207481221 := by
  unfold tailWord_2352464
  simp only [CollatzResearch.WordTrace]
  refine ⟨42900705474716085854928223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57200940632954781139904297 42900705474716085854928223)
  ·
    refine ⟨64351058212074128782392335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42900705474716085854928223 64351058212074128782392335)
    ·
      refine ⟨96526587318111193173588503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64351058212074128782392335 96526587318111193173588503)
      ·
        refine ⟨144789880977166789760382755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96526587318111193173588503 144789880977166789760382755)
        ·
          refine ⟨217184821465750184640574133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144789880977166789760382755 217184821465750184640574133)
          ·
            refine ⟨20361077012414079810053825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 217184821465750184640574133 20361077012414079810053825)
            ·
              refine ⟨15270807759310559857540369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20361077012414079810053825 15270807759310559857540369)
              ·
                refine ⟨11453105819482919893155277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15270807759310559857540369 11453105819482919893155277)
                ·
                  refine ⟨4294914682306094959933229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11453105819482919893155277 4294914682306094959933229)
                  ·
                    refine ⟨1610593005864785609974961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4294914682306094959933229 1610593005864785609974961)
                    ·
                      refine ⟨1207944754398589207481221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1610593005864785609974961 1207944754398589207481221)
                      ·
                        rfl

theorem cell23_2352464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 3, 2].length) (baseStart_2352464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352464 prefixEnd_2352464 := by exact prefixLift 2352464
  have htrace : WordTrace (prefixWord ++ tailWord_2352464) baseStart_2352464 baseEnd_2352464 := by
    simpa [prefixWord, tailWord_2352464, baseEnd_2352464] using wordTrace_append hprefix tailTrace_2352464
  have hstable : (prefixWord ++ tailWord_2352464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352464).length < 2 ^ (prefixWord ++ tailWord_2352464).sum := by decide
  have hdescent : baseEnd_2352464 < baseStart_2352464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352471 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 2, 1, 3]
def baseStart_2352471 : Nat := 118140960795 + 2352471 * 2 ^ 59
def prefixEnd_2352471 : Nat := 4983230072969 + 3 ^ 40 * 2352471 * 2
def baseEnd_2352471 : Nat := 1207948348763170680093689

theorem tailTrace_2352471 : CollatzResearch.WordTrace tailWord_2352471 prefixEnd_2352471 1207948348763170680093689 := by
  unfold tailWord_2352471
  simp only [CollatzResearch.WordTrace]
  refine ⟨85801666260406811905361267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57201110840271207936907511 85801666260406811905361267)
  ·
    refine ⟨128702499390610217858041901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85801666260406811905361267 128702499390610217858041901)
    ·
      refine ⟨48263437271478831696765713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128702499390610217858041901 48263437271478831696765713)
      ·
        refine ⟨36197577953609123772574285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48263437271478831696765713 36197577953609123772574285)
        ·
          refine ⟨13574091732603421414715357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36197577953609123772574285 13574091732603421414715357)
          ·
            refine ⟨5090284399726283030518259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13574091732603421414715357 5090284399726283030518259)
            ·
              refine ⟨7635426599589424545777389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090284399726283030518259 7635426599589424545777389)
              ·
                refine ⟨2863284974846034204666521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7635426599589424545777389 2863284974846034204666521)
                ·
                  refine ⟨2147463731134525653499891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2863284974846034204666521 2147463731134525653499891)
                  ·
                    refine ⟨3221195596701788480249837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2147463731134525653499891 3221195596701788480249837)
                    ·
                      refine ⟨1207948348763170680093689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3221195596701788480249837 1207948348763170680093689)
                      ·
                        rfl

theorem cell23_2352471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_2352471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352471 prefixEnd_2352471 := by exact prefixLift 2352471
  have htrace : WordTrace (prefixWord ++ tailWord_2352471) baseStart_2352471 baseEnd_2352471 := by
    simpa [prefixWord, tailWord_2352471, baseEnd_2352471] using wordTrace_append hprefix tailTrace_2352471
  have hstable : (prefixWord ++ tailWord_2352471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352471).length < 2 ^ (prefixWord ++ tailWord_2352471).sum := by decide
  have hdescent : baseEnd_2352471 < baseStart_2352471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352497 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_2352497 : Nat := 118140960795 + 2352497 * 2 ^ 59
def prefixEnd_2352497 : Nat := 4983230072969 + 3 ^ 40 * 2352497 * 2
def baseEnd_2352497 : Nat := 1207961699260187578368569

theorem tailTrace_2352497 : CollatzResearch.WordTrace tailWord_2352497 prefixEnd_2352497 1207961699260187578368569 := by
  unfold tailWord_2352497
  simp only [CollatzResearch.WordTrace]
  refine ⟨85802614558312618345807745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57201743038875078897205163 85802614558312618345807745)
  ·
    refine ⟨64351960918734463759355809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85802614558312618345807745 64351960918734463759355809)
    ·
      refine ⟨48263970689050847819516857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64351960918734463759355809 48263970689050847819516857)
      ·
        refine ⟨36197978016788135864637643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48263970689050847819516857 36197978016788135864637643)
        ·
          refine ⟨54296967025182203796956465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36197978016788135864637643 54296967025182203796956465)
          ·
            refine ⟨40722725268886652847717349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54296967025182203796956465 40722725268886652847717349)
            ·
              refine ⟨7635510987916247408947003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40722725268886652847717349 7635510987916247408947003)
              ·
                refine ⟨11453266481874371113420505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635510987916247408947003 11453266481874371113420505)
                ·
                  refine ⟨8589949861405778335065379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11453266481874371113420505 8589949861405778335065379)
                  ·
                    refine ⟨12884924792108667502598069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8589949861405778335065379 12884924792108667502598069)
                    ·
                      refine ⟨1207961699260187578368569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12884924792108667502598069 1207961699260187578368569)
                      ·
                        rfl

theorem cell23_2352497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_2352497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352497 prefixEnd_2352497 := by exact prefixLift 2352497
  have htrace : WordTrace (prefixWord ++ tailWord_2352497) baseStart_2352497 baseEnd_2352497 := by
    simpa [prefixWord, tailWord_2352497, baseEnd_2352497] using wordTrace_append hprefix tailTrace_2352497
  have hstable : (prefixWord ++ tailWord_2352497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352497).length < 2 ^ (prefixWord ++ tailWord_2352497).sum := by decide
  have hdescent : baseEnd_2352497 < baseStart_2352497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352498 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 1, 3, 2]
def baseStart_2352498 : Nat := 118140960795 + 2352498 * 2 ^ 59
def prefixEnd_2352498 : Nat := 4983230072969 + 3 ^ 40 * 2352498 * 2
def baseEnd_2352498 : Nat := 1207962212740842074456065

theorem tailTrace_2352498 : CollatzResearch.WordTrace tailWord_2352498 prefixEnd_2352498 1207962212740842074456065 := by
  unfold tailWord_2352498
  simp only [CollatzResearch.WordTrace]
  refine ⟨21450662757827248879148537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57201767354205997011062765 21450662757827248879148537)
  ·
    refine ⟨16087997068370436659361403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21450662757827248879148537 16087997068370436659361403)
    ·
      refine ⟨24131995602555654989042105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16087997068370436659361403 24131995602555654989042105)
      ·
        refine ⟨18098996701916741241781579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24131995602555654989042105 18098996701916741241781579)
        ·
          refine ⟨27148495052875111862672369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18098996701916741241781579 27148495052875111862672369)
          ·
            refine ⟨20361371289656333897004277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27148495052875111862672369 20361371289656333897004277)
            ·
              refine ⟨1908878558405281302844151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20361371289656333897004277 1908878558405281302844151)
              ·
                refine ⟨2863317837607921954266227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908878558405281302844151 2863317837607921954266227)
                ·
                  refine ⟨4294976756411882931399341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2863317837607921954266227 4294976756411882931399341)
                  ·
                    refine ⟨1610616283654456099274753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4294976756411882931399341 1610616283654456099274753)
                    ·
                      refine ⟨1207962212740842074456065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1610616283654456099274753 1207962212740842074456065)
                      ·
                        rfl

theorem cell23_2352498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_2352498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352498 prefixEnd_2352498 := by exact prefixLift 2352498
  have htrace : WordTrace (prefixWord ++ tailWord_2352498) baseStart_2352498 baseEnd_2352498 := by
    simpa [prefixWord, tailWord_2352498, baseEnd_2352498] using wordTrace_append hprefix tailTrace_2352498
  have hstable : (prefixWord ++ tailWord_2352498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352498).length < 2 ^ (prefixWord ++ tailWord_2352498).sum := by decide
  have hdescent : baseEnd_2352498 < baseStart_2352498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352507 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 4]
def baseStart_2352507 : Nat := 118140960795 + 2352507 * 2 ^ 59
def prefixEnd_2352507 : Nat := 4983230072969 + 3 ^ 40 * 2352507 * 2
def baseEnd_2352507 : Nat := 1207966834066732539243523

theorem tailTrace_2352507 : CollatzResearch.WordTrace tailWord_2352507 prefixEnd_2352507 1207966834066732539243523 := by
  unfold tailWord_2352507
  simp only [CollatzResearch.WordTrace]
  refine ⟨85802979288276390053671775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57201986192184260035781183 85802979288276390053671775)
  ·
    refine ⟨128704468932414585080507663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85802979288276390053671775 128704468932414585080507663)
    ·
      refine ⟨193056703398621877620761495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128704468932414585080507663 193056703398621877620761495)
      ·
        refine ⟨289585055097932816431142243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193056703398621877620761495 289585055097932816431142243)
        ·
          refine ⟨434377582646899224646713365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289585055097932816431142243 434377582646899224646713365)
          ·
            refine ⟨20361449186573401155314689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 434377582646899224646713365 20361449186573401155314689)
            ·
              refine ⟨15271086889930050866486017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20361449186573401155314689 15271086889930050866486017)
              ·
                refine ⟨11453315167447538149864513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15271086889930050866486017 11453315167447538149864513)
                ·
                  refine ⟨8589986375585653612398385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11453315167447538149864513 8589986375585653612398385)
                  ·
                    refine ⟨6442489781689240209298789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8589986375585653612398385 6442489781689240209298789)
                    ·
                      refine ⟨1207966834066732539243523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6442489781689240209298789 1207966834066732539243523)
                      ·
                        rfl

theorem cell23_2352507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 4].length) (baseStart_2352507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352507 prefixEnd_2352507 := by exact prefixLift 2352507
  have htrace : WordTrace (prefixWord ++ tailWord_2352507) baseStart_2352507 baseEnd_2352507 := by
    simpa [prefixWord, tailWord_2352507, baseEnd_2352507] using wordTrace_append hprefix tailTrace_2352507
  have hstable : (prefixWord ++ tailWord_2352507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352507).length < 2 ^ (prefixWord ++ tailWord_2352507).sum := by decide
  have hdescent : baseEnd_2352507 < baseStart_2352507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352547 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 1, 7]
def baseStart_2352547 : Nat := 118140960795 + 2352547 * 2 ^ 59
def prefixEnd_2352547 : Nat := 4983230072969 + 3 ^ 40 * 2352547 * 2
def baseEnd_2352547 : Nat := 402662457764304127581113

theorem tailTrace_2352547 : CollatzResearch.WordTrace tailWord_2352547 prefixEnd_2352547 402662457764304127581113 := by
  unfold tailWord_2352547
  simp only [CollatzResearch.WordTrace]
  refine ⟨85804438208131476885127895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57202958805420984590085263 85804438208131476885127895)
  ·
    refine ⟨128706657312197215327691843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85804438208131476885127895 128706657312197215327691843)
    ·
      refine ⟨193059985968295822991537765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128706657312197215327691843 193059985968295822991537765)
      ·
        refine ⟨36198747369055466810913331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193059985968295822991537765 36198747369055466810913331)
        ·
          refine ⟨54298121053583200216369997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36198747369055466810913331 54298121053583200216369997)
          ·
            refine ⟨20361795395093700081138749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54298121053583200216369997 20361795395093700081138749)
            ·
              refine ⟨7635673273160137530427031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20361795395093700081138749 7635673273160137530427031)
              ·
                refine ⟨11453509909740206295640547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635673273160137530427031 11453509909740206295640547)
                ·
                  refine ⟨17180264864610309443460821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11453509909740206295640547 17180264864610309443460821)
                  ·
                    refine ⟨402662457764304127581113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17180264864610309443460821 402662457764304127581113)
                    ·
                      rfl

theorem cell23_2352547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 7].length) (baseStart_2352547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352547 prefixEnd_2352547 := by exact prefixLift 2352547
  have htrace : WordTrace (prefixWord ++ tailWord_2352547) baseStart_2352547 baseEnd_2352547 := by
    simpa [prefixWord, tailWord_2352547, baseEnd_2352547] using wordTrace_append hprefix tailTrace_2352547
  have hstable : (prefixWord ++ tailWord_2352547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352547).length < 2 ^ (prefixWord ++ tailWord_2352547).sum := by decide
  have hdescent : baseEnd_2352547 < baseStart_2352547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352551 : List Nat := [1, 1, 6, 1, 1, 1, 4, 3, 5]
def baseStart_2352551 : Nat := 118140960795 + 2352551 * 2 ^ 59
def prefixEnd_2352551 : Nat := 4983230072969 + 3 ^ 40 * 2352551 * 2
def baseEnd_2352551 : Nat := 134221047468392263010369

theorem tailTrace_2352551 : CollatzResearch.WordTrace tailWord_2352551 prefixEnd_2352551 134221047468392263010369 := by
  unfold tailWord_2352551
  simp only [CollatzResearch.WordTrace]
  refine ⟨85804584100116985568273507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57203056066744657045515671 85804584100116985568273507)
  ·
    refine ⟨128706876150175478352410261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85804584100116985568273507 128706876150175478352410261)
    ·
      refine ⟨6033134819539475547769231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128706876150175478352410261 6033134819539475547769231)
      ·
        refine ⟨9049702229309213321653847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6033134819539475547769231 9049702229309213321653847)
        ·
          refine ⟨13574553343963819982480771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9049702229309213321653847 13574553343963819982480771)
          ·
            refine ⟨20361830015945729973721157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13574553343963819982480771 20361830015945729973721157)
            ·
              refine ⟨3817843127989824370072717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20361830015945729973721157 3817843127989824370072717)
              ·
                refine ⟨1431691172996184138777269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3817843127989824370072717 1431691172996184138777269)
                ·
                  refine ⟨134221047468392263010369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1431691172996184138777269 134221047468392263010369)
                  ·
                    rfl

theorem cell23_2352551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 5].length) (baseStart_2352551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352551 prefixEnd_2352551 := by exact prefixLift 2352551
  have htrace : WordTrace (prefixWord ++ tailWord_2352551) baseStart_2352551 baseEnd_2352551 := by
    simpa [prefixWord, tailWord_2352551, baseEnd_2352551] using wordTrace_append hprefix tailTrace_2352551
  have hstable : (prefixWord ++ tailWord_2352551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352551).length < 2 ^ (prefixWord ++ tailWord_2352551).sum := by decide
  have hdescent : baseEnd_2352551 < baseStart_2352551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352607 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 10]
def baseStart_2352607 : Nat := 118140960795 + 2352607 * 2 ^ 59
def prefixEnd_2352607 : Nat := 4983230072969 + 3 ^ 40 * 2352607 * 2
def baseEnd_2352607 : Nat := 134224242459131349777007

theorem tailTrace_2352607 : CollatzResearch.WordTrace tailWord_2352607 prefixEnd_2352607 134224242459131349777007 := by
  unfold tailWord_2352607
  simp only [CollatzResearch.WordTrace]
  refine ⟨85806626587914107132312075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57204417725276071421541383 85806626587914107132312075)
  ·
    refine ⟨128709939881871160698468113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85806626587914107132312075 128709939881871160698468113)
    ·
      refine ⟨96532454911403370523851085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128709939881871160698468113 96532454911403370523851085)
      ·
        refine ⟨36199670591776263946444157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96532454911403370523851085 36199670591776263946444157)
        ·
          refine ⟨13574876471916098979916559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36199670591776263946444157 13574876471916098979916559)
          ·
            refine ⟨20362314707874148469874839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13574876471916098979916559 20362314707874148469874839)
            ·
              refine ⟨30543472061811222704812259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20362314707874148469874839 30543472061811222704812259)
              ·
                refine ⟨45815208092716834057218389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30543472061811222704812259 45815208092716834057218389)
                ·
                  refine ⟨134224242459131349777007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 45815208092716834057218389 134224242459131349777007)
                  ·
                    rfl

theorem cell23_2352607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 10].length) (baseStart_2352607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352607 prefixEnd_2352607 := by exact prefixLift 2352607
  have htrace : WordTrace (prefixWord ++ tailWord_2352607) baseStart_2352607 baseEnd_2352607 := by
    simpa [prefixWord, tailWord_2352607, baseEnd_2352607] using wordTrace_append hprefix tailTrace_2352607
  have hstable : (prefixWord ++ tailWord_2352607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352607).length < 2 ^ (prefixWord ++ tailWord_2352607).sum := by decide
  have hdescent : baseEnd_2352607 < baseStart_2352607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352627 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 6]
def baseStart_2352627 : Nat := 118140960795 + 2352627 * 2 ^ 59
def prefixEnd_2352627 : Nat := 4983230072969 + 3 ^ 40 * 2352627 * 2
def baseEnd_2352627 : Nat := 1208028451745272069742971

theorem tailTrace_2352627 : CollatzResearch.WordTrace tailWord_2352627 prefixEnd_2352627 1208028451745272069742971 := by
  unfold tailWord_2352627
  simp only [CollatzResearch.WordTrace]
  refine ⟨85807356047841650548040135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57204904031894433698693423 85807356047841650548040135)
  ·
    refine ⟨128711034071762475822060203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85807356047841650548040135 128711034071762475822060203)
    ·
      refine ⟨193066551107643713733090305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128711034071762475822060203 193066551107643713733090305)
      ·
        refine ⟨144799913330732785299817729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193066551107643713733090305 144799913330732785299817729)
        ·
          refine ⟨108599934998049588974863297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144799913330732785299817729 108599934998049588974863297)
          ·
            refine ⟨81449951248537191731147473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108599934998049588974863297 81449951248537191731147473)
            ·
              refine ⟨61087463436402893798360605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81449951248537191731147473 61087463436402893798360605)
              ·
                refine ⟨22907798788651085174385227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61087463436402893798360605 22907798788651085174385227)
                ·
                  refine ⟨34361698182976627761577841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22907798788651085174385227 34361698182976627761577841)
                  ·
                    refine ⟨25771273637232470821183381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34361698182976627761577841 25771273637232470821183381)
                    ·
                      refine ⟨1208028451745272069742971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25771273637232470821183381 1208028451745272069742971)
                      ·
                        rfl

theorem cell23_2352627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_2352627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352627 prefixEnd_2352627 := by exact prefixLift 2352627
  have htrace : WordTrace (prefixWord ++ tailWord_2352627) baseStart_2352627 baseEnd_2352627 := by
    simpa [prefixWord, tailWord_2352627, baseEnd_2352627] using wordTrace_append hprefix tailTrace_2352627
  have hstable : (prefixWord ++ tailWord_2352627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352627).length < 2 ^ (prefixWord ++ tailWord_2352627).sum := by decide
  have hdescent : baseEnd_2352627 < baseStart_2352627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352641 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 6]
def baseStart_2352641 : Nat := 118140960795 + 2352641 * 2 ^ 59
def prefixEnd_2352641 : Nat := 4983230072969 + 3 ^ 40 * 2352641 * 2
def baseEnd_2352641 : Nat := 134226182274937223885323

theorem tailTrace_2352641 : CollatzResearch.WordTrace tailWord_2352641 prefixEnd_2352641 134226182274937223885323 := by
  unfold tailWord_2352641
  simp only [CollatzResearch.WordTrace]
  refine ⟨85807866669790930939049777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57205244446527287292699851 85807866669790930939049777)
  ·
    refine ⟨64355900002343198204287333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85807866669790930939049777 64355900002343198204287333)
    ·
      refine ⟨12066731250439349663303875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64355900002343198204287333 12066731250439349663303875)
      ·
        refine ⟨18100096875659024494955813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12066731250439349663303875 18100096875659024494955813)
        ·
          refine ⟨3393768164186067092804215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18100096875659024494955813 3393768164186067092804215)
          ·
            refine ⟨5090652246279100639206323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393768164186067092804215 5090652246279100639206323)
            ·
              refine ⟨7635978369418650958809485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090652246279100639206323 7635978369418650958809485)
              ·
                refine ⟨2863491888531994109553557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7635978369418650958809485 2863491888531994109553557)
                ·
                  refine ⟨134226182274937223885323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2863491888531994109553557 134226182274937223885323)
                  ·
                    rfl

theorem cell23_2352641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 6].length) (baseStart_2352641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352641 prefixEnd_2352641 := by exact prefixLift 2352641
  have htrace : WordTrace (prefixWord ++ tailWord_2352641) baseStart_2352641 baseEnd_2352641 := by
    simpa [prefixWord, tailWord_2352641, baseEnd_2352641] using wordTrace_append hprefix tailTrace_2352641
  have hstable : (prefixWord ++ tailWord_2352641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352641).length < 2 ^ (prefixWord ++ tailWord_2352641).sum := by decide
  have hdescent : baseEnd_2352641 < baseStart_2352641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352776 : List Nat := [2, 1, 3, 5, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2352776 : Nat := 118140960795 + 2352776 * 2 ^ 59
def prefixEnd_2352776 : Nat := 4983230072969 + 3 ^ 40 * 2352776 * 2
def baseEnd_2352776 : Nat := 1208104960362791986779787

theorem tailTrace_2352776 : CollatzResearch.WordTrace tailWord_2352776 prefixEnd_2352776 1208104960362791986779787 := by
  unfold tailWord_2352776
  simp only [CollatzResearch.WordTrace]
  refine ⟨42906395262150924497607091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57208527016201232663476121 42906395262150924497607091)
  ·
    refine ⟨64359592893226386746410637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42906395262150924497607091 64359592893226386746410637)
    ·
      refine ⟨24134847334959895029903989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64359592893226386746410637 24134847334959895029903989)
      ·
        refine ⟨2262641937652490159053499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24134847334959895029903989 2262641937652490159053499)
        ·
          refine ⟨3393962906478735238580249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262641937652490159053499 3393962906478735238580249)
          ·
            refine ⟨2545472179859051428935187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3393962906478735238580249 2545472179859051428935187)
            ·
              refine ⟨3818208269788577143402781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545472179859051428935187 3818208269788577143402781)
              ·
                refine ⟨1431828101170716428776043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3818208269788577143402781 1431828101170716428776043)
                ·
                  refine ⟨2147742151756074643164065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431828101170716428776043 2147742151756074643164065)
                  ·
                    refine ⟨1610806613817055982373049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2147742151756074643164065 1610806613817055982373049)
                    ·
                      refine ⟨1208104960362791986779787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1610806613817055982373049 1208104960362791986779787)
                      ·
                        rfl

theorem cell23_2352776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2352776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352776 prefixEnd_2352776 := by exact prefixLift 2352776
  have htrace : WordTrace (prefixWord ++ tailWord_2352776) baseStart_2352776 baseEnd_2352776 := by
    simpa [prefixWord, tailWord_2352776, baseEnd_2352776] using wordTrace_append hprefix tailTrace_2352776
  have hstable : (prefixWord ++ tailWord_2352776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352776).length < 2 ^ (prefixWord ++ tailWord_2352776).sum := by decide
  have hdescent : baseEnd_2352776 < baseStart_2352776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352815 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 2, 2, 2]
def baseStart_2352815 : Nat := 118140960795 + 2352815 * 2 ^ 59
def prefixEnd_2352815 : Nat := 4983230072969 + 3 ^ 40 * 2352815 * 2
def baseEnd_2352815 : Nat := 1208124986108317334192107

theorem tailTrace_2352815 : CollatzResearch.WordTrace tailWord_2352815 prefixEnd_2352815 1208124986108317334192107 := by
  unfold tailWord_2352815
  simp only [CollatzResearch.WordTrace]
  refine ⟨85814212971160558655883899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57209475314107039103922599 85814212971160558655883899)
  ·
    refine ⟨128721319456740837983825849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85814212971160558655883899 128721319456740837983825849)
    ·
      refine ⟨96540989592555628487869387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128721319456740837983825849 96540989592555628487869387)
      ·
        refine ⟨144811484388833442731804081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96540989592555628487869387 144811484388833442731804081)
        ·
          refine ⟨108608613291625082048853061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144811484388833442731804081 108608613291625082048853061)
          ·
            refine ⟨20364114992179702884159949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108608613291625082048853061 20364114992179702884159949)
            ·
              refine ⟨7636543122067388581559981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20364114992179702884159949 7636543122067388581559981)
              ·
                refine ⟨2863703670775270718084993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7636543122067388581559981 2863703670775270718084993)
                ·
                  refine ⟨2147777753081453038563745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2863703670775270718084993 2147777753081453038563745)
                  ·
                    refine ⟨1610833314811089778922809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2147777753081453038563745 1610833314811089778922809)
                    ·
                      refine ⟨1208124986108317334192107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1610833314811089778922809 1208124986108317334192107)
                      ·
                        rfl

theorem cell23_2352815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 2, 2].length) (baseStart_2352815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352815 prefixEnd_2352815 := by exact prefixLift 2352815
  have htrace : WordTrace (prefixWord ++ tailWord_2352815) baseStart_2352815 baseEnd_2352815 := by
    simpa [prefixWord, tailWord_2352815, baseEnd_2352815] using wordTrace_append hprefix tailTrace_2352815
  have hstable : (prefixWord ++ tailWord_2352815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352815).length < 2 ^ (prefixWord ++ tailWord_2352815).sum := by decide
  have hdescent : baseEnd_2352815 < baseStart_2352815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352824 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_2352824 : Nat := 118140960795 + 2352824 * 2 ^ 59
def prefixEnd_2352824 : Nat := 4983230072969 + 3 ^ 40 * 2352824 * 2
def baseEnd_2352824 : Nat := 1208129607434207798979565

theorem tailTrace_2352824 : CollatzResearch.WordTrace tailWord_2352824 prefixEnd_2352824 1208129607434207798979565 := by
  unfold tailWord_2352824
  simp only [CollatzResearch.WordTrace]
  refine ⟨42907270614063976596480763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57209694152085302128641017 42907270614063976596480763)
  ·
    refine ⟨64360905921095964894721145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42907270614063976596480763 64360905921095964894721145)
    ·
      refine ⟨48270679440821973671040859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64360905921095964894721145 48270679440821973671040859)
      ·
        refine ⟨72406019161232960506561289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48270679440821973671040859 72406019161232960506561289)
        ·
          refine ⟨54304514370924720379920967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72406019161232960506561289 54304514370924720379920967)
          ·
            refine ⟨81456771556387080569881451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54304514370924720379920967 81456771556387080569881451)
            ·
              refine ⟨122185157334580620854822177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81456771556387080569881451 122185157334580620854822177)
              ·
                refine ⟨91638868000935465641116633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122185157334580620854822177 91638868000935465641116633)
                ·
                  refine ⟨68729151000701599230837475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91638868000935465641116633 68729151000701599230837475)
                  ·
                    refine ⟨103093726501052398846256213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68729151000701599230837475 103093726501052398846256213)
                    ·
                      refine ⟨1208129607434207798979565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 103093726501052398846256213 1208129607434207798979565)
                      ·
                        rfl

theorem cell23_2352824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_2352824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352824 prefixEnd_2352824 := by exact prefixLift 2352824
  have htrace : WordTrace (prefixWord ++ tailWord_2352824) baseStart_2352824 baseEnd_2352824 := by
    simpa [prefixWord, tailWord_2352824, baseEnd_2352824] using wordTrace_append hprefix tailTrace_2352824
  have hstable : (prefixWord ++ tailWord_2352824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352824).length < 2 ^ (prefixWord ++ tailWord_2352824).sum := by decide
  have hdescent : baseEnd_2352824 < baseStart_2352824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352858 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2]
def baseStart_2352858 : Nat := 118140960795 + 2352858 * 2 ^ 59
def prefixEnd_2352858 : Nat := 4983230072969 + 3 ^ 40 * 2352858 * 2
def baseEnd_2352858 : Nat := 1208147065776460665954409

theorem tailTrace_2352858 : CollatzResearch.WordTrace tailWord_2352858 prefixEnd_2352858 1208147065776460665954409 := by
  unfold tailWord_2352858
  simp only [CollatzResearch.WordTrace]
  refine ⟨21453945327501194249924807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57210520873336517999799485 21453945327501194249924807)
  ·
    refine ⟨32180917991251791374887211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21453945327501194249924807 32180917991251791374887211)
    ·
      refine ⟨48271376986877687062330817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32180917991251791374887211 48271376986877687062330817)
      ·
        refine ⟨36203532740158265296748113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48271376986877687062330817 36203532740158265296748113)
        ·
          refine ⟨27152649555118698972561085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36203532740158265296748113 27152649555118698972561085)
          ·
            refine ⟨10182243583169512114710407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27152649555118698972561085 10182243583169512114710407)
            ·
              refine ⟨15273365374754268172065611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10182243583169512114710407 15273365374754268172065611)
              ·
                refine ⟨22910048062131402258098417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15273365374754268172065611 22910048062131402258098417)
                ·
                  refine ⟨17182536046598551693573813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22910048062131402258098417 17182536046598551693573813)
                  ·
                    refine ⟨1610862754368614221272545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17182536046598551693573813 1610862754368614221272545)
                    ·
                      refine ⟨1208147065776460665954409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1610862754368614221272545 1208147065776460665954409)
                      ·
                        rfl

theorem cell23_2352858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_2352858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352858 prefixEnd_2352858 := by exact prefixLift 2352858
  have htrace : WordTrace (prefixWord ++ tailWord_2352858) baseStart_2352858 baseEnd_2352858 := by
    simpa [prefixWord, tailWord_2352858, baseEnd_2352858] using wordTrace_append hprefix tailTrace_2352858
  have hstable : (prefixWord ++ tailWord_2352858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352858).length < 2 ^ (prefixWord ++ tailWord_2352858).sum := by decide
  have hdescent : baseEnd_2352858 < baseStart_2352858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352908 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 2, 2, 3]
def baseStart_2352908 : Nat := 118140960795 + 2352908 * 2 ^ 59
def prefixEnd_2352908 : Nat := 4983230072969 + 3 ^ 40 * 2352908 * 2
def baseEnd_2352908 : Nat := 1208172739809185470329179

theorem tailTrace_2352908 : CollatzResearch.WordTrace tailWord_2352908 prefixEnd_2352908 1208172739809185470329179 := by
  unfold tailWord_2352908
  simp only [CollatzResearch.WordTrace]
  refine ⟨42908802479911817769509689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57211736639882423692679585 42908802479911817769509689)
  ·
    refine ⟨32181601859933863327132267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42908802479911817769509689 32181601859933863327132267)
    ·
      refine ⟨48272402789900794990698401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32181601859933863327132267 48272402789900794990698401)
      ·
        refine ⟨36204302092425596243023801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48272402789900794990698401 36204302092425596243023801)
        ·
          refine ⟨27153226569319197182267851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36204302092425596243023801 27153226569319197182267851)
          ·
            refine ⟨40729839853978795773401777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27153226569319197182267851 40729839853978795773401777)
            ·
              refine ⟨30547379890484096830051333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40729839853978795773401777 30547379890484096830051333)
              ·
                refine ⟨5727633729465768155634625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30547379890484096830051333 5727633729465768155634625)
                ·
                  refine ⟨4295725297099326116725969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5727633729465768155634625 4295725297099326116725969)
                  ·
                    refine ⟨3221793972824494587544477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4295725297099326116725969 3221793972824494587544477)
                    ·
                      refine ⟨1208172739809185470329179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3221793972824494587544477 1208172739809185470329179)
                      ·
                        rfl

theorem cell23_2352908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_2352908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352908 prefixEnd_2352908 := by exact prefixLift 2352908
  have htrace : WordTrace (prefixWord ++ tailWord_2352908) baseStart_2352908 baseEnd_2352908 := by
    simpa [prefixWord, tailWord_2352908, baseEnd_2352908] using wordTrace_append hprefix tailTrace_2352908
  have hstable : (prefixWord ++ tailWord_2352908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352908).length < 2 ^ (prefixWord ++ tailWord_2352908).sum := by decide
  have hdescent : baseEnd_2352908 < baseStart_2352908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352911 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 6]
def baseStart_2352911 : Nat := 118140960795 + 2352911 * 2 ^ 59
def prefixEnd_2352911 : Nat := 4983230072969 + 3 ^ 40 * 2352911 * 2
def baseEnd_2352911 : Nat := 134241586694572106510185

theorem tailTrace_2352911 : CollatzResearch.WordTrace tailWord_2352911 prefixEnd_2352911 134241586694572106510185 := by
  unfold tailWord_2352911
  simp only [CollatzResearch.WordTrace]
  refine ⟨85817714378812767051378587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57211809585875178034252391 85817714378812767051378587)
  ·
    refine ⟨128726571568219150577067881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85817714378812767051378587 128726571568219150577067881)
    ·
      refine ⟨96544928676164362932800911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128726571568219150577067881 96544928676164362932800911)
      ·
        refine ⟨144817393014246544399201367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96544928676164362932800911 144817393014246544399201367)
        ·
          refine ⟨217226089521369816598802051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144817393014246544399201367 217226089521369816598802051)
          ·
            refine ⟨325839134282054724898203077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217226089521369816598802051 325839134282054724898203077)
            ·
              refine ⟨61094837677885260918413077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 325839134282054724898203077 61094837677885260918413077)
              ·
                refine ⟨2863820516150871605550613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61094837677885260918413077 2863820516150871605550613)
                ·
                  refine ⟨134241586694572106510185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2863820516150871605550613 134241586694572106510185)
                  ·
                    rfl

theorem cell23_2352911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 6].length) (baseStart_2352911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352911 prefixEnd_2352911 := by exact prefixLift 2352911
  have htrace : WordTrace (prefixWord ++ tailWord_2352911) baseStart_2352911 baseEnd_2352911 := by
    simpa [prefixWord, tailWord_2352911, baseEnd_2352911] using wordTrace_append hprefix tailTrace_2352911
  have hstable : (prefixWord ++ tailWord_2352911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352911).length < 2 ^ (prefixWord ++ tailWord_2352911).sum := by decide
  have hdescent : baseEnd_2352911 < baseStart_2352911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352949 : List Nat := [1, 3, 3, 1, 4, 2, 1, 3, 1, 4]
def baseStart_2352949 : Nat := 118140960795 + 2352949 * 2 ^ 59
def prefixEnd_2352949 : Nat := 4983230072969 + 3 ^ 40 * 2352949 * 2
def baseEnd_2352949 : Nat := 402731264172006603305497

theorem tailTrace_2352949 : CollatzResearch.WordTrace tailWord_2352949 prefixEnd_2352949 402731264172006603305497 := by
  unfold tailWord_2352949
  simp only [CollatzResearch.WordTrace]
  refine ⟨85819100352675099541261901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57212733568450066360841267 85819100352675099541261901)
  ·
    refine ⟨32182162632253162327973213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85819100352675099541261901 32182162632253162327973213)
    ·
      refine ⟨12068310987094935872989955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32182162632253162327973213 12068310987094935872989955)
      ·
        refine ⟨18102466480642403809484933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12068310987094935872989955 18102466480642403809484933)
        ·
          refine ⟨3394212465120450714278425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18102466480642403809484933 3394212465120450714278425)
          ·
            refine ⟨2545659348840338035708819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3394212465120450714278425 2545659348840338035708819)
            ·
              refine ⟨3818489023260507053563229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545659348840338035708819 3818489023260507053563229)
              ·
                refine ⟨1431933383722690145086211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3818489023260507053563229 1431933383722690145086211)
                ·
                  refine ⟨2147900075584035217629317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431933383722690145086211 2147900075584035217629317)
                  ·
                    refine ⟨402731264172006603305497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2147900075584035217629317 402731264172006603305497)
                    ·
                      rfl

theorem cell23_2352949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_2352949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352949 prefixEnd_2352949 := by exact prefixLift 2352949
  have htrace : WordTrace (prefixWord ++ tailWord_2352949) baseStart_2352949 baseEnd_2352949 := by
    simpa [prefixWord, tailWord_2352949, baseEnd_2352949] using wordTrace_append hprefix tailTrace_2352949
  have hstable : (prefixWord ++ tailWord_2352949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352949).length < 2 ^ (prefixWord ++ tailWord_2352949).sum := by decide
  have hdescent : baseEnd_2352949 < baseStart_2352949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352965 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 2, 3, 2]
def baseStart_2352965 : Nat := 118140960795 + 2352965 * 2 ^ 59
def prefixEnd_2352965 : Nat := 4983230072969 + 3 ^ 40 * 2352965 * 2
def baseEnd_2352965 : Nat := 1208202008206491747316417

theorem tailTrace_2352965 : CollatzResearch.WordTrace tailWord_2352965 prefixEnd_2352965 1208202008206491747316417 := by
  unfold tailWord_2352965
  simp only [CollatzResearch.WordTrace]
  refine ⟨85819683920617134273844349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57213122613744756182562899 85819683920617134273844349)
  ·
    refine ⟨32182381470231425352691631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85819683920617134273844349 32182381470231425352691631)
    ·
      refine ⟨48273572205347138029037447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32182381470231425352691631 48273572205347138029037447)
      ·
        refine ⟨72410358308020707043556171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48273572205347138029037447 72410358308020707043556171)
        ·
          refine ⟨108615537462031060565334257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72410358308020707043556171 108615537462031060565334257)
          ·
            refine ⟨81461653096523295424000693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108615537462031060565334257 81461653096523295424000693)
            ·
              refine ⟨7637029977799058946000065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81461653096523295424000693 7637029977799058946000065)
              ·
                refine ⟨5727772483349294209500049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7637029977799058946000065 5727772483349294209500049)
                ·
                  refine ⟨4295829362511970657125037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5727772483349294209500049 4295829362511970657125037)
                  ·
                    refine ⟨1610936010941988996421889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4295829362511970657125037 1610936010941988996421889)
                    ·
                      refine ⟨1208202008206491747316417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1610936010941988996421889 1208202008206491747316417)
                      ·
                        rfl

theorem cell23_2352965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_2352965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352965 prefixEnd_2352965 := by exact prefixLift 2352965
  have htrace : WordTrace (prefixWord ++ tailWord_2352965) baseStart_2352965 baseEnd_2352965 := by
    simpa [prefixWord, tailWord_2352965, baseEnd_2352965] using wordTrace_append hprefix tailTrace_2352965
  have hstable : (prefixWord ++ tailWord_2352965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352965).length < 2 ^ (prefixWord ++ tailWord_2352965).sum := by decide
  have hdescent : baseEnd_2352965 < baseStart_2352965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352995 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 4]
def baseStart_2352995 : Nat := 118140960795 + 2352995 * 2 ^ 59
def prefixEnd_2352995 : Nat := 4983230072969 + 3 ^ 40 * 2352995 * 2
def baseEnd_2352995 : Nat := 1208217412626126629941279

theorem tailTrace_2352995 : CollatzResearch.WordTrace tailWord_2352995 prefixEnd_2352995 1208217412626126629941279 := by
  unfold tailWord_2352995
  simp only [CollatzResearch.WordTrace]
  refine ⟨85820778110508449397436439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57213852073672299598290959 85820778110508449397436439)
  ·
    refine ⟨128731167165762674096154659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85820778110508449397436439 128731167165762674096154659)
    ·
      refine ⟨193096750748644011144231989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128731167165762674096154659 193096750748644011144231989)
      ·
        refine ⟨18102820382685376044771749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193096750748644011144231989 18102820382685376044771749)
        ·
          refine ⟨3394278821753508008394703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18102820382685376044771749 3394278821753508008394703)
          ·
            refine ⟨5091418232630262012592055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394278821753508008394703 5091418232630262012592055)
            ·
              refine ⟨7637127348945393018888083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5091418232630262012592055 7637127348945393018888083)
              ·
                refine ⟨11455691023418089528332125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637127348945393018888083 11455691023418089528332125)
                ·
                  refine ⟨4295884133781783573124547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11455691023418089528332125 4295884133781783573124547)
                  ·
                    refine ⟨6443826200672675359686821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4295884133781783573124547 6443826200672675359686821)
                    ·
                      refine ⟨1208217412626126629941279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6443826200672675359686821 1208217412626126629941279)
                      ·
                        rfl

theorem cell23_2352995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_2352995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2352995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2352995 prefixEnd_2352995 := by exact prefixLift 2352995
  have htrace : WordTrace (prefixWord ++ tailWord_2352995) baseStart_2352995 baseEnd_2352995 := by
    simpa [prefixWord, tailWord_2352995, baseEnd_2352995] using wordTrace_append hprefix tailTrace_2352995
  have hstable : (prefixWord ++ tailWord_2352995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352995).length < 2 ^ (prefixWord ++ tailWord_2352995).sum := by decide
  have hdescent : baseEnd_2352995 < baseStart_2352995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353029 : List Nat := [1, 3, 1, 1, 3, 2, 3, 4, 1, 2, 2]
def baseStart_2353029 : Nat := 118140960795 + 2353029 * 2 ^ 59
def prefixEnd_2353029 : Nat := 4983230072969 + 3 ^ 40 * 2353029 * 2
def baseEnd_2353029 : Nat := 1208234870968379496916123

theorem tailTrace_2353029 : CollatzResearch.WordTrace tailWord_2353029 prefixEnd_2353029 1208234870968379496916123 := by
  unfold tailWord_2353029
  simp only [CollatzResearch.WordTrace]
  refine ⟨85822018192385273204174141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57214678794923515469449427 85822018192385273204174141)
  ·
    refine ⟨32183256822144477451565303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85822018192385273204174141 32183256822144477451565303)
    ·
      refine ⟨48274885233216716177347955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32183256822144477451565303 48274885233216716177347955)
      ·
        refine ⟨72412327849825074266021933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48274885233216716177347955 72412327849825074266021933)
        ·
          refine ⟨27154622943684402849758225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72412327849825074266021933 27154622943684402849758225)
          ·
            refine ⟨20365967207763302137318669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27154622943684402849758225 20365967207763302137318669)
            ·
              refine ⟨7637237702911238301494501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20365967207763302137318669 7637237702911238301494501)
              ·
                refine ⟨1431982069295857181530219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7637237702911238301494501 1431982069295857181530219)
                ·
                  refine ⟨2147973103943785772295329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431982069295857181530219 2147973103943785772295329)
                  ·
                    refine ⟨1610979827957839329221497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2147973103943785772295329 1610979827957839329221497)
                    ·
                      refine ⟨1208234870968379496916123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1610979827957839329221497 1208234870968379496916123)
                      ·
                        rfl

theorem cell23_2353029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 1, 2, 2].length) (baseStart_2353029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353029 prefixEnd_2353029 := by exact prefixLift 2353029
  have htrace : WordTrace (prefixWord ++ tailWord_2353029) baseStart_2353029 baseEnd_2353029 := by
    simpa [prefixWord, tailWord_2353029, baseEnd_2353029] using wordTrace_append hprefix tailTrace_2353029
  have hstable : (prefixWord ++ tailWord_2353029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353029).length < 2 ^ (prefixWord ++ tailWord_2353029).sum := by decide
  have hdescent : baseEnd_2353029 < baseStart_2353029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353042 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2353042 : Nat := 118140960795 + 2353042 * 2 ^ 59
def prefixEnd_2353042 : Nat := 4983230072969 + 3 ^ 40 * 2353042 * 2
def baseEnd_2353042 : Nat := 1208241546216887946053563

theorem tailTrace_2353042 : CollatzResearch.WordTrace tailWord_2353042 prefixEnd_2353042 1208241546216887946053563 := by
  unfold tailWord_2353042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21455623085334544106099345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57214994894225450949598253 21455623085334544106099345)
  ·
    refine ⟨16091717314000908079574509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21455623085334544106099345 16091717314000908079574509)
    ·
      refine ⟨6034393992750340529840441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16091717314000908079574509 6034393992750340529840441)
      ·
        refine ⟨4525795494562755397380331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6034393992750340529840441 4525795494562755397380331)
        ·
          refine ⟨6788693241844133096070497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4525795494562755397380331 6788693241844133096070497)
          ·
            refine ⟨5091519931383099822052873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6788693241844133096070497 5091519931383099822052873)
            ·
              refine ⟨3818639948537324866539655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5091519931383099822052873 3818639948537324866539655)
              ·
                refine ⟨5727959922805987299809483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3818639948537324866539655 5727959922805987299809483)
                ·
                  refine ⟨8591939884208980949714225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5727959922805987299809483 8591939884208980949714225)
                  ·
                    refine ⟨6443954913156735712285669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8591939884208980949714225 6443954913156735712285669)
                    ·
                      refine ⟨1208241546216887946053563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6443954913156735712285669 1208241546216887946053563)
                      ·
                        rfl

theorem cell23_2353042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2353042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353042 prefixEnd_2353042 := by exact prefixLift 2353042
  have htrace : WordTrace (prefixWord ++ tailWord_2353042) baseStart_2353042 baseEnd_2353042 := by
    simpa [prefixWord, tailWord_2353042, baseEnd_2353042] using wordTrace_append hprefix tailTrace_2353042
  have hstable : (prefixWord ++ tailWord_2353042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353042).length < 2 ^ (prefixWord ++ tailWord_2353042).sum := by decide
  have hdescent : baseEnd_2353042 < baseStart_2353042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353045 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_2353045 : Nat := 118140960795 + 2353045 * 2 ^ 59
def prefixEnd_2353045 : Nat := 4983230072969 + 3 ^ 40 * 2353045 * 2
def baseEnd_2353045 : Nat := 1208243086658851434316049

theorem tailTrace_2353045 : CollatzResearch.WordTrace tailWord_2353045 prefixEnd_2353045 1208243086658851434316049 := by
  unfold tailWord_2353045
  simp only [CollatzResearch.WordTrace]
  refine ⟨85822601760327307936756589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57215067840218205291171059 85822601760327307936756589)
  ·
    refine ⟨32183475660122740476283721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85822601760327307936756589 32183475660122740476283721)
    ·
      refine ⟨24137606745092055357212791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32183475660122740476283721 24137606745092055357212791)
      ·
        refine ⟨36206410117638083035819187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24137606745092055357212791 36206410117638083035819187)
        ·
          refine ⟨54309615176457124553728781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36206410117638083035819187 54309615176457124553728781)
          ·
            refine ⟨20366105691171421707648293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54309615176457124553728781 20366105691171421707648293)
            ·
              refine ⟨3818644817094641570184055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20366105691171421707648293 3818644817094641570184055)
              ·
                refine ⟨5727967225641962355276083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3818644817094641570184055 5727967225641962355276083)
                ·
                  refine ⟨8591950838462943532914125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5727967225641962355276083 8591950838462943532914125)
                  ·
                    refine ⟨3221981564423603824842797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8591950838462943532914125 3221981564423603824842797)
                    ·
                      refine ⟨1208243086658851434316049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3221981564423603824842797 1208243086658851434316049)
                      ·
                        rfl

theorem cell23_2353045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_2353045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353045 prefixEnd_2353045 := by exact prefixLift 2353045
  have htrace : WordTrace (prefixWord ++ tailWord_2353045) baseStart_2353045 baseEnd_2353045 := by
    simpa [prefixWord, tailWord_2353045, baseEnd_2353045] using wordTrace_append hprefix tailTrace_2353045
  have hstable : (prefixWord ++ tailWord_2353045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353045).length < 2 ^ (prefixWord ++ tailWord_2353045).sum := by decide
  have hdescent : baseEnd_2353045 < baseStart_2353045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353106 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_2353106 : Nat := 118140960795 + 2353106 * 2 ^ 59
def prefixEnd_2353106 : Nat := 4983230072969 + 3 ^ 40 * 2353106 * 2
def baseEnd_2353106 : Nat := 1208274408978775695653269

theorem tailTrace_2353106 : CollatzResearch.WordTrace tailWord_2353106 prefixEnd_2353106 1208274408978775695653269 := by
  unfold tailWord_2353106
  simp only [CollatzResearch.WordTrace]
  refine ⟨21456206653276578838681793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57216551075404210236484781 21456206653276578838681793)
  ·
    refine ⟨16092154989957434129011345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21456206653276578838681793 16092154989957434129011345)
    ·
      refine ⟨12069116242468075596758509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16092154989957434129011345 12069116242468075596758509)
      ·
        refine ⟨4525918590925528348784441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12069116242468075596758509 4525918590925528348784441)
        ·
          refine ⟨3394438943194146261588331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4525918590925528348784441 3394438943194146261588331)
          ·
            refine ⟨5091658414791219392382497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394438943194146261588331 5091658414791219392382497)
            ·
              refine ⟨3818743811093414544286873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5091658414791219392382497 3818743811093414544286873)
              ·
                refine ⟨2864057858320060908215155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3818743811093414544286873 2864057858320060908215155)
                ·
                  refine ⟨4296086787480091362322733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864057858320060908215155 4296086787480091362322733)
                  ·
                    refine ⟨1611032545305034260871025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4296086787480091362322733 1611032545305034260871025)
                    ·
                      refine ⟨1208274408978775695653269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611032545305034260871025 1208274408978775695653269)
                      ·
                        rfl

theorem cell23_2353106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_2353106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353106 prefixEnd_2353106 := by exact prefixLift 2353106
  have htrace : WordTrace (prefixWord ++ tailWord_2353106) baseStart_2353106 baseEnd_2353106 := by
    simpa [prefixWord, tailWord_2353106, baseEnd_2353106] using wordTrace_append hprefix tailTrace_2353106
  have hstable : (prefixWord ++ tailWord_2353106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353106).length < 2 ^ (prefixWord ++ tailWord_2353106).sum := by decide
  have hdescent : baseEnd_2353106 < baseStart_2353106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353195 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 3]
def baseStart_2353195 : Nat := 118140960795 + 2353195 * 2 ^ 59
def prefixEnd_2353195 : Nat := 4983230072969 + 3 ^ 40 * 2353195 * 2
def baseEnd_2353195 : Nat := 1208320108757025847440359

theorem tailTrace_2353195 : CollatzResearch.WordTrace tailWord_2353195 prefixEnd_2353195 1208320108757025847440359 := by
  unfold tailWord_2353195
  simp only [CollatzResearch.WordTrace]
  refine ⟨85828072709783883554717039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57218715139855922369811359 85828072709783883554717039)
  ·
    refine ⟨128742109064675825332075559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85828072709783883554717039 128742109064675825332075559)
    ·
      refine ⟨193113163597013737998113339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128742109064675825332075559 193113163597013737998113339)
      ·
        refine ⟨289669745395520606997170009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193113163597013737998113339 289669745395520606997170009)
        ·
          refine ⟨217252309046640455247877507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289669745395520606997170009 217252309046640455247877507)
          ·
            refine ⟨325878463569960682871816261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217252309046640455247877507 325878463569960682871816261)
            ·
              refine ⟨61102211919367628038465549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 325878463569960682871816261 61102211919367628038465549)
              ·
                refine ⟨22913329469762860514424581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61102211919367628038465549 22913329469762860514424581)
                ·
                  refine ⟨4296249275580536346454609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22913329469762860514424581 4296249275580536346454609)
                  ·
                    refine ⟨3222186956685402259840957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4296249275580536346454609 3222186956685402259840957)
                    ·
                      refine ⟨1208320108757025847440359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3222186956685402259840957 1208320108757025847440359)
                      ·
                        rfl

theorem cell23_2353195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 3].length) (baseStart_2353195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353195 prefixEnd_2353195 := by exact prefixLift 2353195
  have htrace : WordTrace (prefixWord ++ tailWord_2353195) baseStart_2353195 baseEnd_2353195 := by
    simpa [prefixWord, tailWord_2353195, baseEnd_2353195] using wordTrace_append hprefix tailTrace_2353195
  have hstable : (prefixWord ++ tailWord_2353195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353195).length < 2 ^ (prefixWord ++ tailWord_2353195).sum := by decide
  have hdescent : baseEnd_2353195 < baseStart_2353195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353209 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 2, 4, 2]
def baseStart_2353209 : Nat := 118140960795 + 2353209 * 2 ^ 59
def prefixEnd_2353209 : Nat := 4983230072969 + 3 ^ 40 * 2353209 * 2
def baseEnd_2353209 : Nat := 1208327297486188792665295

theorem tailTrace_2353209 : CollatzResearch.WordTrace tailWord_2353209 prefixEnd_2353209 1208327297486188792665295 := by
  unfold tailWord_2353209
  simp only [CollatzResearch.WordTrace]
  refine ⟨85828583331733163945726681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57219055554488775963817787 85828583331733163945726681)
  ·
    refine ⟨64371437498799872959295011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85828583331733163945726681 64371437498799872959295011)
    ·
      refine ⟨96557156248199809438942517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64371437498799872959295011 96557156248199809438942517)
      ·
        refine ⟨9052233398268732134900861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96557156248199809438942517 9052233398268732134900861)
        ·
          refine ⟨3394587524350774550587823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9052233398268732134900861 3394587524350774550587823)
          ·
            refine ⟨5091881286526161825881735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394587524350774550587823 5091881286526161825881735)
            ·
              refine ⟨7637821929789242738822603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5091881286526161825881735 7637821929789242738822603)
              ·
                refine ⟨11456732894683864108233905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637821929789242738822603 11456732894683864108233905)
                ·
                  refine ⟨8592549671012898081175429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11456732894683864108233905 8592549671012898081175429)
                  ·
                    refine ⟨1611103063314918390220393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8592549671012898081175429 1611103063314918390220393)
                    ·
                      refine ⟨1208327297486188792665295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611103063314918390220393 1208327297486188792665295)
                      ·
                        rfl

theorem cell23_2353209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_2353209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353209 prefixEnd_2353209 := by exact prefixLift 2353209
  have htrace : WordTrace (prefixWord ++ tailWord_2353209) baseStart_2353209 baseEnd_2353209 := by
    simpa [prefixWord, tailWord_2353209, baseEnd_2353209] using wordTrace_append hprefix tailTrace_2353209
  have hstable : (prefixWord ++ tailWord_2353209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353209).length < 2 ^ (prefixWord ++ tailWord_2353209).sum := by decide
  have hdescent : baseEnd_2353209 < baseStart_2353209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353215 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 6]
def baseStart_2353215 : Nat := 118140960795 + 2353215 * 2 ^ 59
def prefixEnd_2353215 : Nat := 4983230072969 + 3 ^ 40 * 2353215 * 2
def baseEnd_2353215 : Nat := 134258930930012863243363

theorem tailTrace_2353215 : CollatzResearch.WordTrace tailWord_2353215 prefixEnd_2353215 134258930930012863243363 := by
  unfold tailWord_2353215
  simp only [CollatzResearch.WordTrace]
  refine ⟨85828802169711426970445099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57219201446474284646963399 85828802169711426970445099)
  ·
    refine ⟨128743203254567140455667649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85828802169711426970445099 128743203254567140455667649)
    ·
      refine ⟨96557402440925355341750737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128743203254567140455667649 96557402440925355341750737)
      ·
        refine ⟨72418051830694016506313053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96557402440925355341750737 72418051830694016506313053)
        ·
          refine ⟨27156769436510256189867395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72418051830694016506313053 27156769436510256189867395)
          ·
            refine ⟨40735154154765384284801093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27156769436510256189867395 40735154154765384284801093)
            ·
              refine ⟨7637841404018509553400205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40735154154765384284801093 7637841404018509553400205)
              ·
                refine ⟨2864190526506941082525077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7637841404018509553400205 2864190526506941082525077)
                ·
                  refine ⟨134258930930012863243363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2864190526506941082525077 134258930930012863243363)
                  ·
                    rfl

theorem cell23_2353215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 6].length) (baseStart_2353215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353215 prefixEnd_2353215 := by exact prefixLift 2353215
  have htrace : WordTrace (prefixWord ++ tailWord_2353215) baseStart_2353215 baseEnd_2353215 := by
    simpa [prefixWord, tailWord_2353215, baseEnd_2353215] using wordTrace_append hprefix tailTrace_2353215
  have hstable : (prefixWord ++ tailWord_2353215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353215).length < 2 ^ (prefixWord ++ tailWord_2353215).sum := by decide
  have hdescent : baseEnd_2353215 < baseStart_2353215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353242 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3]
def baseStart_2353242 : Nat := 118140960795 + 2353242 * 2 ^ 59
def prefixEnd_2353242 : Nat := 4983230072969 + 3 ^ 40 * 2353242 * 2
def baseEnd_2353242 : Nat := 1208344242347787163552643

theorem tailTrace_2353242 : CollatzResearch.WordTrace tailWord_2353242 prefixEnd_2353242 1208344242347787163552643 := by
  unfold tailWord_2353242
  simp only [CollatzResearch.WordTrace]
  refine ⟨21457446735153402645419495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57219857960409073721118653 21457446735153402645419495)
  ·
    refine ⟨32186170102730103968129243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21457446735153402645419495 32186170102730103968129243)
    ·
      refine ⟨48279255154095155952193865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32186170102730103968129243 48279255154095155952193865)
      ·
        refine ⟨36209441365571366964145399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48279255154095155952193865 36209441365571366964145399)
        ·
          refine ⟨54314162048357050446218099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36209441365571366964145399 54314162048357050446218099)
          ·
            refine ⟨81471243072535575669327149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54314162048357050446218099 81471243072535575669327149)
            ·
              refine ⟨30551716152200840875997681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81471243072535575669327149 30551716152200840875997681)
              ·
                refine ⟨22913787114150630656998261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30551716152200840875997681 22913787114150630656998261)
                ·
                  refine ⟨2148167541951621624093587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22913787114150630656998261 2148167541951621624093587)
                  ·
                    refine ⟨3222251312927432436140381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2148167541951621624093587 3222251312927432436140381)
                    ·
                      refine ⟨1208344242347787163552643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3222251312927432436140381 1208344242347787163552643)
                      ·
                        rfl

theorem cell23_2353242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_2353242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353242 prefixEnd_2353242 := by exact prefixLift 2353242
  have htrace : WordTrace (prefixWord ++ tailWord_2353242) baseStart_2353242 baseEnd_2353242 := by
    simpa [prefixWord, tailWord_2353242, baseEnd_2353242] using wordTrace_append hprefix tailTrace_2353242
  have hstable : (prefixWord ++ tailWord_2353242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353242).length < 2 ^ (prefixWord ++ tailWord_2353242).sum := by decide
  have hdescent : baseEnd_2353242 < baseStart_2353242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353310 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_2353310 : Nat := 118140960795 + 2353310 * 2 ^ 59
def prefixEnd_2353310 : Nat := 4983230072969 + 3 ^ 40 * 2353310 * 2
def baseEnd_2353310 : Nat := 1208379159032292897502331

theorem tailTrace_2353310 : CollatzResearch.WordTrace tailWord_2353310 prefixEnd_2353310 1208379159032292897502331 := by
  unfold tailWord_2353310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10729033388045907274394173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57221511402911505463435589 10729033388045907274394173)
  ·
    refine ⟨4023387520517215227897815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10729033388045907274394173 4023387520517215227897815)
    ·
      refine ⟨6035081280775822841846723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4023387520517215227897815 6035081280775822841846723)
      ·
        refine ⟨9052621921163734262770085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6035081280775822841846723 9052621921163734262770085)
        ·
          refine ⟨1697366610218200174269391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9052621921163734262770085 1697366610218200174269391)
          ·
            refine ⟨2546049915327300261404087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697366610218200174269391 2546049915327300261404087)
            ·
              refine ⟨3819074872990950392106131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546049915327300261404087 3819074872990950392106131)
              ·
                refine ⟨5728612309486425588159197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3819074872990950392106131 5728612309486425588159197)
                ·
                  refine ⟨2148229616057409595559699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5728612309486425588159197 2148229616057409595559699)
                  ·
                    refine ⟨3222344424086114393339549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2148229616057409595559699 3222344424086114393339549)
                    ·
                      refine ⟨1208379159032292897502331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3222344424086114393339549 1208379159032292897502331)
                      ·
                        rfl

theorem cell23_2353310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_2353310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353310 prefixEnd_2353310 := by exact prefixLift 2353310
  have htrace : WordTrace (prefixWord ++ tailWord_2353310) baseStart_2353310 baseEnd_2353310 := by
    simpa [prefixWord, tailWord_2353310, baseEnd_2353310] using wordTrace_append hprefix tailTrace_2353310
  have hstable : (prefixWord ++ tailWord_2353310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353310).length < 2 ^ (prefixWord ++ tailWord_2353310).sum := by decide
  have hdescent : baseEnd_2353310 < baseStart_2353310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353333 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2353333 : Nat := 118140960795 + 2353333 * 2 ^ 59
def prefixEnd_2353333 : Nat := 4983230072969 + 3 ^ 40 * 2353333 * 2
def baseEnd_2353333 : Nat := 1208390969087346307514725

theorem tailTrace_2353333 : CollatzResearch.WordTrace tailWord_2353333 prefixEnd_2353333 1208390969087346307514725 := by
  unfold tailWord_2353333
  simp only [CollatzResearch.WordTrace]
  refine ⟨85833105983283933123240653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57222070655522622082160435 85833105983283933123240653)
  ·
    refine ⟨32187414743731474921215245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85833105983283933123240653 32187414743731474921215245)
    ·
      refine ⟨12070280528899303095455717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32187414743731474921215245 12070280528899303095455717)
      ·
        refine ⟨2263177599168619330397947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12070280528899303095455717 2263177599168619330397947)
        ·
          refine ⟨3394766398752928995596921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263177599168619330397947 3394766398752928995596921)
          ·
            refine ⟨2546074799064696746697691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3394766398752928995596921 2546074799064696746697691)
            ·
              refine ⟨3819112198597045120046537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546074799064696746697691 3819112198597045120046537)
              ·
                refine ⟨2864334148947783840034903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3819112198597045120046537 2864334148947783840034903)
                ·
                  refine ⟨4296501223421675760052355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864334148947783840034903 4296501223421675760052355)
                  ·
                    refine ⟨6444751835132513640078533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4296501223421675760052355 6444751835132513640078533)
                    ·
                      refine ⟨1208390969087346307514725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6444751835132513640078533 1208390969087346307514725)
                      ·
                        rfl

theorem cell23_2353333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2353333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353333 prefixEnd_2353333 := by exact prefixLift 2353333
  have htrace : WordTrace (prefixWord ++ tailWord_2353333) baseStart_2353333 baseEnd_2353333 := by
    simpa [prefixWord, tailWord_2353333, baseEnd_2353333] using wordTrace_append hprefix tailTrace_2353333
  have hstable : (prefixWord ++ tailWord_2353333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353333).length < 2 ^ (prefixWord ++ tailWord_2353333).sum := by decide
  have hdescent : baseEnd_2353333 < baseStart_2353333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353346 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2353346 : Nat := 118140960795 + 2353346 * 2 ^ 59
def prefixEnd_2353346 : Nat := 4983230072969 + 3 ^ 40 * 2353346 * 2
def baseEnd_2353346 : Nat := 1208397644335854756652165

theorem tailTrace_2353346 : CollatzResearch.WordTrace tailWord_2353346 prefixEnd_2353346 1208397644335854756652165 := by
  unfold tailWord_2353346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21458395033059209085865973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57222386754824557562309261 21458395033059209085865973)
  ·
    refine ⟨2011724534349300851799935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21458395033059209085865973 2011724534349300851799935)
    ·
      refine ⟨3017586801523951277699903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2011724534349300851799935 3017586801523951277699903)
      ·
        refine ⟨4526380202285926916549855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017586801523951277699903 4526380202285926916549855)
        ·
          refine ⟨6789570303428890374824783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526380202285926916549855 6789570303428890374824783)
          ·
            refine ⟨10184355455143335562237175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6789570303428890374824783 10184355455143335562237175)
            ·
              refine ⟨15276533182715003343355763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10184355455143335562237175 15276533182715003343355763)
              ·
                refine ⟨22914799774072505015033645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15276533182715003343355763 22914799774072505015033645)
                ·
                  refine ⟨8593049915277189380637617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22914799774072505015033645 8593049915277189380637617)
                  ·
                    refine ⟨6444787436457892035478213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8593049915277189380637617 6444787436457892035478213)
                    ·
                      refine ⟨1208397644335854756652165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6444787436457892035478213 1208397644335854756652165)
                      ·
                        rfl

theorem cell23_2353346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2353346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353346 prefixEnd_2353346 := by exact prefixLift 2353346
  have htrace : WordTrace (prefixWord ++ tailWord_2353346) baseStart_2353346 baseEnd_2353346 := by
    simpa [prefixWord, tailWord_2353346, baseEnd_2353346] using wordTrace_append hprefix tailTrace_2353346
  have hstable : (prefixWord ++ tailWord_2353346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353346).length < 2 ^ (prefixWord ++ tailWord_2353346).sum := by decide
  have hdescent : baseEnd_2353346 < baseStart_2353346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353385 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_2353385 : Nat := 118140960795 + 2353385 * 2 ^ 59
def prefixEnd_2353385 : Nat := 4983230072969 + 3 ^ 40 * 2353385 * 2
def baseEnd_2353385 : Nat := 1208417670081380104064485

theorem tailTrace_2353385 : CollatzResearch.WordTrace tailWord_2353385 prefixEnd_2353385 1208417670081380104064485 := by
  unfold tailWord_2353385
  simp only [CollatzResearch.WordTrace]
  refine ⟨85835002579095546004133609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57223335052730364002755739 85835002579095546004133609)
  ·
    refine ⟨64376251934321659503100207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85835002579095546004133609 64376251934321659503100207)
    ·
      refine ⟨96564377901482489254650311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64376251934321659503100207 96564377901482489254650311)
      ·
        refine ⟨144846566852223733881975467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96564377901482489254650311 144846566852223733881975467)
        ·
          refine ⟨217269850278335600822963201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144846566852223733881975467 217269850278335600822963201)
          ·
            refine ⟨162952387708751700617222401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217269850278335600822963201 162952387708751700617222401)
            ·
              refine ⟨122214290781563775462916801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162952387708751700617222401 122214290781563775462916801)
              ·
                refine ⟨91660718086172831597187601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122214290781563775462916801 91660718086172831597187601)
                ·
                  refine ⟨68745538564629623697890701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91660718086172831597187601 68745538564629623697890701)
                  ·
                    refine ⟨25779576961736108886709013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68745538564629623697890701 25779576961736108886709013)
                    ·
                      refine ⟨1208417670081380104064485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25779576961736108886709013 1208417670081380104064485)
                      ·
                        rfl

theorem cell23_2353385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_2353385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353385 prefixEnd_2353385 := by exact prefixLift 2353385
  have htrace : WordTrace (prefixWord ++ tailWord_2353385) baseStart_2353385 baseEnd_2353385 := by
    simpa [prefixWord, tailWord_2353385, baseEnd_2353385] using wordTrace_append hprefix tailTrace_2353385
  have hstable : (prefixWord ++ tailWord_2353385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353385).length < 2 ^ (prefixWord ++ tailWord_2353385).sum := by decide
  have hdescent : baseEnd_2353385 < baseStart_2353385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353406 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_2353406 : Nat := 118140960795 + 2353406 * 2 ^ 59
def prefixEnd_2353406 : Nat := 4983230072969 + 3 ^ 40 * 2353406 * 2
def baseEnd_2353406 : Nat := 1208428453175124521901889

theorem tailTrace_2353406 : CollatzResearch.WordTrace tailWord_2353406 prefixEnd_2353406 1208428453175124521901889 := by
  unfold tailWord_2353406
  simp only [CollatzResearch.WordTrace]
  refine ⟨10729471064002433323831009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57223845674679644393765381 10729471064002433323831009)
  ·
    refine ⟨8047103298001824992873257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10729471064002433323831009 8047103298001824992873257)
    ·
      refine ⟨6035327473501368744654943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8047103298001824992873257 6035327473501368744654943)
      ·
        refine ⟨9052991210252053116982415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6035327473501368744654943 9052991210252053116982415)
        ·
          refine ⟨13579486815378079675473623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9052991210252053116982415 13579486815378079675473623)
          ·
            refine ⟨20369230223067119513210435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13579486815378079675473623 20369230223067119513210435)
            ·
              refine ⟨30553845334600679269815653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20369230223067119513210435 30553845334600679269815653)
              ·
                refine ⟨5728846000237627363090435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30553845334600679269815653 5728846000237627363090435)
                ·
                  refine ⟨8593269000356441044635653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5728846000237627363090435 8593269000356441044635653)
                  ·
                    refine ⟨1611237937566832695869185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8593269000356441044635653 1611237937566832695869185)
                    ·
                      refine ⟨1208428453175124521901889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611237937566832695869185 1208428453175124521901889)
                      ·
                        rfl

theorem cell23_2353406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_2353406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353406 prefixEnd_2353406 := by exact prefixLift 2353406
  have htrace : WordTrace (prefixWord ++ tailWord_2353406) baseStart_2353406 baseEnd_2353406 := by
    simpa [prefixWord, tailWord_2353406, baseEnd_2353406] using wordTrace_append hprefix tailTrace_2353406
  have hstable : (prefixWord ++ tailWord_2353406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353406).length < 2 ^ (prefixWord ++ tailWord_2353406).sum := by decide
  have hdescent : baseEnd_2353406 < baseStart_2353406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353410 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_2353410 : Nat := 118140960795 + 2353410 * 2 ^ 59
def prefixEnd_2353410 : Nat := 4983230072969 + 3 ^ 40 * 2353410 * 2
def baseEnd_2353410 : Nat := 1208430507097742506251871

theorem tailTrace_2353410 : CollatzResearch.WordTrace tailWord_2353410 prefixEnd_2353410 1208430507097742506251871 := by
  unfold tailWord_2353410
  simp only [CollatzResearch.WordTrace]
  refine ⟨21458978601001243818448421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57223942936003316849195789 21458978601001243818448421)
  ·
    refine ⟨4023558487687733215959079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21458978601001243818448421 4023558487687733215959079)
    ·
      refine ⟨6035337731531599823938619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4023558487687733215959079 6035337731531599823938619)
      ·
        refine ⟨9053006597297399735907929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6035337731531599823938619 9053006597297399735907929)
        ·
          refine ⟨6789754947973049801930947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9053006597297399735907929 6789754947973049801930947)
          ·
            refine ⟨10184632421959574702896421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6789754947973049801930947 10184632421959574702896421)
            ·
              refine ⟨1909618579117420256793079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10184632421959574702896421 1909618579117420256793079)
              ·
                refine ⟨2864427868676130385189619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1909618579117420256793079 2864427868676130385189619)
                ·
                  refine ⟨4296641803014195577784429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864427868676130385189619 4296641803014195577784429)
                  ·
                    refine ⟨1611240676130323341669161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4296641803014195577784429 1611240676130323341669161)
                    ·
                      refine ⟨1208430507097742506251871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611240676130323341669161 1208430507097742506251871)
                      ·
                        rfl

theorem cell23_2353410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_2353410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353410 prefixEnd_2353410 := by exact prefixLift 2353410
  have htrace : WordTrace (prefixWord ++ tailWord_2353410) baseStart_2353410 baseEnd_2353410 := by
    simpa [prefixWord, tailWord_2353410, baseEnd_2353410] using wordTrace_append hprefix tailTrace_2353410
  have hstable : (prefixWord ++ tailWord_2353410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353410).length < 2 ^ (prefixWord ++ tailWord_2353410).sum := by decide
  have hdescent : baseEnd_2353410 < baseStart_2353410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353429 : List Nat := [1, 3, 2, 1, 2, 1, 4, 4, 5]
def baseStart_2353429 : Nat := 118140960795 + 2353429 * 2 ^ 59
def prefixEnd_2353429 : Nat := 4983230072969 + 3 ^ 40 * 2353429 * 2
def baseEnd_2353429 : Nat := 134271140358908659101587

theorem tailTrace_2353429 : CollatzResearch.WordTrace tailWord_2353429 prefixEnd_2353429 134271140358908659101587 := by
  unfold tailWord_2353429
  simp only [CollatzResearch.WordTrace]
  refine ⟨85836607390936141518735341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57224404927290761012490227 85836607390936141518735341)
  ·
    refine ⟨32188727771601053069525753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85836607390936141518735341 32188727771601053069525753)
    ·
      refine ⟨24141545828700789802144315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32188727771601053069525753 24141545828700789802144315)
      ·
        refine ⟨36212318743051184703216473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24141545828700789802144315 36212318743051184703216473)
        ·
          refine ⟨27159239057288388527412355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36212318743051184703216473 27159239057288388527412355)
          ·
            refine ⟨40738858585932582791118533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27159239057288388527412355 40738858585932582791118533)
            ·
              refine ⟨7638535984862359273334725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40738858585932582791118533 7638535984862359273334725)
              ·
                refine ⟨1432225497161692363750261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7638535984862359273334725 1432225497161692363750261)
                ·
                  refine ⟨134271140358908659101587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1432225497161692363750261 134271140358908659101587)
                  ·
                    rfl

theorem cell23_2353429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_2353429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353429 prefixEnd_2353429 := by exact prefixLift 2353429
  have htrace : WordTrace (prefixWord ++ tailWord_2353429) baseStart_2353429 baseEnd_2353429 := by
    simpa [prefixWord, tailWord_2353429, baseEnd_2353429] using wordTrace_append hprefix tailTrace_2353429
  have hstable : (prefixWord ++ tailWord_2353429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353429).length < 2 ^ (prefixWord ++ tailWord_2353429).sum := by decide
  have hdescent : baseEnd_2353429 < baseStart_2353429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353439 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 3]
def baseStart_2353439 : Nat := 118140960795 + 2353439 * 2 ^ 59
def prefixEnd_2353439 : Nat := 4983230072969 + 3 ^ 40 * 2353439 * 2
def baseEnd_2353439 : Nat := 1208445398036722892789237

theorem tailTrace_2353439 : CollatzResearch.WordTrace tailWord_2353439 prefixEnd_2353439 1208445398036722892789237 := by
  unfold tailWord_2353439
  simp only [CollatzResearch.WordTrace]
  refine ⟨85836972120899913226599371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57224648080599942151066247 85836972120899913226599371)
  ·
    refine ⟨128755458181349869839899057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85836972120899913226599371 128755458181349869839899057)
    ·
      refine ⟨96566593636012402379924293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128755458181349869839899057 96566593636012402379924293)
      ·
        refine ⟨18106236306752325446235805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96566593636012402379924293 18106236306752325446235805)
        ·
          refine ⟨6789838615032122042338427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18106236306752325446235805 6789838615032122042338427)
          ·
            refine ⟨10184757922548183063507641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6789838615032122042338427 10184757922548183063507641)
            ·
              refine ⟨7638568441911137297630731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10184757922548183063507641 7638568441911137297630731)
              ·
                refine ⟨11457852662866705946446097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638568441911137297630731 11457852662866705946446097)
                ·
                  refine ⟨8593389497150029459834573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11457852662866705946446097 8593389497150029459834573)
                  ·
                    refine ⟨3222521061431261047437965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8593389497150029459834573 3222521061431261047437965)
                    ·
                      refine ⟨1208445398036722892789237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3222521061431261047437965 1208445398036722892789237)
                      ·
                        rfl

theorem cell23_2353439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_2353439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353439 prefixEnd_2353439 := by exact prefixLift 2353439
  have htrace : WordTrace (prefixWord ++ tailWord_2353439) baseStart_2353439 baseEnd_2353439 := by
    simpa [prefixWord, tailWord_2353439, baseEnd_2353439] using wordTrace_append hprefix tailTrace_2353439
  have hstable : (prefixWord ++ tailWord_2353439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353439).length < 2 ^ (prefixWord ++ tailWord_2353439).sum := by decide
  have hdescent : baseEnd_2353439 < baseStart_2353439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353440 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 2, 2, 2]
def baseStart_2353440 : Nat := 118140960795 + 2353440 * 2 ^ 59
def prefixEnd_2353440 : Nat := 4983230072969 + 3 ^ 40 * 2353440 * 2
def baseEnd_2353440 : Nat := 1208445911517377388876733

theorem tailTrace_2353440 : CollatzResearch.WordTrace tailWord_2353440 prefixEnd_2353440 1208445911517377388876733 := by
  unfold tailWord_2353440
  simp only [CollatzResearch.WordTrace]
  refine ⟨42918504296948145198692887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57224672395930860264923849 42918504296948145198692887)
  ·
    refine ⟨64377756445422217798039331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42918504296948145198692887 64377756445422217798039331)
    ·
      refine ⟨96566634668133326697058997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64377756445422217798039331 96566634668133326697058997)
      ·
        refine ⟨9053122000137499377849281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96566634668133326697058997 9053122000137499377849281)
        ·
          refine ⟨6789841500103124533386961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9053122000137499377849281 6789841500103124533386961)
          ·
            refine ⟨5092381125077343400040221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6789841500103124533386961 5092381125077343400040221)
            ·
              refine ⟨1909642921904003775015083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5092381125077343400040221 1909642921904003775015083)
              ·
                refine ⟨2864464382856005662522625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1909642921904003775015083 2864464382856005662522625)
                ·
                  refine ⟨2148348287142004246891969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2864464382856005662522625 2148348287142004246891969)
                  ·
                    refine ⟨1611261215356503185168977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2148348287142004246891969 1611261215356503185168977)
                    ·
                      refine ⟨1208445911517377388876733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611261215356503185168977 1208445911517377388876733)
                      ·
                        rfl

theorem cell23_2353440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_2353440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353440 prefixEnd_2353440 := by exact prefixLift 2353440
  have htrace : WordTrace (prefixWord ++ tailWord_2353440) baseStart_2353440 baseEnd_2353440 := by
    simpa [prefixWord, tailWord_2353440, baseEnd_2353440] using wordTrace_append hprefix tailTrace_2353440
  have hstable : (prefixWord ++ tailWord_2353440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353440).length < 2 ^ (prefixWord ++ tailWord_2353440).sum := by decide
  have hdescent : baseEnd_2353440 < baseStart_2353440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353479 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_2353479 : Nat := 118140960795 + 2353479 * 2 ^ 59
def prefixEnd_2353479 : Nat := 4983230072969 + 3 ^ 40 * 2353479 * 2
def baseEnd_2353479 : Nat := 1208465937262902736289053

theorem tailTrace_2353479 : CollatzResearch.WordTrace tailWord_2353479 prefixEnd_2353479 1208465937262902736289053 := by
  unfold tailWord_2353479
  simp only [CollatzResearch.WordTrace]
  refine ⟨85838431040755000058055491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57225620693836666705370327 85838431040755000058055491)
  ·
    refine ⟨128757646561132500087083237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85838431040755000058055491 128757646561132500087083237)
    ·
      refine ⟨24142058730212343766328107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128757646561132500087083237 24142058730212343766328107)
      ·
        refine ⟨36213088095318515649492161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24142058730212343766328107 36213088095318515649492161)
        ·
          refine ⟨27159816071488886737119121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36213088095318515649492161 27159816071488886737119121)
          ·
            refine ⟨20369862053616665052839341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27159816071488886737119121 20369862053616665052839341)
            ·
              refine ⟨7638698270106249394814753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20369862053616665052839341 7638698270106249394814753)
              ·
                refine ⟨5729023702579687046111065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7638698270106249394814753 5729023702579687046111065)
                ·
                  refine ⟨4296767776934765284583299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5729023702579687046111065 4296767776934765284583299)
                  ·
                    refine ⟨6445151665402147926874949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4296767776934765284583299 6445151665402147926874949)
                    ·
                      refine ⟨1208465937262902736289053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6445151665402147926874949 1208465937262902736289053)
                      ·
                        rfl

theorem cell23_2353479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_2353479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353479 prefixEnd_2353479 := by exact prefixLift 2353479
  have htrace : WordTrace (prefixWord ++ tailWord_2353479) baseStart_2353479 baseEnd_2353479 := by
    simpa [prefixWord, tailWord_2353479, baseEnd_2353479] using wordTrace_append hprefix tailTrace_2353479
  have hstable : (prefixWord ++ tailWord_2353479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353479).length < 2 ^ (prefixWord ++ tailWord_2353479).sum := by decide
  have hdescent : baseEnd_2353479 < baseStart_2353479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353586 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_2353586 : Nat := 118140960795 + 2353586 * 2 ^ 59
def prefixEnd_2353586 : Nat := 4983230072969 + 3 ^ 40 * 2353586 * 2
def baseEnd_2353586 : Nat := 1208520879692933817651061

theorem tailTrace_2353586 : CollatzResearch.WordTrace tailWord_2353586 prefixEnd_2353586 1208520879692933817651061 := by
  unfold tailWord_2353586
  simp only [CollatzResearch.WordTrace]
  refine ⟨21460583412841839333050153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57228222434244904888133741 21460583412841839333050153)
  ·
    refine ⟨16095437559631379499787615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21460583412841839333050153 16095437559631379499787615)
    ·
      refine ⟨24143156339447069249681423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16095437559631379499787615 24143156339447069249681423)
      ·
        refine ⟨36214734509170603874522135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24143156339447069249681423 36214734509170603874522135)
        ·
          refine ⟨54322101763755905811783203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36214734509170603874522135 54322101763755905811783203)
          ·
            refine ⟨81483152645633858717674805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54322101763755905811783203 81483152645633858717674805)
            ·
              refine ⟨7639045560528174254782013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81483152645633858717674805 7639045560528174254782013)
              ·
                refine ⟨2864642085198065345543255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7639045560528174254782013 2864642085198065345543255)
                ·
                  refine ⟨4296963127797098018314883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864642085198065345543255 4296963127797098018314883)
                  ·
                    refine ⟨6445444691695647027472325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4296963127797098018314883 6445444691695647027472325)
                    ·
                      refine ⟨1208520879692933817651061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6445444691695647027472325 1208520879692933817651061)
                      ·
                        rfl

theorem cell23_2353586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_2353586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353586 prefixEnd_2353586 := by exact prefixLift 2353586
  have htrace : WordTrace (prefixWord ++ tailWord_2353586) baseStart_2353586 baseEnd_2353586 := by
    simpa [prefixWord, tailWord_2353586, baseEnd_2353586] using wordTrace_append hprefix tailTrace_2353586
  have hstable : (prefixWord ++ tailWord_2353586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353586).length < 2 ^ (prefixWord ++ tailWord_2353586).sum := by decide
  have hdescent : baseEnd_2353586 < baseStart_2353586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353620 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_2353620 : Nat := 118140960795 + 2353620 * 2 ^ 59
def prefixEnd_2353620 : Nat := 4983230072969 + 3 ^ 40 * 2353620 * 2
def baseEnd_2353620 : Nat := 1208538338035186684625905

theorem tailTrace_2353620 : CollatzResearch.WordTrace tailWord_2353620 prefixEnd_2353620 1208538338035186684625905 := by
  unfold tailWord_2353620
  simp only [CollatzResearch.WordTrace]
  refine ⟨42921786866622090569469157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57229049155496120759292209 42921786866622090569469157)
  ·
    refine ⟨8047835037491641981775467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42921786866622090569469157 8047835037491641981775467)
    ·
      refine ⟨12071752556237462972663201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8047835037491641981775467 12071752556237462972663201)
      ·
        refine ⟨9053814417178097229497401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12071752556237462972663201 9053814417178097229497401)
        ·
          refine ⟨6790360812883572922123051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9053814417178097229497401 6790360812883572922123051)
          ·
            refine ⟨10185541219325359383184577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6790360812883572922123051 10185541219325359383184577)
            ·
              refine ⟨7639155914494019537388433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10185541219325359383184577 7639155914494019537388433)
              ·
                refine ⟨5729366935870514653041325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7639155914494019537388433 5729366935870514653041325)
                ·
                  refine ⟨2148512600951442994890497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5729366935870514653041325 2148512600951442994890497)
                  ·
                    refine ⟨1611384450713582246167873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2148512600951442994890497 1611384450713582246167873)
                    ·
                      refine ⟨1208538338035186684625905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611384450713582246167873 1208538338035186684625905)
                      ·
                        rfl

theorem cell23_2353620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_2353620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353620 prefixEnd_2353620 := by exact prefixLift 2353620
  have htrace : WordTrace (prefixWord ++ tailWord_2353620) baseStart_2353620 baseEnd_2353620 := by
    simpa [prefixWord, tailWord_2353620, baseEnd_2353620] using wordTrace_append hprefix tailTrace_2353620
  have hstable : (prefixWord ++ tailWord_2353620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353620).length < 2 ^ (prefixWord ++ tailWord_2353620).sum := by decide
  have hdescent : baseEnd_2353620 < baseStart_2353620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353649 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_2353649 : Nat := 118140960795 + 2353649 * 2 ^ 59
def prefixEnd_2353649 : Nat := 4983230072969 + 3 ^ 40 * 2353649 * 2
def baseEnd_2353649 : Nat := 1208553228974167071163271

theorem tailTrace_2353649 : CollatzResearch.WordTrace tailWord_2353649 prefixEnd_2353649 1208553228974167071163271 := by
  unfold tailWord_2353649
  simp only [CollatzResearch.WordTrace]
  refine ⟨85844631450139119091744001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57229754300092746061162667 85844631450139119091744001)
  ·
    refine ⟨64383473587604339318808001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85844631450139119091744001 64383473587604339318808001)
    ·
      refine ⟨48287605190703254489106001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64383473587604339318808001 48287605190703254489106001)
      ·
        refine ⟨36215703893027440866829501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48287605190703254489106001 36215703893027440866829501)
        ·
          refine ⟨13580888959885290325061063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36215703893027440866829501 13580888959885290325061063)
          ·
            refine ⟨20371333439827935487591595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13580888959885290325061063 20371333439827935487591595)
            ·
              refine ⟨30557000159741903231387393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20371333439827935487591595 30557000159741903231387393)
              ·
                refine ⟨22917750119806427423540545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30557000159741903231387393 22917750119806427423540545)
                ·
                  refine ⟨17188312589854820567655409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22917750119806427423540545 17188312589854820567655409)
                  ·
                    refine ⟨12891234442391115425741557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17188312589854820567655409 12891234442391115425741557)
                    ·
                      refine ⟨1208553228974167071163271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12891234442391115425741557 1208553228974167071163271)
                      ·
                        rfl

theorem cell23_2353649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_2353649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353649 prefixEnd_2353649 := by exact prefixLift 2353649
  have htrace : WordTrace (prefixWord ++ tailWord_2353649) baseStart_2353649 baseEnd_2353649 := by
    simpa [prefixWord, tailWord_2353649, baseEnd_2353649] using wordTrace_append hprefix tailTrace_2353649
  have hstable : (prefixWord ++ tailWord_2353649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353649).length < 2 ^ (prefixWord ++ tailWord_2353649).sum := by decide
  have hdescent : baseEnd_2353649 < baseStart_2353649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353654 : List Nat := [5, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_2353654 : Nat := 118140960795 + 2353654 * 2 ^ 59
def prefixEnd_2353654 : Nat := 4983230072969 + 3 ^ 40 * 2353654 * 2
def baseEnd_2353654 : Nat := 1208555796377439551600749

theorem tailTrace_2353654 : CollatzResearch.WordTrace tailWord_2353654 prefixEnd_2353654 1208555796377439551600749 := by
  unfold tailWord_2353654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5365300863445062809104751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57229875876747336630450677 5365300863445062809104751)
  ·
    refine ⟨8047951295167594213657127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5365300863445062809104751 8047951295167594213657127)
    ·
      refine ⟨12071926942751391320485691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8047951295167594213657127 12071926942751391320485691)
      ·
        refine ⟨18107890414127086980728537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12071926942751391320485691 18107890414127086980728537)
        ·
          refine ⟨13580917810595315235546403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18107890414127086980728537 13580917810595315235546403)
          ·
            refine ⟨20371376715892972853319605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13580917810595315235546403 20371376715892972853319605)
            ·
              refine ⟨1909816567114966204998713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20371376715892972853319605 1909816567114966204998713)
              ·
                refine ⟨1432362425336224653749035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909816567114966204998713 1432362425336224653749035)
                ·
                  refine ⟨2148543638004336980623553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1432362425336224653749035 2148543638004336980623553)
                  ·
                    refine ⟨1611407728503252735467665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2148543638004336980623553 1611407728503252735467665)
                    ·
                      refine ⟨1208555796377439551600749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611407728503252735467665 1208555796377439551600749)
                      ·
                        rfl

theorem cell23_2353654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_2353654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353654 prefixEnd_2353654 := by exact prefixLift 2353654
  have htrace : WordTrace (prefixWord ++ tailWord_2353654) baseStart_2353654 baseEnd_2353654 := by
    simpa [prefixWord, tailWord_2353654, baseEnd_2353654] using wordTrace_append hprefix tailTrace_2353654
  have hstable : (prefixWord ++ tailWord_2353654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353654).length < 2 ^ (prefixWord ++ tailWord_2353654).sum := by decide
  have hdescent : baseEnd_2353654 < baseStart_2353654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353669 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_2353669 : Nat := 118140960795 + 2353669 * 2 ^ 59
def prefixEnd_2353669 : Nat := 4983230072969 + 3 ^ 40 * 2353669 * 2
def baseEnd_2353669 : Nat := 402854499529085664304393

theorem tailTrace_2353669 : CollatzResearch.WordTrace tailWord_2353669 prefixEnd_2353669 402854499529085664304393 := by
  unfold tailWord_2353669
  simp only [CollatzResearch.WordTrace]
  refine ⟨85845360910066662507472061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57230240606711108338314707 85845360910066662507472061)
  ·
    refine ⟨32192010341274998440302023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85845360910066662507472061 32192010341274998440302023)
    ·
      refine ⟨48288015511912497660453035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32192010341274998440302023 48288015511912497660453035)
      ·
        refine ⟨72432023267868746490679553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48288015511912497660453035 72432023267868746490679553)
        ·
          refine ⟨54324017450901559868009665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72432023267868746490679553 54324017450901559868009665)
          ·
            refine ⟨40743013088176169901007249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54324017450901559868009665 40743013088176169901007249)
            ·
              refine ⟨30557259816132127425755437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40743013088176169901007249 30557259816132127425755437)
              ·
                refine ⟨11458972431049547784658289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30557259816132127425755437 11458972431049547784658289)
                ·
                  refine ⟨8594229323287160838493717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11458972431049547784658289 8594229323287160838493717)
                  ·
                    refine ⟨402854499529085664304393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8594229323287160838493717 402854499529085664304393)
                    ·
                      rfl

theorem cell23_2353669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_2353669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353669 prefixEnd_2353669 := by exact prefixLift 2353669
  have htrace : WordTrace (prefixWord ++ tailWord_2353669) baseStart_2353669 baseEnd_2353669 := by
    simpa [prefixWord, tailWord_2353669, baseEnd_2353669] using wordTrace_append hprefix tailTrace_2353669
  have hstable : (prefixWord ++ tailWord_2353669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353669).length < 2 ^ (prefixWord ++ tailWord_2353669).sum := by decide
  have hdescent : baseEnd_2353669 < baseStart_2353669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353679 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_2353679 : Nat := 118140960795 + 2353679 * 2 ^ 59
def prefixEnd_2353679 : Nat := 4983230072969 + 3 ^ 40 * 2353679 * 2
def baseEnd_2353679 : Nat := 1208568633393801953788133

theorem tailTrace_2353679 : CollatzResearch.WordTrace tailWord_2353679 prefixEnd_2353679 1208568633393801953788133 := by
  unfold tailWord_2353679
  simp only [CollatzResearch.WordTrace]
  refine ⟨85845725640030434215336091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57230483760020289476890727 85845725640030434215336091)
  ·
    refine ⟨128768588460045651323004137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85845725640030434215336091 128768588460045651323004137)
    ·
      refine ⟨96576441345034238492253103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128768588460045651323004137 96576441345034238492253103)
      ·
        refine ⟨144864662017551357738379655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96576441345034238492253103 144864662017551357738379655)
        ·
          refine ⟨217296993026327036607569483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144864662017551357738379655 217296993026327036607569483)
          ·
            refine ⟨325945489539490554911354225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217296993026327036607569483 325945489539490554911354225)
            ·
              refine ⟨244459117154617916183515669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325945489539490554911354225 244459117154617916183515669)
              ·
                refine ⟨11459021116622714821102297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 244459117154617916183515669 11459021116622714821102297)
                ·
                  refine ⟨8594265837467036115826723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11459021116622714821102297 8594265837467036115826723)
                  ·
                    refine ⟨12891398756200554173740085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8594265837467036115826723 12891398756200554173740085)
                    ·
                      refine ⟨1208568633393801953788133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12891398756200554173740085 1208568633393801953788133)
                      ·
                        rfl

theorem cell23_2353679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_2353679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353679 prefixEnd_2353679 := by exact prefixLift 2353679
  have htrace : WordTrace (prefixWord ++ tailWord_2353679) baseStart_2353679 baseEnd_2353679 := by
    simpa [prefixWord, tailWord_2353679, baseEnd_2353679] using wordTrace_append hprefix tailTrace_2353679
  have hstable : (prefixWord ++ tailWord_2353679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353679).length < 2 ^ (prefixWord ++ tailWord_2353679).sum := by decide
  have hdescent : baseEnd_2353679 < baseStart_2353679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353689 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_2353689 : Nat := 118140960795 + 2353689 * 2 ^ 59
def prefixEnd_2353689 : Nat := 4983230072969 + 3 ^ 40 * 2353689 * 2
def baseEnd_2353689 : Nat := 1208573768200346914663087

theorem tailTrace_2353689 : CollatzResearch.WordTrace tailWord_2353689 prefixEnd_2353689 1208573768200346914663087 := by
  unfold tailWord_2353689
  simp only [CollatzResearch.WordTrace]
  refine ⟨85846090369994205923200121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57230726913329470615466747 85846090369994205923200121)
  ·
    refine ⟨64384567777495654442400091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85846090369994205923200121 64384567777495654442400091)
    ·
      refine ⟨96576851666243481663600137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64384567777495654442400091 96576851666243481663600137)
      ·
        refine ⟨72432638749682611247700103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96576851666243481663600137 72432638749682611247700103)
        ·
          refine ⟨108648958124523916871550155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72432638749682611247700103 108648958124523916871550155)
          ·
            refine ⟨162973437186785875307325233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108648958124523916871550155 162973437186785875307325233)
            ·
              refine ⟨122230077890089406480493925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162973437186785875307325233 122230077890089406480493925)
              ·
                refine ⟨22918139604391763715092611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122230077890089406480493925 22918139604391763715092611)
                ·
                  refine ⟨34377209406587645572638917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22918139604391763715092611 34377209406587645572638917)
                  ·
                    refine ⟨6445726763735183544869797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34377209406587645572638917 6445726763735183544869797)
                    ·
                      refine ⟨1208573768200346914663087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6445726763735183544869797 1208573768200346914663087)
                      ·
                        rfl

theorem cell23_2353689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_2353689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353689 prefixEnd_2353689 := by exact prefixLift 2353689
  have htrace : WordTrace (prefixWord ++ tailWord_2353689) baseStart_2353689 baseEnd_2353689 := by
    simpa [prefixWord, tailWord_2353689, baseEnd_2353689] using wordTrace_append hprefix tailTrace_2353689
  have hstable : (prefixWord ++ tailWord_2353689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353689).length < 2 ^ (prefixWord ++ tailWord_2353689).sum := by decide
  have hdescent : baseEnd_2353689 < baseStart_2353689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353693 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_2353693 : Nat := 118140960795 + 2353693 * 2 ^ 59
def prefixEnd_2353693 : Nat := 4983230072969 + 3 ^ 40 * 2353693 * 2
def baseEnd_2353693 : Nat := 1208575822122964899013069

theorem tailTrace_2353693 : CollatzResearch.WordTrace tailWord_2353693 prefixEnd_2353693 1208575822122964899013069 := by
  unfold tailWord_2353693
  simp only [CollatzResearch.WordTrace]
  refine ⟨85846236261979714606345733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57230824174653143070897155 85846236261979714606345733)
  ·
    refine ⟨16096169299121196488689825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85846236261979714606345733 16096169299121196488689825)
    ·
      refine ⟨12072126974340897366517369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16096169299121196488689825 12072126974340897366517369)
      ·
        refine ⟨9054095230755673024888027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12072126974340897366517369 9054095230755673024888027)
        ·
          refine ⟨13581142846133509537332041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9054095230755673024888027 13581142846133509537332041)
          ·
            refine ⟨10185857134600132152999031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13581142846133509537332041 10185857134600132152999031)
            ·
              refine ⟨15278785701900198229498547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10185857134600132152999031 15278785701900198229498547)
              ·
                refine ⟨22918178552850297344247821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15278785701900198229498547 22918178552850297344247821)
                ·
                  refine ⟨8594316957318861504092933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22918178552850297344247821 8594316957318861504092933)
                  ·
                    refine ⟨1611434429497286532017425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8594316957318861504092933 1611434429497286532017425)
                    ·
                      refine ⟨1208575822122964899013069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1611434429497286532017425 1208575822122964899013069)
                      ·
                        rfl

theorem cell23_2353693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_2353693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353693 prefixEnd_2353693 := by exact prefixLift 2353693
  have htrace : WordTrace (prefixWord ++ tailWord_2353693) baseStart_2353693 baseEnd_2353693 := by
    simpa [prefixWord, tailWord_2353693, baseEnd_2353693] using wordTrace_append hprefix tailTrace_2353693
  have hstable : (prefixWord ++ tailWord_2353693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353693).length < 2 ^ (prefixWord ++ tailWord_2353693).sum := by decide
  have hdescent : baseEnd_2353693 < baseStart_2353693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353739 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 7]
def baseStart_2353739 : Nat := 118140960795 + 2353739 * 2 ^ 59
def prefixEnd_2353739 : Nat := 4983230072969 + 3 ^ 40 * 2353739 * 2
def baseEnd_2353739 : Nat := 1208599442233071719037857

theorem tailTrace_2353739 : CollatzResearch.WordTrace tailWord_2353739 prefixEnd_2353739 1208599442233071719037857 := by
  unfold tailWord_2353739
  simp only [CollatzResearch.WordTrace]
  refine ⟨85847914019813064462520271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57231942679875376308346847 85847914019813064462520271)
  ·
    refine ⟨128771871029719596693780407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85847914019813064462520271 128771871029719596693780407)
    ·
      refine ⟨193157806544579395040670611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128771871029719596693780407 193157806544579395040670611)
      ·
        refine ⟨289736709816869092561005917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193157806544579395040670611 289736709816869092561005917)
        ·
          refine ⟨108651266181325909710377219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289736709816869092561005917 108651266181325909710377219)
          ·
            refine ⟨162976899271988864565565829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108651266181325909710377219 162976899271988864565565829)
            ·
              refine ⟨30558168613497912106043593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162976899271988864565565829 30558168613497912106043593)
              ·
                refine ⟨22918626460123434079532695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30558168613497912106043593 22918626460123434079532695)
                ·
                  refine ⟨34377939690185151119299043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22918626460123434079532695 34377939690185151119299043)
                  ·
                    refine ⟨51566909535277726678948565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34377939690185151119299043 51566909535277726678948565)
                    ·
                      refine ⟨1208599442233071719037857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51566909535277726678948565 1208599442233071719037857)
                      ·
                        rfl

theorem cell23_2353739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_2353739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353739 prefixEnd_2353739 := by exact prefixLift 2353739
  have htrace : WordTrace (prefixWord ++ tailWord_2353739) baseStart_2353739 baseEnd_2353739 := by
    simpa [prefixWord, tailWord_2353739, baseEnd_2353739] using wordTrace_append hprefix tailTrace_2353739
  have hstable : (prefixWord ++ tailWord_2353739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353739).length < 2 ^ (prefixWord ++ tailWord_2353739).sum := by decide
  have hdescent : baseEnd_2353739 < baseStart_2353739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353746 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2353746 : Nat := 118140960795 + 2353746 * 2 ^ 59
def prefixEnd_2353746 : Nat := 4983230072969 + 3 ^ 40 * 2353746 * 2
def baseEnd_2353746 : Nat := 402867678865884397216775

theorem tailTrace_2353746 : CollatzResearch.WordTrace tailWord_2353746 prefixEnd_2353746 402867678865884397216775 := by
  unfold tailWord_2353746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21462042332696926164506273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57232112887191803105350061 21462042332696926164506273)
  ·
    refine ⟨16096531749522694623379705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21462042332696926164506273 16096531749522694623379705)
    ·
      refine ⟨12072398812142020967534779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16096531749522694623379705 12072398812142020967534779)
      ·
        refine ⟨18108598218213031451302169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12072398812142020967534779 18108598218213031451302169)
        ·
          refine ⟨13581448663659773588476627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18108598218213031451302169 13581448663659773588476627)
          ·
            refine ⟨20372172995489660382714941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13581448663659773588476627 20372172995489660382714941)
            ·
              refine ⟨7639564873308622643518103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20372172995489660382714941 7639564873308622643518103)
              ·
                refine ⟨11459347309962933965277155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7639564873308622643518103 11459347309962933965277155)
                ·
                  refine ⟨17189020964944400947915733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11459347309962933965277155 17189020964944400947915733)
                  ·
                    refine ⟨402867678865884397216775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17189020964944400947915733 402867678865884397216775)
                    ·
                      rfl

theorem cell23_2353746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2353746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353746 prefixEnd_2353746 := by exact prefixLift 2353746
  have htrace : WordTrace (prefixWord ++ tailWord_2353746) baseStart_2353746 baseEnd_2353746 := by
    simpa [prefixWord, tailWord_2353746, baseEnd_2353746] using wordTrace_append hprefix tailTrace_2353746
  have hstable : (prefixWord ++ tailWord_2353746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353746).length < 2 ^ (prefixWord ++ tailWord_2353746).sum := by decide
  have hdescent : baseEnd_2353746 < baseStart_2353746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
