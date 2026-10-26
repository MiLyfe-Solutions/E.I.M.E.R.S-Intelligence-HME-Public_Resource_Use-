import V185TrunkScan20Chunk156

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_956298 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_956298 : Nat := 118140960795 + 956298 * 2 ^ 59
def prefixEnd_956298 : Nat := 4983230072969 + 3 ^ 40 * 956298 * 2
def baseEnd_956298 : Nat := 436480464829693078557397

theorem tailTrace_956298 : CollatzResearch.WordTrace tailWord_956298 prefixEnd_956298 436480464829693078557397 := by
  unfold tailWord_956298
  simp only [CollatzResearch.WordTrace]
  refine ⟨8719763372375785885181387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23252702326335429027150365 8719763372375785885181387)
  ·
    refine ⟨13079645058563678827772081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8719763372375785885181387 13079645058563678827772081)
    ·
      refine ⟨9809733793922759120829061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13079645058563678827772081 9809733793922759120829061)
      ·
        refine ⟨1839325086360517335155449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9809733793922759120829061 1839325086360517335155449)
        ·
          refine ⟨1379493814770388001366587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1839325086360517335155449 1379493814770388001366587)
          ·
            refine ⟨2069240722155582002049881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379493814770388001366587 2069240722155582002049881)
            ·
              refine ⟨1551930541616686501537411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2069240722155582002049881 1551930541616686501537411)
              ·
                refine ⟨2327895812425029752306117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551930541616686501537411 2327895812425029752306117)
                ·
                  refine ⟨436480464829693078557397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2327895812425029752306117 436480464829693078557397)
                  ·
                    rfl

theorem cell20_956298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_956298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956298 prefixEnd_956298 := by exact prefixLift 956298
  have htrace : WordTrace (prefixWord ++ tailWord_956298) baseStart_956298 baseEnd_956298 := by
    simpa [prefixWord, tailWord_956298, baseEnd_956298] using wordTrace_append hprefix tailTrace_956298
  have hstable : (prefixWord ++ tailWord_956298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956298).length < 2 ^ (prefixWord ++ tailWord_956298).sum := by decide
  have hdescent : baseEnd_956298 < baseStart_956298 := by decide
  rcases family_descends (prefixWord ++ tailWord_956298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956309 : List Nat := [1, 3, 2, 1, 1, 3, 2, 7]
def baseStart_956309 : Nat := 118140960795 + 956309 * 2 ^ 59
def prefixEnd_956309 : Nat := 4983230072969 + 3 ^ 40 * 956309 * 2
def baseEnd_956309 : Nat := 145495161843141976396895

theorem tailTrace_956309 : CollatzResearch.WordTrace tailWord_956309 prefixEnd_956309 145495161843141976396895 := by
  unfold tailWord_956309
  simp only [CollatzResearch.WordTrace]
  refine ⟨34879454692463292419375981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23252969794975528279583987 34879454692463292419375981)
  ·
    refine ⟨13079795509673734657265993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34879454692463292419375981 13079795509673734657265993)
    ·
      refine ⟨9809846632255300992949495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13079795509673734657265993 9809846632255300992949495)
      ·
        refine ⟨14714769948382951489424243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9809846632255300992949495 14714769948382951489424243)
        ·
          refine ⟨22072154922574427234136365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14714769948382951489424243 22072154922574427234136365)
          ·
            refine ⟨8277058095965410212801137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22072154922574427234136365 8277058095965410212801137)
            ·
              refine ⟨6207793571974057659600853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8277058095965410212801137 6207793571974057659600853)
              ·
                refine ⟨145495161843141976396895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6207793571974057659600853 145495161843141976396895)
                ·
                  rfl

theorem cell20_956309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_956309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956309 prefixEnd_956309 := by exact prefixLift 956309
  have htrace : WordTrace (prefixWord ++ tailWord_956309) baseStart_956309 baseEnd_956309 := by
    simpa [prefixWord, tailWord_956309, baseEnd_956309] using wordTrace_append hprefix tailTrace_956309
  have hstable : (prefixWord ++ tailWord_956309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956309).length < 2 ^ (prefixWord ++ tailWord_956309).sum := by decide
  have hdescent : baseEnd_956309 < baseStart_956309 := by decide
  rcases family_descends (prefixWord ++ tailWord_956309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956318 : List Nat := [4, 3, 1, 3, 2, 1, 2, 4]
def baseStart_956318 : Nat := 118140960795 + 956318 * 2 ^ 59
def prefixEnd_956318 : Nat := 4983230072969 + 3 ^ 40 * 956318 * 2
def baseEnd_956318 : Nat := 145496531124887299296883

theorem tailTrace_956318 : CollatzResearch.WordTrace tailWord_956318 prefixEnd_956318 145496531124887299296883 := by
  unfold tailWord_956318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4359972868678835869556701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23253188632953791304302405 4359972868678835869556701)
  ·
    refine ⟨1634989825754563451083763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4359972868678835869556701 1634989825754563451083763)
    ·
      refine ⟨2452484738631845176625645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634989825754563451083763 2452484738631845176625645)
      ·
        refine ⟨919681776986941941234617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2452484738631845176625645 919681776986941941234617)
        ·
          refine ⟨689761332740206455925963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919681776986941941234617 689761332740206455925963)
          ·
            refine ⟨1034641999110309683888945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689761332740206455925963 1034641999110309683888945)
            ·
              refine ⟨775981499332732262916709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034641999110309683888945 775981499332732262916709)
              ·
                refine ⟨145496531124887299296883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775981499332732262916709 145496531124887299296883)
                ·
                  rfl

theorem cell20_956318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_956318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956318 prefixEnd_956318 := by exact prefixLift 956318
  have htrace : WordTrace (prefixWord ++ tailWord_956318) baseStart_956318 baseEnd_956318 := by
    simpa [prefixWord, tailWord_956318, baseEnd_956318] using wordTrace_append hprefix tailTrace_956318
  have hstable : (prefixWord ++ tailWord_956318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956318).length < 2 ^ (prefixWord ++ tailWord_956318).sum := by decide
  have hdescent : baseEnd_956318 < baseStart_956318 := by decide
  rcases family_descends (prefixWord ++ tailWord_956318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956322 : List Nat := [3, 3, 1, 2, 3, 2, 2, 4]
def baseStart_956322 : Nat := 118140960795 + 956322 * 2 ^ 59
def prefixEnd_956322 : Nat := 4983230072969 + 3 ^ 40 * 956322 * 2
def baseEnd_956322 : Nat := 145497139694551887252433

theorem tailTrace_956322 : CollatzResearch.WordTrace tailWord_956322 prefixEnd_956322 145497139694551887252433 := by
  unfold tailWord_956322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8719982210354048909899805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23253285894277463759732813 8719982210354048909899805)
  ·
    refine ⟨3269993328882768341212427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8719982210354048909899805 3269993328882768341212427)
    ·
      refine ⟨4904989993324152511818641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269993328882768341212427 4904989993324152511818641)
      ·
        refine ⟨3678742494993114383863981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4904989993324152511818641 3678742494993114383863981)
        ·
          refine ⟨1379528435622417893948993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3678742494993114383863981 1379528435622417893948993)
          ·
            refine ⟨1034646326716813420461745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1379528435622417893948993 1034646326716813420461745)
            ·
              refine ⟨775984745037610065346309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034646326716813420461745 775984745037610065346309)
              ·
                refine ⟨145497139694551887252433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775984745037610065346309 145497139694551887252433)
                ·
                  rfl

theorem cell20_956322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_956322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956322 prefixEnd_956322 := by exact prefixLift 956322
  have htrace : WordTrace (prefixWord ++ tailWord_956322) baseStart_956322 baseEnd_956322 := by
    simpa [prefixWord, tailWord_956322, baseEnd_956322] using wordTrace_append hprefix tailTrace_956322
  have hstable : (prefixWord ++ tailWord_956322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956322).length < 2 ^ (prefixWord ++ tailWord_956322).sum := by decide
  have hdescent : baseEnd_956322 < baseStart_956322 := by decide
  rcases family_descends (prefixWord ++ tailWord_956322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956364 : List Nat := [2, 2, 1, 4, 1, 3, 2, 5]
def baseStart_956364 : Nat := 118140960795 + 956364 * 2 ^ 59
def prefixEnd_956364 : Nat := 4983230072969 + 3 ^ 40 * 956364 * 2
def baseEnd_956364 : Nat := 145503529676030060785709

theorem tailTrace_956364 : CollatzResearch.WordTrace tailWord_956364 prefixEnd_956364 145503529676030060785709 := by
  unfold tailWord_956364
  simp only [CollatzResearch.WordTrace]
  refine ⟨17440730353632018406314073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23254307138176024541752097 17440730353632018406314073)
  ·
    refine ⟨13080547765224013804735555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17440730353632018406314073 13080547765224013804735555)
    ·
      refine ⟨19620821647836020707103333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13080547765224013804735555 19620821647836020707103333)
      ·
        refine ⟨3678904058969253882581875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19620821647836020707103333 3678904058969253882581875)
        ·
          refine ⟨5518356088453880823872813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678904058969253882581875 5518356088453880823872813)
          ·
            refine ⟨2069383533170205308952305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5518356088453880823872813 2069383533170205308952305)
            ·
              refine ⟨1552037649877653981714229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2069383533170205308952305 1552037649877653981714229)
              ·
                refine ⟨145503529676030060785709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1552037649877653981714229 145503529676030060785709)
                ·
                  rfl

theorem cell20_956364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_956364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956364 prefixEnd_956364 := by exact prefixLift 956364
  have htrace : WordTrace (prefixWord ++ tailWord_956364) baseStart_956364 baseEnd_956364 := by
    simpa [prefixWord, tailWord_956364, baseEnd_956364] using wordTrace_append hprefix tailTrace_956364
  have hstable : (prefixWord ++ tailWord_956364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956364).length < 2 ^ (prefixWord ++ tailWord_956364).sum := by decide
  have hdescent : baseEnd_956364 < baseStart_956364 := by decide
  rcases family_descends (prefixWord ++ tailWord_956364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956385 : List Nat := [1, 2, 3, 1, 2, 1, 4, 6]
def baseStart_956385 : Nat := 118140960795 + 956385 * 2 ^ 59
def prefixEnd_956385 : Nat := 4983230072969 + 3 ^ 40 * 956385 * 2
def baseEnd_956385 : Nat := 145506724666769147552347

theorem tailTrace_956385 : CollatzResearch.WordTrace tailWord_956385 prefixEnd_956385 145506724666769147552347 := by
  unfold tailWord_956385
  simp only [CollatzResearch.WordTrace]
  refine ⟨34882226640187957399142609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23254817760125304932761739 34882226640187957399142609)
  ·
    refine ⟨26161669980140968049356957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34882226640187957399142609 26161669980140968049356957)
    ·
      refine ⟨9810626242552863018508859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26161669980140968049356957 9810626242552863018508859)
      ·
        refine ⟨14715939363829294527763289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9810626242552863018508859 14715939363829294527763289)
        ·
          refine ⟨11036954522871970895822467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14715939363829294527763289 11036954522871970895822467)
          ·
            refine ⟨16555431784307956343733701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11036954522871970895822467 16555431784307956343733701)
            ·
              refine ⟨3104143459557741814450069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16555431784307956343733701 3104143459557741814450069)
              ·
                refine ⟨145506724666769147552347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3104143459557741814450069 145506724666769147552347)
                ·
                  rfl

theorem cell20_956385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_956385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956385 prefixEnd_956385 := by exact prefixLift 956385
  have htrace : WordTrace (prefixWord ++ tailWord_956385) baseStart_956385 baseEnd_956385 := by
    simpa [prefixWord, tailWord_956385, baseEnd_956385] using wordTrace_append hprefix tailTrace_956385
  have hstable : (prefixWord ++ tailWord_956385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956385).length < 2 ^ (prefixWord ++ tailWord_956385).sum := by decide
  have hdescent : baseEnd_956385 < baseStart_956385 := by decide
  rcases family_descends (prefixWord ++ tailWord_956385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956409 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 3]
def baseStart_956409 : Nat := 118140960795 + 956409 * 2 ^ 59
def prefixEnd_956409 : Nat := 4983230072969 + 3 ^ 40 * 956409 * 2
def baseEnd_956409 : Nat := 436531128254270025856943

theorem tailTrace_956409 : CollatzResearch.WordTrace tailWord_956409 prefixEnd_956409 436531128254270025856943 := by
  unfold tailWord_956409
  simp only [CollatzResearch.WordTrace]
  refine ⟨34883101992101009498016281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23255401328067339665344187 34883101992101009498016281)
  ·
    refine ⟨26162326494075757123512211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34883101992101009498016281 26162326494075757123512211)
    ·
      refine ⟨39243489741113635685268317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26162326494075757123512211 39243489741113635685268317)
      ·
        refine ⟨14716308652917613381975619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39243489741113635685268317 14716308652917613381975619)
        ·
          refine ⟨22074462979376420072963429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14716308652917613381975619 22074462979376420072963429)
          ·
            refine ⟨4138961808633078763680643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22074462979376420072963429 4138961808633078763680643)
            ·
              refine ⟨6208442712949618145520965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138961808633078763680643 6208442712949618145520965)
              ·
                refine ⟨1164083008678053402285181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6208442712949618145520965 1164083008678053402285181)
                ·
                  refine ⟨436531128254270025856943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164083008678053402285181 436531128254270025856943)
                  ·
                    rfl

theorem cell20_956409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_956409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956409 prefixEnd_956409 := by exact prefixLift 956409
  have htrace : WordTrace (prefixWord ++ tailWord_956409) baseStart_956409 baseEnd_956409 := by
    simpa [prefixWord, tailWord_956409, baseEnd_956409] using wordTrace_append hprefix tailTrace_956409
  have hstable : (prefixWord ++ tailWord_956409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956409).length < 2 ^ (prefixWord ++ tailWord_956409).sum := by decide
  have hdescent : baseEnd_956409 < baseStart_956409 := by decide
  rcases family_descends (prefixWord ++ tailWord_956409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956440 : List Nat := [2, 1, 2, 3, 2, 1, 5, 4]
def baseStart_956440 : Nat := 118140960795 + 956440 * 2 ^ 59
def prefixEnd_956440 : Nat := 4983230072969 + 3 ^ 40 * 956440 * 2
def baseEnd_956440 : Nat := 145515092499657231941161

theorem tailTrace_956440 : CollatzResearch.WordTrace tailWord_956440 prefixEnd_956440 145515092499657231941161 := by
  unfold tailWord_956440
  simp only [CollatzResearch.WordTrace]
  refine ⟨17442116327494350896197387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23256155103325801194929849 17442116327494350896197387)
  ·
    refine ⟨26163174491241526344296081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17442116327494350896197387 26163174491241526344296081)
    ·
      refine ⟨19622380868431144758222061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26163174491241526344296081 19622380868431144758222061)
      ·
        refine ⟨7358392825661679284333273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19622380868431144758222061 7358392825661679284333273)
        ·
          refine ⟨5518794619246259463249955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7358392825661679284333273 5518794619246259463249955)
          ·
            refine ⟨8278191928869389194874933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5518794619246259463249955 8278191928869389194874933)
            ·
              refine ⟨776080493331505237019525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8278191928869389194874933 776080493331505237019525)
              ·
                refine ⟨145515092499657231941161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 776080493331505237019525 145515092499657231941161)
                ·
                  rfl

theorem cell20_956440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_956440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956440 prefixEnd_956440 := by exact prefixLift 956440
  have htrace : WordTrace (prefixWord ++ tailWord_956440) baseStart_956440 baseEnd_956440 := by
    simpa [prefixWord, tailWord_956440, baseEnd_956440] using wordTrace_append hprefix tailTrace_956440
  have hstable : (prefixWord ++ tailWord_956440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956440).length < 2 ^ (prefixWord ++ tailWord_956440).sum := by decide
  have hdescent : baseEnd_956440 < baseStart_956440 := by decide
  rcases family_descends (prefixWord ++ tailWord_956440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956450 : List Nat := [3, 3, 1, 1, 1, 2, 4, 3, 2]
def baseStart_956450 : Nat := 118140960795 + 956450 * 2 ^ 59
def prefixEnd_956450 : Nat := 4983230072969 + 3 ^ 40 * 956450 * 2
def baseEnd_956450 : Nat := 436549841771456105490109

theorem tailTrace_956450 : CollatzResearch.WordTrace tailWord_956450 prefixEnd_956450 436549841771456105490109 := by
  unfold tailWord_956450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721149346238118375064701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23256398256634982333505869 8721149346238118375064701)
  ·
    refine ⟨3270431004839294390649263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8721149346238118375064701 3270431004839294390649263)
    ·
      refine ⟨4905646507258941585973895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3270431004839294390649263 4905646507258941585973895)
      ·
        refine ⟨7358469760888412378960843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4905646507258941585973895 7358469760888412378960843)
        ·
          refine ⟨11037704641332618568441265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358469760888412378960843 11037704641332618568441265)
          ·
            refine ⟨8278278480999463926330949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11037704641332618568441265 8278278480999463926330949)
            ·
              refine ⟨1552177215187399486187053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8278278480999463926330949 1552177215187399486187053)
              ·
                refine ⟨582066455695274807320145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552177215187399486187053 582066455695274807320145)
                ·
                  refine ⟨436549841771456105490109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582066455695274807320145 436549841771456105490109)
                  ·
                    rfl

theorem cell20_956450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_956450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956450 prefixEnd_956450 := by exact prefixLift 956450
  have htrace : WordTrace (prefixWord ++ tailWord_956450) baseStart_956450 baseEnd_956450 := by
    simpa [prefixWord, tailWord_956450, baseEnd_956450] using wordTrace_append hprefix tailTrace_956450
  have hstable : (prefixWord ++ tailWord_956450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956450).length < 2 ^ (prefixWord ++ tailWord_956450).sum := by decide
  have hdescent : baseEnd_956450 < baseStart_956450 := by decide
  rcases family_descends (prefixWord ++ tailWord_956450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956464 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 3]
def baseStart_956464 : Nat := 118140960795 + 956464 * 2 ^ 59
def prefixEnd_956464 : Nat := 4983230072969 + 3 ^ 40 * 956464 * 2
def baseEnd_956464 : Nat := 436556231752934279023385

theorem tailTrace_956464 : CollatzResearch.WordTrace tailWord_956464 prefixEnd_956464 436556231752934279023385 := by
  unfold tailWord_956464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17442554003450876945634223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23256738671267835927512297 17442554003450876945634223)
  ·
    refine ⟨26163831005176315418451335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17442554003450876945634223 26163831005176315418451335)
    ·
      refine ⟨39245746507764473127677003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26163831005176315418451335 39245746507764473127677003)
      ·
        refine ⟨58868619761646709691515505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39245746507764473127677003 58868619761646709691515505)
        ·
          refine ⟨44151464821235032268636629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58868619761646709691515505 44151464821235032268636629)
          ·
            refine ⟨1034799956747696068796171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44151464821235032268636629 1034799956747696068796171)
            ·
              refine ⟨1552199935121544103194257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034799956747696068796171 1552199935121544103194257)
              ·
                refine ⟨1164149951341158077395693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552199935121544103194257 1164149951341158077395693)
                ·
                  refine ⟨436556231752934279023385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164149951341158077395693 436556231752934279023385)
                  ·
                    rfl

theorem cell20_956464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_956464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956464 prefixEnd_956464 := by exact prefixLift 956464
  have htrace : WordTrace (prefixWord ++ tailWord_956464) baseStart_956464 baseEnd_956464 := by
    simpa [prefixWord, tailWord_956464, baseEnd_956464] using wordTrace_append hprefix tailTrace_956464
  have hstable : (prefixWord ++ tailWord_956464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956464).length < 2 ^ (prefixWord ++ tailWord_956464).sum := by decide
  have hdescent : baseEnd_956464 < baseStart_956464 := by decide
  rcases family_descends (prefixWord ++ tailWord_956464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956471 : List Nat := [1, 1, 3, 1, 2, 2, 4, 4, 2]
def baseStart_956471 : Nat := 118140960795 + 956471 * 2 ^ 59
def prefixEnd_956471 : Nat := 4983230072969 + 3 ^ 40 * 956471 * 2
def baseEnd_956471 : Nat := 436559426743673365790023

theorem tailTrace_956471 : CollatzResearch.WordTrace tailWord_956471 prefixEnd_956471 436559426743673365790023 := by
  unfold tailWord_956471
  simp only [CollatzResearch.WordTrace]
  refine ⟨34885363317876394086773267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23256908878584262724515511 34885363317876394086773267)
  ·
    refine ⟨52328044976814591130159901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34885363317876394086773267 52328044976814591130159901)
    ·
      refine ⟨19623016866305471673809963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52328044976814591130159901 19623016866305471673809963)
      ·
        refine ⟨29434525299458207510714945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19623016866305471673809963 29434525299458207510714945)
        ·
          refine ⟨22075893974593655633036209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29434525299458207510714945 22075893974593655633036209)
          ·
            refine ⟨16556920480945241724777157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22075893974593655633036209 16556920480945241724777157)
            ·
              refine ⟨3104422590177232823395717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16556920480945241724777157 3104422590177232823395717)
              ·
                refine ⟨582079235658231154386697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3104422590177232823395717 582079235658231154386697)
                ·
                  refine ⟨436559426743673365790023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582079235658231154386697 436559426743673365790023)
                  ·
                    rfl

theorem cell20_956471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 2].length) (baseStart_956471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956471 prefixEnd_956471 := by exact prefixLift 956471
  have htrace : WordTrace (prefixWord ++ tailWord_956471) baseStart_956471 baseEnd_956471 := by
    simpa [prefixWord, tailWord_956471, baseEnd_956471] using wordTrace_append hprefix tailTrace_956471
  have hstable : (prefixWord ++ tailWord_956471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956471).length < 2 ^ (prefixWord ++ tailWord_956471).sum := by decide
  have hdescent : baseEnd_956471 < baseStart_956471 := by decide
  rcases family_descends (prefixWord ++ tailWord_956471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956475 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_956475 : Nat := 118140960795 + 956475 * 2 ^ 59
def prefixEnd_956475 : Nat := 4983230072969 + 3 ^ 40 * 956475 * 2
def baseEnd_956475 : Nat := 436561252452667129656673

theorem tailTrace_956475 : CollatzResearch.WordTrace tailWord_956475 prefixEnd_956475 436561252452667129656673 := by
  unfold tailWord_956475
  simp only [CollatzResearch.WordTrace]
  refine ⟨34885509209861902769918879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23257006139907935179945919 34885509209861902769918879)
  ·
    refine ⟨52328263814792854154878319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34885509209861902769918879 52328263814792854154878319)
    ·
      refine ⟨78492395722189281232317479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52328263814792854154878319 78492395722189281232317479)
      ·
        refine ⟨117738593583283921848476219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78492395722189281232317479 117738593583283921848476219)
        ·
          refine ⟨176607890374925882772714329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117738593583283921848476219 176607890374925882772714329)
          ·
            refine ⟨132455917781194412079535747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176607890374925882772714329 132455917781194412079535747)
            ·
              refine ⟨198683876671791618119303621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132455917781194412079535747 198683876671791618119303621)
              ·
                refine ⟨37253226875960928397369429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198683876671791618119303621 37253226875960928397369429)
                ·
                  refine ⟨436561252452667129656673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37253226875960928397369429 436561252452667129656673)
                  ·
                    rfl

theorem cell20_956475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_956475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956475 prefixEnd_956475 := by exact prefixLift 956475
  have htrace : WordTrace (prefixWord ++ tailWord_956475) baseStart_956475 baseEnd_956475 := by
    simpa [prefixWord, tailWord_956475, baseEnd_956475] using wordTrace_append hprefix tailTrace_956475
  have hstable : (prefixWord ++ tailWord_956475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956475).length < 2 ^ (prefixWord ++ tailWord_956475).sum := by decide
  have hdescent : baseEnd_956475 < baseStart_956475 := by decide
  rcases family_descends (prefixWord ++ tailWord_956475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956481 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 3]
def baseStart_956481 : Nat := 118140960795 + 956481 * 2 ^ 59
def prefixEnd_956481 : Nat := 4983230072969 + 3 ^ 40 * 956481 * 2
def baseEnd_956481 : Nat := 436563991016157775456649

theorem tailTrace_956481 : CollatzResearch.WordTrace tailWord_956481 prefixEnd_956481 436563991016157775456649 := by
  unfold tailWord_956481
  simp only [CollatzResearch.WordTrace]
  refine ⟨34885728047840165794637297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23257152031893443863091531 34885728047840165794637297)
  ·
    refine ⟨26164296035880124345977973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34885728047840165794637297 26164296035880124345977973)
    ·
      refine ⟨2452902753363761657435435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26164296035880124345977973 2452902753363761657435435)
      ·
        refine ⟨3679354130045642486153153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452902753363761657435435 3679354130045642486153153)
        ·
          refine ⟨2759515597534231864614865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3679354130045642486153153 2759515597534231864614865)
          ·
            refine ⟨2069636698150673898461149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2759515597534231864614865 2069636698150673898461149)
            ·
              refine ⟨776113761806502711922931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2069636698150673898461149 776113761806502711922931)
              ·
                refine ⟨1164170642709754067884397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776113761806502711922931 1164170642709754067884397)
                ·
                  refine ⟨436563991016157775456649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164170642709754067884397 436563991016157775456649)
                  ·
                    rfl

theorem cell20_956481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_956481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956481 prefixEnd_956481 := by exact prefixLift 956481
  have htrace : WordTrace (prefixWord ++ tailWord_956481) baseStart_956481 baseEnd_956481 := by
    simpa [prefixWord, tailWord_956481, baseEnd_956481] using wordTrace_append hprefix tailTrace_956481
  have hstable : (prefixWord ++ tailWord_956481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956481).length < 2 ^ (prefixWord ++ tailWord_956481).sum := by decide
  have hdescent : baseEnd_956481 < baseStart_956481 := by decide
  rcases family_descends (prefixWord ++ tailWord_956481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956492 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_956492 : Nat := 118140960795 + 956492 * 2 ^ 59
def prefixEnd_956492 : Nat := 4983230072969 + 3 ^ 40 * 956492 * 2
def baseEnd_956492 : Nat := 436569011715890626089937

theorem tailTrace_956492 : CollatzResearch.WordTrace tailWord_956492 prefixEnd_956492 436569011715890626089937 := by
  unfold tailWord_956492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17443064625400157336643865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23257419500533543115525153 17443064625400157336643865)
  ·
    refine ⟨13082298469050118002482899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17443064625400157336643865 13082298469050118002482899)
    ·
      refine ⟨19623447703575177003724349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13082298469050118002482899 19623447703575177003724349)
      ·
        refine ⟨7358792888840691376396631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19623447703575177003724349 7358792888840691376396631)
        ·
          refine ⟨11038189333261037064594947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358792888840691376396631 11038189333261037064594947)
          ·
            refine ⟨16557283999891555596892421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11038189333261037064594947 16557283999891555596892421)
            ·
              refine ⟨3104490749979666674417329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16557283999891555596892421 3104490749979666674417329)
              ·
                refine ⟨2328368062484750005812997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3104490749979666674417329 2328368062484750005812997)
                ·
                  refine ⟨436569011715890626089937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2328368062484750005812997 436569011715890626089937)
                  ·
                    rfl

theorem cell20_956492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_956492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956492 prefixEnd_956492 := by exact prefixLift 956492
  have htrace : WordTrace (prefixWord ++ tailWord_956492) baseStart_956492 baseEnd_956492 := by
    simpa [prefixWord, tailWord_956492, baseEnd_956492] using wordTrace_append hprefix tailTrace_956492
  have hstable : (prefixWord ++ tailWord_956492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956492).length < 2 ^ (prefixWord ++ tailWord_956492).sum := by decide
  have hdescent : baseEnd_956492 < baseStart_956492 := by decide
  rcases family_descends (prefixWord ++ tailWord_956492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956506 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_956506 : Nat := 118140960795 + 956506 * 2 ^ 59
def prefixEnd_956506 : Nat := 4983230072969 + 3 ^ 40 * 956506 * 2
def baseEnd_956506 : Nat := 436575401697368799623213

theorem tailTrace_956506 : CollatzResearch.WordTrace tailWord_956506 prefixEnd_956506 436575401697368799623213 := by
  unfold tailWord_956506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721659968187398766074343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23257759915166396709531581 8721659968187398766074343)
  ·
    refine ⟨13082489952281098149111515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8721659968187398766074343 13082489952281098149111515)
    ·
      refine ⟨19623734928421647223667273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13082489952281098149111515 19623734928421647223667273)
      ·
        refine ⟨14717801196316235417750455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19623734928421647223667273 14717801196316235417750455)
        ·
          refine ⟨22076701794474353126625683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14717801196316235417750455 22076701794474353126625683)
          ·
            refine ⟨33115052691711529689938525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22076701794474353126625683 33115052691711529689938525)
            ·
              refine ⟨12418144759391823633726947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33115052691711529689938525 12418144759391823633726947)
              ·
                refine ⟨18627217139087735450590421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12418144759391823633726947 18627217139087735450590421)
                ·
                  refine ⟨436575401697368799623213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18627217139087735450590421 436575401697368799623213)
                  ·
                    rfl

theorem cell20_956506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_956506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956506 prefixEnd_956506 := by exact prefixLift 956506
  have htrace : WordTrace (prefixWord ++ tailWord_956506) baseStart_956506 baseEnd_956506 := by
    simpa [prefixWord, tailWord_956506, baseEnd_956506] using wordTrace_append hprefix tailTrace_956506
  have hstable : (prefixWord ++ tailWord_956506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956506).length < 2 ^ (prefixWord ++ tailWord_956506).sum := by decide
  have hdescent : baseEnd_956506 < baseStart_956506 := by decide
  rcases family_descends (prefixWord ++ tailWord_956506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956537 : List Nat := [1, 2, 1, 3, 4, 1, 1, 7]
def baseStart_956537 : Nat := 118140960795 + 956537 * 2 ^ 59
def prefixEnd_956537 : Nat := 4983230072969 + 3 ^ 40 * 956537 * 2
def baseEnd_956537 : Nat := 145529850314023489863251

theorem tailTrace_956537 : CollatzResearch.WordTrace tailWord_956537 prefixEnd_956537 145529850314023489863251 := by
  unfold tailWord_956537
  simp only [CollatzResearch.WordTrace]
  refine ⟨34887770535637287358675865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23258513690424858239117243 34887770535637287358675865)
  ·
    refine ⟨26165827901727965519006899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34887770535637287358675865 26165827901727965519006899)
    ·
      refine ⟨39248741852591948278510349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26165827901727965519006899 39248741852591948278510349)
      ·
        refine ⟨14718278194721980604441381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39248741852591948278510349 14718278194721980604441381)
        ·
          refine ⟨2759677161510371363332759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14718278194721980604441381 2759677161510371363332759)
          ·
            refine ⟨4139515742265557044999139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759677161510371363332759 4139515742265557044999139)
            ·
              refine ⟨6209273613398335567498709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4139515742265557044999139 6209273613398335567498709)
              ·
                refine ⟨145529850314023489863251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6209273613398335567498709 145529850314023489863251)
                ·
                  rfl

theorem cell20_956537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_956537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956537 prefixEnd_956537 := by exact prefixLift 956537
  have htrace : WordTrace (prefixWord ++ tailWord_956537) baseStart_956537 baseEnd_956537 := by
    simpa [prefixWord, tailWord_956537, baseEnd_956537] using wordTrace_append hprefix tailTrace_956537
  have hstable : (prefixWord ++ tailWord_956537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956537).length < 2 ^ (prefixWord ++ tailWord_956537).sum := by decide
  have hdescent : baseEnd_956537 < baseStart_956537 := by decide
  rcases family_descends (prefixWord ++ tailWord_956537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956540 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 3]
def baseStart_956540 : Nat := 118140960795 + 956540 * 2 ^ 59
def prefixEnd_956540 : Nat := 4983230072969 + 3 ^ 40 * 956540 * 2
def baseEnd_956540 : Nat := 436590920223815792489741

theorem tailTrace_956540 : CollatzResearch.WordTrace tailWord_956540 prefixEnd_956540 436590920223815792489741 := by
  unfold tailWord_956540
  simp only [CollatzResearch.WordTrace]
  refine ⟨17443939977313209435517537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23258586636417612580690049 17443939977313209435517537)
  ·
    refine ⟨13082954982984907076638153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17443939977313209435517537 13082954982984907076638153)
    ·
      refine ⟨9812216237238680307478615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13082954982984907076638153 9812216237238680307478615)
      ·
        refine ⟨14718324355858020461217923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9812216237238680307478615 14718324355858020461217923)
        ·
          refine ⟨22077486533787030691826885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14718324355858020461217923 22077486533787030691826885)
          ·
            refine ⟨4139528725085068254717541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22077486533787030691826885 4139528725085068254717541)
            ·
              refine ⟨776161635953450297759539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4139528725085068254717541 776161635953450297759539)
              ·
                refine ⟨1164242453930175446639309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776161635953450297759539 1164242453930175446639309)
                ·
                  refine ⟨436590920223815792489741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164242453930175446639309 436590920223815792489741)
                  ·
                    rfl

theorem cell20_956540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_956540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956540 prefixEnd_956540 := by exact prefixLift 956540
  have htrace : WordTrace (prefixWord ++ tailWord_956540) baseStart_956540 baseEnd_956540 := by
    simpa [prefixWord, tailWord_956540, baseEnd_956540] using wordTrace_append hprefix tailTrace_956540
  have hstable : (prefixWord ++ tailWord_956540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956540).length < 2 ^ (prefixWord ++ tailWord_956540).sum := by decide
  have hdescent : baseEnd_956540 < baseStart_956540 := by decide
  rcases family_descends (prefixWord ++ tailWord_956540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956575 : List Nat := [1, 1, 2, 6, 1, 9]
def baseStart_956575 : Nat := 118140960795 + 956575 * 2 ^ 59
def prefixEnd_956575 : Nat := 4983230072969 + 3 ^ 40 * 956575 * 2
def baseEnd_956575 : Nat := 16170625747315230604553

theorem tailTrace_956575 : CollatzResearch.WordTrace tailWord_956575 prefixEnd_956575 16170625747315230604553 := by
  unfold tailWord_956575
  simp only [CollatzResearch.WordTrace]
  refine ⟨34889156509499619848559179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23259437672999746565706119 34889156509499619848559179)
  ·
    refine ⟨52333734764249429772838769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34889156509499619848559179 52333734764249429772838769)
    ·
      refine ⟨39250301073187072329629077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52333734764249429772838769 39250301073187072329629077)
      ·
        refine ⟨1839857862805644015451363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39250301073187072329629077 1839857862805644015451363)
        ·
          refine ⟨2759786794208466023177045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1839857862805644015451363 2759786794208466023177045)
          ·
            refine ⟨16170625747315230604553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2759786794208466023177045 16170625747315230604553)
            ·
              rfl

theorem cell20_956575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 9].length) (baseStart_956575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956575 prefixEnd_956575 := by exact prefixLift 956575
  have htrace : WordTrace (prefixWord ++ tailWord_956575) baseStart_956575 baseEnd_956575 := by
    simpa [prefixWord, tailWord_956575, baseEnd_956575] using wordTrace_append hprefix tailTrace_956575
  have hstable : (prefixWord ++ tailWord_956575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956575).length < 2 ^ (prefixWord ++ tailWord_956575).sum := by decide
  have hdescent : baseEnd_956575 < baseStart_956575 := by decide
  rcases family_descends (prefixWord ++ tailWord_956575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956578 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_956578 : Nat := 118140960795 + 956578 * 2 ^ 59
def prefixEnd_956578 : Nat := 4983230072969 + 3 ^ 40 * 956578 * 2
def baseEnd_956578 : Nat := 436608264459256549222919

theorem tailTrace_956578 : CollatzResearch.WordTrace tailWord_956578 prefixEnd_956578 436608264459256549222919 := by
  unfold tailWord_956578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8722316482122187840229597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23259510618992500907278925 8722316482122187840229597)
  ·
    refine ⟨3270868680795820440086099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8722316482122187840229597 3270868680795820440086099)
    ·
      refine ⟨4906303021193730660129149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3270868680795820440086099 4906303021193730660129149)
      ·
        refine ⟨1839863632947648997548431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4906303021193730660129149 1839863632947648997548431)
        ·
          refine ⟨2759795449421473496322647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1839863632947648997548431 2759795449421473496322647)
          ·
            refine ⟨4139693174132210244483971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759795449421473496322647 4139693174132210244483971)
            ·
              refine ⟨6209539761198315366725957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4139693174132210244483971 6209539761198315366725957)
              ·
                refine ⟨1164288705224684131261117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6209539761198315366725957 1164288705224684131261117)
                ·
                  refine ⟨436608264459256549222919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164288705224684131261117 436608264459256549222919)
                  ·
                    rfl

theorem cell20_956578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_956578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956578 prefixEnd_956578 := by exact prefixLift 956578
  have htrace : WordTrace (prefixWord ++ tailWord_956578) baseStart_956578 baseEnd_956578 := by
    simpa [prefixWord, tailWord_956578, baseEnd_956578] using wordTrace_append hprefix tailTrace_956578
  have hstable : (prefixWord ++ tailWord_956578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956578).length < 2 ^ (prefixWord ++ tailWord_956578).sum := by decide
  have hdescent : baseEnd_956578 < baseStart_956578 := by decide
  rcases family_descends (prefixWord ++ tailWord_956578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956599 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 3]
def baseStart_956599 : Nat := 118140960795 + 956599 * 2 ^ 59
def prefixEnd_956599 : Nat := 4983230072969 + 3 ^ 40 * 956599 * 2
def baseEnd_956599 : Nat := 436617849431473809522833

theorem tailTrace_956599 : CollatzResearch.WordTrace tailWord_956599 prefixEnd_956599 436617849431473809522833 := by
  unfold tailWord_956599
  simp only [CollatzResearch.WordTrace]
  refine ⟨34890031861412671947432851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23260021240941781298288567 34890031861412671947432851)
  ·
    refine ⟨52335047792119007921149277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34890031861412671947432851 52335047792119007921149277)
    ·
      refine ⟨19625642922044627970430979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52335047792119007921149277 19625642922044627970430979)
      ·
        refine ⟨29438464383066941955646469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19625642922044627970430979 29438464383066941955646469)
        ·
          refine ⟨5519712071825051616683713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29438464383066941955646469 5519712071825051616683713)
          ·
            refine ⟨4139784053868788712512785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5519712071825051616683713 4139784053868788712512785)
            ·
              refine ⟨3104838040401591534384589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4139784053868788712512785 3104838040401591534384589)
              ·
                refine ⟨1164314265150596825394221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3104838040401591534384589 1164314265150596825394221)
                ·
                  refine ⟨436617849431473809522833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164314265150596825394221 436617849431473809522833)
                  ·
                    rfl

theorem cell20_956599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 3].length) (baseStart_956599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956599 prefixEnd_956599 := by exact prefixLift 956599
  have htrace : WordTrace (prefixWord ++ tailWord_956599) baseStart_956599 baseEnd_956599 := by
    simpa [prefixWord, tailWord_956599, baseEnd_956599] using wordTrace_append hprefix tailTrace_956599
  have hstable : (prefixWord ++ tailWord_956599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956599).length < 2 ^ (prefixWord ++ tailWord_956599).sum := by decide
  have hdescent : baseEnd_956599 < baseStart_956599 := by decide
  rcases family_descends (prefixWord ++ tailWord_956599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956623 : List Nat := [1, 1, 2, 1, 1, 3, 6, 3, 2]
def baseStart_956623 : Nat := 118140960795 + 956623 * 2 ^ 59
def prefixEnd_956623 : Nat := 4983230072969 + 3 ^ 40 * 956623 * 2
def baseEnd_956623 : Nat := 436628803685436392722735

theorem tailTrace_956623 : CollatzResearch.WordTrace tailWord_956623 prefixEnd_956623 436628803685436392722735 := by
  unfold tailWord_956623
  simp only [CollatzResearch.WordTrace]
  refine ⟨34890907213325724046306523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23260604808883816030871015 34890907213325724046306523)
  ·
    refine ⟨52336360819988586069459785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34890907213325724046306523 52336360819988586069459785)
    ·
      refine ⟨39252270614991439552094839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52336360819988586069459785 39252270614991439552094839)
      ·
        refine ⟨58878405922487159328142259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39252270614991439552094839 58878405922487159328142259)
        ·
          refine ⟨88317608883730738992213389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58878405922487159328142259 88317608883730738992213389)
          ·
            refine ⟨33119103331399027122080021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88317608883730738992213389 33119103331399027122080021)
            ·
              refine ⟨1552457968659329396347501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33119103331399027122080021 1552457968659329396347501)
              ·
                refine ⟨582171738247248523630313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552457968659329396347501 582171738247248523630313)
                ·
                  refine ⟨436628803685436392722735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582171738247248523630313 436628803685436392722735)
                  ·
                    rfl

theorem cell20_956623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 2].length) (baseStart_956623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956623 prefixEnd_956623 := by exact prefixLift 956623
  have htrace : WordTrace (prefixWord ++ tailWord_956623) baseStart_956623 baseEnd_956623 := by
    simpa [prefixWord, tailWord_956623, baseEnd_956623] using wordTrace_append hprefix tailTrace_956623
  have hstable : (prefixWord ++ tailWord_956623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956623).length < 2 ^ (prefixWord ++ tailWord_956623).sum := by decide
  have hdescent : baseEnd_956623 < baseStart_956623 := by decide
  rcases family_descends (prefixWord ++ tailWord_956623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956665 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_956665 : Nat := 118140960795 + 956665 * 2 ^ 59
def prefixEnd_956665 : Nat := 4983230072969 + 3 ^ 40 * 956665 * 2
def baseEnd_956665 : Nat := 436647973629870913322563

theorem tailTrace_956665 : CollatzResearch.WordTrace tailWord_956665 prefixEnd_956665 436647973629870913322563 := by
  unfold tailWord_956665
  simp only [CollatzResearch.WordTrace]
  refine ⟨34892439079173565219335449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23261626052782376812890299 34892439079173565219335449)
  ·
    refine ⟨26169329309380173914501587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34892439079173565219335449 26169329309380173914501587)
    ·
      refine ⟨39253993964070260871752381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26169329309380173914501587 39253993964070260871752381)
      ·
        refine ⟨14720247736526347826907143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39253993964070260871752381 14720247736526347826907143)
        ·
          refine ⟨22080371604789521740360715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14720247736526347826907143 22080371604789521740360715)
          ·
            refine ⟨33120557407184282610541073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22080371604789521740360715 33120557407184282610541073)
            ·
              refine ⟨24840418055388211957905805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33120557407184282610541073 24840418055388211957905805)
              ·
                refine ⟨9315156770770579484214677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24840418055388211957905805 9315156770770579484214677)
                ·
                  refine ⟨436647973629870913322563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9315156770770579484214677 436647973629870913322563)
                  ·
                    rfl

theorem cell20_956665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_956665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956665 prefixEnd_956665 := by exact prefixLift 956665
  have htrace : WordTrace (prefixWord ++ tailWord_956665) baseStart_956665 baseEnd_956665 := by
    simpa [prefixWord, tailWord_956665, baseEnd_956665] using wordTrace_append hprefix tailTrace_956665
  have hstable : (prefixWord ++ tailWord_956665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956665).length < 2 ^ (prefixWord ++ tailWord_956665).sum := by decide
  have hdescent : baseEnd_956665 < baseStart_956665 := by decide
  rcases family_descends (prefixWord ++ tailWord_956665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956668 : List Nat := [2, 2, 2, 1, 4, 1, 4, 4]
def baseStart_956668 : Nat := 118140960795 + 956668 * 2 ^ 59
def prefixEnd_956668 : Nat := 4983230072969 + 3 ^ 40 * 956668 * 2
def baseEnd_956668 : Nat := 145549780970538745407517

theorem tailTrace_956668 : CollatzResearch.WordTrace tailWord_956668 prefixEnd_956668 145549780970538745407517 := by
  unfold tailWord_956668
  simp only [CollatzResearch.WordTrace]
  refine ⟨17446274249081348365847329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23261698998775131154463105 17446274249081348365847329)
  ·
    refine ⟨13084705686811011274385497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17446274249081348365847329 13084705686811011274385497)
    ·
      refine ⟨9813529265108258455789123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13084705686811011274385497 9813529265108258455789123)
      ·
        refine ⟨14720293897662387683683685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9813529265108258455789123 14720293897662387683683685)
        ·
          refine ⟨2760055105811697690690691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14720293897662387683683685 2760055105811697690690691)
          ·
            refine ⟨4140082658717546536036037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760055105811697690690691 4140082658717546536036037)
            ·
              refine ⟨776265498509539975506757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4140082658717546536036037 776265498509539975506757)
              ·
                refine ⟨145549780970538745407517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 776265498509539975506757 145549780970538745407517)
                ·
                  rfl

theorem cell20_956668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_956668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956668 prefixEnd_956668 := by exact prefixLift 956668
  have htrace : WordTrace (prefixWord ++ tailWord_956668) baseStart_956668 baseEnd_956668 := by
    simpa [prefixWord, tailWord_956668, baseEnd_956668] using wordTrace_append hprefix tailTrace_956668
  have hstable : (prefixWord ++ tailWord_956668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956668).length < 2 ^ (prefixWord ++ tailWord_956668).sum := by decide
  have hdescent : baseEnd_956668 < baseStart_956668 := by decide
  rcases family_descends (prefixWord ++ tailWord_956668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956689 : List Nat := [1, 2, 2, 1, 1, 7, 6]
def baseStart_956689 : Nat := 118140960795 + 956689 * 2 ^ 59
def prefixEnd_956689 : Nat := 4983230072969 + 3 ^ 40 * 956689 * 2
def baseEnd_956689 : Nat := 48517658653759277391385

theorem tailTrace_956689 : CollatzResearch.WordTrace tailWord_956689 prefixEnd_956689 48517658653759277391385 := by
  unfold tailWord_956689
  simp only [CollatzResearch.WordTrace]
  refine ⟨34893314431086617318209121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23262209620724411545472747 34893314431086617318209121)
  ·
    refine ⟨26169985823314962988656841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34893314431086617318209121 26169985823314962988656841)
    ·
      refine ⟨19627489367486222241492631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26169985823314962988656841 19627489367486222241492631)
      ·
        refine ⟨29441234051229333362238947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19627489367486222241492631 29441234051229333362238947)
        ·
          refine ⟨44161851076844000043358421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29441234051229333362238947 44161851076844000043358421)
          ·
            refine ⟨1035043384613531251016213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44161851076844000043358421 1035043384613531251016213)
            ·
              refine ⟨48517658653759277391385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1035043384613531251016213 48517658653759277391385)
              ·
                rfl

theorem cell20_956689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 6].length) (baseStart_956689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956689 prefixEnd_956689 := by exact prefixLift 956689
  have htrace : WordTrace (prefixWord ++ tailWord_956689) baseStart_956689 baseEnd_956689 := by
    simpa [prefixWord, tailWord_956689, baseEnd_956689] using wordTrace_append hprefix tailTrace_956689
  have hstable : (prefixWord ++ tailWord_956689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956689).length < 2 ^ (prefixWord ++ tailWord_956689).sum := by decide
  have hdescent : baseEnd_956689 < baseStart_956689 := by decide
  rcases family_descends (prefixWord ++ tailWord_956689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956696 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_956696 : Nat := 118140960795 + 956696 * 2 ^ 59
def prefixEnd_956696 : Nat := 4983230072969 + 3 ^ 40 * 956696 * 2
def baseEnd_956696 : Nat := 436662122874572583289103

theorem tailTrace_956696 : CollatzResearch.WordTrace tailWord_956696 prefixEnd_956696 436662122874572583289103 := by
  unfold tailWord_956696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17446784871030628756856971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23262379828040838342475961 17446784871030628756856971)
  ·
    refine ⟨26170177306545943135285457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17446784871030628756856971 26170177306545943135285457)
    ·
      refine ⟨19627632979909457351464093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26170177306545943135285457 19627632979909457351464093)
      ·
        refine ⟨7360362367466046506799035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19627632979909457351464093 7360362367466046506799035)
        ·
          refine ⟨11040543551199069760198553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360362367466046506799035 11040543551199069760198553)
          ·
            refine ⟨8280407663399302320148915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11040543551199069760198553 8280407663399302320148915)
            ·
              refine ⟨12420611495098953480223373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8280407663399302320148915 12420611495098953480223373)
              ·
                refine ⟨4657729310662107555083765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12420611495098953480223373 4657729310662107555083765)
                ·
                  refine ⟨436662122874572583289103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4657729310662107555083765 436662122874572583289103)
                  ·
                    rfl

theorem cell20_956696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_956696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956696 prefixEnd_956696 := by exact prefixLift 956696
  have htrace : WordTrace (prefixWord ++ tailWord_956696) baseStart_956696 baseEnd_956696 := by
    simpa [prefixWord, tailWord_956696, baseEnd_956696] using wordTrace_append hprefix tailTrace_956696
  have hstable : (prefixWord ++ tailWord_956696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956696).length < 2 ^ (prefixWord ++ tailWord_956696).sum := by decide
  have hdescent : baseEnd_956696 < baseStart_956696 := by decide
  rcases family_descends (prefixWord ++ tailWord_956696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956706 : List Nat := [3, 3, 1, 1, 3, 2, 2, 5]
def baseStart_956706 : Nat := 118140960795 + 956706 * 2 ^ 59
def prefixEnd_956706 : Nat := 4983230072969 + 3 ^ 40 * 956706 * 2
def baseEnd_956706 : Nat := 145555562382352330985243

theorem tailTrace_956706 : CollatzResearch.WordTrace tailWord_956706 prefixEnd_956706 145555562382352330985243 := by
  unfold tailWord_956706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8723483618006257305394493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23262622981350019481051981 8723483618006257305394493)
  ·
    refine ⟨3271306356752346489522935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8723483618006257305394493 3271306356752346489522935)
    ·
      refine ⟨4906959535128519734284403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3271306356752346489522935 4906959535128519734284403)
      ·
        refine ⟨7360439302692779601426605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4906959535128519734284403 7360439302692779601426605)
        ·
          refine ⟨2760164738509792350534977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7360439302692779601426605 2760164738509792350534977)
          ·
            refine ⟨2070123553882344262901233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2760164738509792350534977 2070123553882344262901233)
            ·
              refine ⟨1552592665411758197175925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2070123553882344262901233 1552592665411758197175925)
              ·
                refine ⟨145555562382352330985243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1552592665411758197175925 145555562382352330985243)
                ·
                  rfl

theorem cell20_956706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_956706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956706 prefixEnd_956706 := by exact prefixLift 956706
  have htrace : WordTrace (prefixWord ++ tailWord_956706) baseStart_956706 baseEnd_956706 := by
    simpa [prefixWord, tailWord_956706, baseEnd_956706] using wordTrace_append hprefix tailTrace_956706
  have hstable : (prefixWord ++ tailWord_956706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956706).length < 2 ^ (prefixWord ++ tailWord_956706).sum := by decide
  have hdescent : baseEnd_956706 < baseStart_956706 := by decide
  rcases family_descends (prefixWord ++ tailWord_956706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956709 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 3]
def baseStart_956709 : Nat := 118140960795 + 956709 * 2 ^ 59
def prefixEnd_956709 : Nat := 4983230072969 + 3 ^ 40 * 956709 * 2
def baseEnd_956709 : Nat := 436668056428802315855717

theorem tailTrace_956709 : CollatzResearch.WordTrace tailWord_956709 prefixEnd_956709 436668056428802315855717 := by
  unfold tailWord_956709
  simp only [CollatzResearch.WordTrace]
  refine ⟨34894043891014160733937181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23262695927342773822624787 34894043891014160733937181)
  ·
    refine ⟨13085266459130310275226443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34894043891014160733937181 13085266459130310275226443)
    ·
      refine ⟨19627899688695465412839665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13085266459130310275226443 19627899688695465412839665)
      ·
        refine ⟨14720924766521599059629749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19627899688695465412839665 14720924766521599059629749)
        ·
          refine ⟨1380086696861399911840289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14720924766521599059629749 1380086696861399911840289)
          ·
            refine ⟨1035065022646049933880217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380086696861399911840289 1035065022646049933880217)
            ·
              refine ⟨776298766984537450410163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1035065022646049933880217 776298766984537450410163)
              ·
                refine ⟨1164448150476806175615245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776298766984537450410163 1164448150476806175615245)
                ·
                  refine ⟨436668056428802315855717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164448150476806175615245 436668056428802315855717)
                  ·
                    rfl

theorem cell20_956709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_956709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956709 prefixEnd_956709 := by exact prefixLift 956709
  have htrace : WordTrace (prefixWord ++ tailWord_956709) baseStart_956709 baseEnd_956709 := by
    simpa [prefixWord, tailWord_956709, baseEnd_956709] using wordTrace_append hprefix tailTrace_956709
  have hstable : (prefixWord ++ tailWord_956709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956709).length < 2 ^ (prefixWord ++ tailWord_956709).sum := by decide
  have hdescent : baseEnd_956709 < baseStart_956709 := by decide
  rcases family_descends (prefixWord ++ tailWord_956709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956754 : List Nat := [3, 2, 2, 1, 1, 1, 6, 2, 2]
def baseStart_956754 : Nat := 118140960795 + 956754 * 2 ^ 59
def prefixEnd_956754 : Nat := 4983230072969 + 3 ^ 40 * 956754 * 2
def baseEnd_956754 : Nat := 436688595654982159355533

theorem tailTrace_956754 : CollatzResearch.WordTrace tailWord_956754 prefixEnd_956754 436688595654982159355533 := by
  unfold tailWord_956754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8723921293962783354831329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23263790117234088946216877 8723921293962783354831329)
  ·
    refine ⟨6542940970472087516123497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8723921293962783354831329 6542940970472087516123497)
    ·
      refine ⟨4907205727854065637092623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6542940970472087516123497 4907205727854065637092623)
      ·
        refine ⟨7360808591781098455638935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4907205727854065637092623 7360808591781098455638935)
        ·
          refine ⟨11041212887671647683458403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360808591781098455638935 11041212887671647683458403)
          ·
            refine ⟨16561819331507471525187605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11041212887671647683458403 16561819331507471525187605)
            ·
              refine ⟨776335281164412727743169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16561819331507471525187605 776335281164412727743169)
              ·
                refine ⟨582251460873309545807377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776335281164412727743169 582251460873309545807377)
                ·
                  refine ⟨436688595654982159355533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582251460873309545807377 436688595654982159355533)
                  ·
                    rfl

theorem cell20_956754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_956754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956754 prefixEnd_956754 := by exact prefixLift 956754
  have htrace : WordTrace (prefixWord ++ tailWord_956754) baseStart_956754 baseEnd_956754 := by
    simpa [prefixWord, tailWord_956754, baseEnd_956754] using wordTrace_append hprefix tailTrace_956754
  have hstable : (prefixWord ++ tailWord_956754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956754).length < 2 ^ (prefixWord ++ tailWord_956754).sum := by decide
  have hdescent : baseEnd_956754 < baseStart_956754 := by decide
  rcases family_descends (prefixWord ++ tailWord_956754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956779 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_956779 : Nat := 118140960795 + 956779 * 2 ^ 59
def prefixEnd_956779 : Nat := 4983230072969 + 3 ^ 40 * 956779 * 2
def baseEnd_956779 : Nat := 436700006336193183522097

theorem tailTrace_956779 : CollatzResearch.WordTrace tailWord_956779 prefixEnd_956779 436700006336193183522097 := by
  unfold tailWord_956779
  simp only [CollatzResearch.WordTrace]
  refine ⟨34896597000760562688985391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23264398000507041792656927 34896597000760562688985391)
  ·
    refine ⟨52344895501140844033478087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34896597000760562688985391 52344895501140844033478087)
    ·
      refine ⟨78517343251711266050217131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52344895501140844033478087 78517343251711266050217131)
      ·
        refine ⟨117776014877566899075325697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78517343251711266050217131 117776014877566899075325697)
        ·
          refine ⟨88332011158175174306494273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117776014877566899075325697 88332011158175174306494273)
          ·
            refine ⟨66249008368631380729870705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88332011158175174306494273 66249008368631380729870705)
            ·
              refine ⟨49686756276473535547403029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66249008368631380729870705 49686756276473535547403029)
              ·
                refine ⟨2329066700459696978784517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49686756276473535547403029 2329066700459696978784517)
                ·
                  refine ⟨436700006336193183522097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329066700459696978784517 436700006336193183522097)
                  ·
                    rfl

theorem cell20_956779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_956779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956779 prefixEnd_956779 := by exact prefixLift 956779
  have htrace : WordTrace (prefixWord ++ tailWord_956779) baseStart_956779 baseEnd_956779 := by
    simpa [prefixWord, tailWord_956779, baseEnd_956779] using wordTrace_append hprefix tailTrace_956779
  have hstable : (prefixWord ++ tailWord_956779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956779).length < 2 ^ (prefixWord ++ tailWord_956779).sum := by decide
  have hdescent : baseEnd_956779 < baseStart_956779 := by decide
  rcases family_descends (prefixWord ++ tailWord_956779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956802 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_956802 : Nat := 118140960795 + 956802 * 2 ^ 59
def prefixEnd_956802 : Nat := 4983230072969 + 3 ^ 40 * 956802 * 2
def baseEnd_956802 : Nat := 436710504162907325755337

theorem tailTrace_956802 : CollatzResearch.WordTrace tailWord_956802 prefixEnd_956802 436710504162907325755337 := by
  unfold tailWord_956802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8724358969919309404268165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23264957253118158411381773 8724358969919309404268165)
  ·
    refine ⟨1635817306859870513300281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8724358969919309404268165 1635817306859870513300281)
    ·
      refine ⟨1226862980144902884975211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1635817306859870513300281 1226862980144902884975211)
      ·
        refine ⟨1840294470217354327462817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226862980144902884975211 1840294470217354327462817)
        ·
          refine ⟨1380220852663015745597113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1840294470217354327462817 1380220852663015745597113)
          ·
            refine ⟨1035165639497261809197835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380220852663015745597113 1035165639497261809197835)
            ·
              refine ⟨1552748459245892713796753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035165639497261809197835 1552748459245892713796753)
              ·
                refine ⟨1164561344434419535347565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552748459245892713796753 1164561344434419535347565)
                ·
                  refine ⟨436710504162907325755337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164561344434419535347565 436710504162907325755337)
                  ·
                    rfl

theorem cell20_956802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_956802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956802 prefixEnd_956802 := by exact prefixLift 956802
  have htrace : WordTrace (prefixWord ++ tailWord_956802) baseStart_956802 baseEnd_956802 := by
    simpa [prefixWord, tailWord_956802, baseEnd_956802] using wordTrace_append hprefix tailTrace_956802
  have hstable : (prefixWord ++ tailWord_956802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956802).length < 2 ^ (prefixWord ++ tailWord_956802).sum := by decide
  have hdescent : baseEnd_956802 < baseStart_956802 := by decide
  rcases family_descends (prefixWord ++ tailWord_956802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956803 : List Nat := [1, 1, 1, 3, 6, 1, 7]
def baseStart_956803 : Nat := 118140960795 + 956803 * 2 ^ 59
def prefixEnd_956803 : Nat := 4983230072969 + 3 ^ 40 * 956803 * 2
def baseEnd_956803 : Nat := 48523440065572862969111

theorem tailTrace_956803 : CollatzResearch.WordTrace tailWord_956803 prefixEnd_956803 48523440065572862969111 := by
  unfold tailWord_956803
  simp only [CollatzResearch.WordTrace]
  refine ⟨34897472352673614787859063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23264981568449076525239375 34897472352673614787859063)
  ·
    refine ⟨52346208529010422181788595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34897472352673614787859063 52346208529010422181788595)
    ·
      refine ⟨78519312793515633272682893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52346208529010422181788595 78519312793515633272682893)
      ·
        refine ⟨29444742297568362477256085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78519312793515633272682893 29444742297568362477256085)
        ·
          refine ⟨1380222295198516991121379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29444742297568362477256085 1380222295198516991121379)
          ·
            refine ⟨2070333442797775486682069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380222295198516991121379 2070333442797775486682069)
            ·
              refine ⟨48523440065572862969111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2070333442797775486682069 48523440065572862969111)
              ·
                rfl

theorem cell20_956803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 7].length) (baseStart_956803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956803 prefixEnd_956803 := by exact prefixLift 956803
  have htrace : WordTrace (prefixWord ++ tailWord_956803) baseStart_956803 baseEnd_956803 := by
    simpa [prefixWord, tailWord_956803, baseEnd_956803] using wordTrace_append hprefix tailTrace_956803
  have hstable : (prefixWord ++ tailWord_956803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956803).length < 2 ^ (prefixWord ++ tailWord_956803).sum := by decide
  have hdescent : baseEnd_956803 < baseStart_956803 := by decide
  rcases family_descends (prefixWord ++ tailWord_956803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956834 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_956834 : Nat := 118140960795 + 956834 * 2 ^ 59
def prefixEnd_956834 : Nat := 4983230072969 + 3 ^ 40 * 956834 * 2
def baseEnd_956834 : Nat := 436725109834857436688539

theorem tailTrace_956834 : CollatzResearch.WordTrace tailWord_956834 prefixEnd_956834 436725109834857436688539 := by
  unfold tailWord_956834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8724650753890326770559389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23265735343707538054825037 8724650753890326770559389)
  ·
    refine ⟨3271744032708872538959771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8724650753890326770559389 3271744032708872538959771)
    ·
      refine ⟨4907616049063308808439657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3271744032708872538959771 4907616049063308808439657)
      ·
        refine ⟨3680712036797481606329743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4907616049063308808439657 3680712036797481606329743)
        ·
          refine ⟨5521068055196222409494615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680712036797481606329743 5521068055196222409494615)
          ·
            refine ⟨8281602082794333614241923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5521068055196222409494615 8281602082794333614241923)
            ·
              refine ⟨12422403124191500421362885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281602082794333614241923 12422403124191500421362885)
              ·
                refine ⟨2329200585785906329005541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12422403124191500421362885 2329200585785906329005541)
                ·
                  refine ⟨436725109834857436688539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329200585785906329005541 436725109834857436688539)
                  ·
                    rfl

theorem cell20_956834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_956834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956834 prefixEnd_956834 := by exact prefixLift 956834
  have htrace : WordTrace (prefixWord ++ tailWord_956834) baseStart_956834 baseEnd_956834 := by
    simpa [prefixWord, tailWord_956834, baseEnd_956834] using wordTrace_append hprefix tailTrace_956834
  have hstable : (prefixWord ++ tailWord_956834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956834).length < 2 ^ (prefixWord ++ tailWord_956834).sum := by decide
  have hdescent : baseEnd_956834 < baseStart_956834 := by decide
  rcases family_descends (prefixWord ++ tailWord_956834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956868 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 4]
def baseStart_956868 : Nat := 118140960795 + 956868 * 2 ^ 59
def prefixEnd_956868 : Nat := 4983230072969 + 3 ^ 40 * 956868 * 2
def baseEnd_956868 : Nat := 436740628361304429555067

theorem tailTrace_956868 : CollatzResearch.WordTrace tailWord_956868 prefixEnd_956868 436740628361304429555067 := by
  unfold tailWord_956868
  simp only [CollatzResearch.WordTrace]
  refine ⟨17449921548719065444487629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23266562064958753925983505 17449921548719065444487629)
  ·
    refine ⟨6543720580769649541682861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17449921548719065444487629 6543720580769649541682861)
    ·
      refine ⟨2453895217788618578131073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6543720580769649541682861 2453895217788618578131073)
      ·
        refine ⟨1840421413341463933598305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2453895217788618578131073 1840421413341463933598305)
        ·
          refine ⟨1380316060006097950198729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1840421413341463933598305 1380316060006097950198729)
          ·
            refine ⟨1035237045004573462649047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380316060006097950198729 1035237045004573462649047)
            ·
              refine ⟨1552855567506860193973571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035237045004573462649047 1552855567506860193973571)
              ·
                refine ⟨2329283351260290290960357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552855567506860193973571 2329283351260290290960357)
                ·
                  refine ⟨436740628361304429555067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329283351260290290960357 436740628361304429555067)
                  ·
                    rfl

theorem cell20_956868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_956868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956868 prefixEnd_956868 := by exact prefixLift 956868
  have htrace : WordTrace (prefixWord ++ tailWord_956868) baseStart_956868 baseEnd_956868 := by
    simpa [prefixWord, tailWord_956868, baseEnd_956868] using wordTrace_append hprefix tailTrace_956868
  have hstable : (prefixWord ++ tailWord_956868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956868).length < 2 ^ (prefixWord ++ tailWord_956868).sum := by decide
  have hdescent : baseEnd_956868 < baseStart_956868 := by decide
  rcases family_descends (prefixWord ++ tailWord_956868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956872 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_956872 : Nat := 118140960795 + 956872 * 2 ^ 59
def prefixEnd_956872 : Nat := 4983230072969 + 3 ^ 40 * 956872 * 2
def baseEnd_956872 : Nat := 436742454070298193421717

theorem tailTrace_956872 : CollatzResearch.WordTrace tailWord_956872 prefixEnd_956872 436742454070298193421717 := by
  unfold tailWord_956872
  simp only [CollatzResearch.WordTrace]
  refine ⟨17449994494711819786060435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23266659326282426381413913 17449994494711819786060435)
  ·
    refine ⟨26174991742067729679090653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17449994494711819786060435 26174991742067729679090653)
    ·
      refine ⟨9815621903275398629658995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26174991742067729679090653 9815621903275398629658995)
      ·
        refine ⟨14723432854913097944488493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9815621903275398629658995 14723432854913097944488493)
        ·
          refine ⟨5521287320592411729183185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14723432854913097944488493 5521287320592411729183185)
          ·
            refine ⟨4140965490444308796887389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5521287320592411729183185 4140965490444308796887389)
            ·
              refine ⟨1552862058916615798832771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4140965490444308796887389 1552862058916615798832771)
              ·
                refine ⟨2329293088374923698249157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552862058916615798832771 2329293088374923698249157)
                ·
                  refine ⟨436742454070298193421717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329293088374923698249157 436742454070298193421717)
                  ·
                    rfl

theorem cell20_956872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_956872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956872 prefixEnd_956872 := by exact prefixLift 956872
  have htrace : WordTrace (prefixWord ++ tailWord_956872) baseStart_956872 baseEnd_956872 := by
    simpa [prefixWord, tailWord_956872, baseEnd_956872] using wordTrace_append hprefix tailTrace_956872
  have hstable : (prefixWord ++ tailWord_956872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956872).length < 2 ^ (prefixWord ++ tailWord_956872).sum := by decide
  have hdescent : baseEnd_956872 < baseStart_956872 := by decide
  rcases family_descends (prefixWord ++ tailWord_956872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956917 : List Nat := [1, 3, 5, 1, 10]
def baseStart_956917 : Nat := 118140960795 + 956917 * 2 ^ 59
def prefixEnd_956917 : Nat := 4983230072969 + 3 ^ 40 * 956917 * 2
def baseEnd_956917 : Nat := 5392135719709605394093

theorem tailTrace_956917 : CollatzResearch.WordTrace tailWord_956917 prefixEnd_956917 5392135719709605394093 := by
  unfold tailWord_956917
  simp only [CollatzResearch.WordTrace]
  refine ⟨34901630274260612257509005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23267753516173741505006003 34901630274260612257509005)
  ·
    refine ⟨13088111352847729596565877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34901630274260612257509005 13088111352847729596565877)
    ·
      refine ⟨1227010439329474649678051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13088111352847729596565877 1227010439329474649678051)
      ·
        refine ⟨1840515658994211974517077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227010439329474649678051 1840515658994211974517077)
        ·
          refine ⟨5392135719709605394093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1840515658994211974517077 5392135719709605394093)
          ·
            rfl

theorem cell20_956917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 10].length) (baseStart_956917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956917 prefixEnd_956917 := by exact prefixLift 956917
  have htrace : WordTrace (prefixWord ++ tailWord_956917) baseStart_956917 baseEnd_956917 := by
    simpa [prefixWord, tailWord_956917, baseEnd_956917] using wordTrace_append hprefix tailTrace_956917
  have hstable : (prefixWord ++ tailWord_956917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956917).length < 2 ^ (prefixWord ++ tailWord_956917).sum := by decide
  have hdescent : baseEnd_956917 < baseStart_956917 := by decide
  rcases family_descends (prefixWord ++ tailWord_956917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956930 : List Nat := [3, 4, 1, 2, 3, 1, 1, 5]
def baseStart_956930 : Nat := 118140960795 + 956930 * 2 ^ 59
def prefixEnd_956930 : Nat := 4983230072969 + 3 ^ 40 * 956930 * 2
def baseEnd_956930 : Nat := 145589642283569256496049

theorem tailTrace_956930 : CollatzResearch.WordTrace tailWord_956930 prefixEnd_956930 145589642283569256496049 := by
  unfold tailWord_956930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8725526105803378869433061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23268069615475676985154829 8725526105803378869433061)
  ·
    refine ⟨1636036144838133538018699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8725526105803378869433061 1636036144838133538018699)
    ·
      refine ⟨2454054217257200307028049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636036144838133538018699 2454054217257200307028049)
      ·
        refine ⟨1840540662942900230271037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2454054217257200307028049 1840540662942900230271037)
        ·
          refine ⟨690202748603587586351639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1840540662942900230271037 690202748603587586351639)
          ·
            refine ⟨1035304122905381379527459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690202748603587586351639 1035304122905381379527459)
            ·
              refine ⟨1552956184358072069291189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035304122905381379527459 1552956184358072069291189)
              ·
                refine ⟨145589642283569256496049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1552956184358072069291189 145589642283569256496049)
                ·
                  rfl

theorem cell20_956930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_956930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956930 prefixEnd_956930 := by exact prefixLift 956930
  have htrace : WordTrace (prefixWord ++ tailWord_956930) baseStart_956930 baseEnd_956930 := by
    simpa [prefixWord, tailWord_956930, baseEnd_956930] using wordTrace_append hprefix tailTrace_956930
  have hstable : (prefixWord ++ tailWord_956930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956930).length < 2 ^ (prefixWord ++ tailWord_956930).sum := by decide
  have hdescent : baseEnd_956930 < baseStart_956930 := by decide
  rcases family_descends (prefixWord ++ tailWord_956930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956931 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_956931 : Nat := 118140960795 + 956931 * 2 ^ 59
def prefixEnd_956931 : Nat := 4983230072969 + 3 ^ 40 * 956931 * 2
def baseEnd_956931 : Nat := 436769383277956210454809

theorem tailTrace_956931 : CollatzResearch.WordTrace tailWord_956931 prefixEnd_956931 436769383277956210454809 := by
  unfold tailWord_956931
  simp only [CollatzResearch.WordTrace]
  refine ⟨34902140896209892648518647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23268093930806595099012431 34902140896209892648518647)
  ·
    refine ⟨52353211344314838972777971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34902140896209892648518647 52353211344314838972777971)
    ·
      refine ⟨78529817016472258459166957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52353211344314838972777971 78529817016472258459166957)
      ·
        refine ⟨29448681381177096922187609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78529817016472258459166957 29448681381177096922187609)
        ·
          refine ⟨22086511035882822691640707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29448681381177096922187609 22086511035882822691640707)
          ·
            refine ⟨33129766553824234037461061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22086511035882822691640707 33129766553824234037461061)
            ·
              refine ⟨6211831228842043882023949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33129766553824234037461061 6211831228842043882023949)
              ·
                refine ⟨2329436710815766455758981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6211831228842043882023949 2329436710815766455758981)
                ·
                  refine ⟨436769383277956210454809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329436710815766455758981 436769383277956210454809)
                  ·
                    rfl

theorem cell20_956931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_956931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956931 prefixEnd_956931 := by exact prefixLift 956931
  have htrace : WordTrace (prefixWord ++ tailWord_956931) baseStart_956931 baseEnd_956931 := by
    simpa [prefixWord, tailWord_956931, baseEnd_956931] using wordTrace_append hprefix tailTrace_956931
  have hstable : (prefixWord ++ tailWord_956931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956931).length < 2 ^ (prefixWord ++ tailWord_956931).sum := by decide
  have hdescent : baseEnd_956931 < baseStart_956931 := by decide
  rcases family_descends (prefixWord ++ tailWord_956931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956951 : List Nat := [1, 1, 3, 6, 1, 1, 3, 4]
def baseStart_956951 : Nat := 118140960795 + 956951 * 2 ^ 59
def prefixEnd_956951 : Nat := 4983230072969 + 3 ^ 40 * 956951 * 2
def baseEnd_956951 : Nat := 145592837274308343262687

theorem tailTrace_956951 : CollatzResearch.WordTrace tailWord_956951 prefixEnd_956951 145592837274308343262687 := by
  unfold tailWord_956951
  simp only [CollatzResearch.WordTrace]
  refine ⟨34902870356137436064246707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23268580237424957376164471 34902870356137436064246707)
  ·
    refine ⟨52354305534206154096370061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34902870356137436064246707 52354305534206154096370061)
    ·
      refine ⟨19632864575327307786138773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52354305534206154096370061 19632864575327307786138773)
      ·
        refine ⟨920290526968467552475255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19632864575327307786138773 920290526968467552475255)
        ·
          refine ⟨1380435790452701328712883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920290526968467552475255 1380435790452701328712883)
          ·
            refine ⟨2070653685679051993069325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380435790452701328712883 2070653685679051993069325)
            ·
              refine ⟨776495132129644497400997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2070653685679051993069325 776495132129644497400997)
              ·
                refine ⟨145592837274308343262687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 776495132129644497400997 145592837274308343262687)
                ·
                  rfl

theorem cell20_956951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 4].length) (baseStart_956951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956951 prefixEnd_956951 := by exact prefixLift 956951
  have htrace : WordTrace (prefixWord ++ tailWord_956951) baseStart_956951 baseEnd_956951 := by
    simpa [prefixWord, tailWord_956951, baseEnd_956951] using wordTrace_append hprefix tailTrace_956951
  have hstable : (prefixWord ++ tailWord_956951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956951).length < 2 ^ (prefixWord ++ tailWord_956951).sum := by decide
  have hdescent : baseEnd_956951 < baseStart_956951 := by decide
  rcases family_descends (prefixWord ++ tailWord_956951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956962 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_956962 : Nat := 118140960795 + 956962 * 2 ^ 59
def prefixEnd_956962 : Nat := 4983230072969 + 3 ^ 40 * 956962 * 2
def baseEnd_956962 : Nat := 436783532522657880421349

theorem tailTrace_956962 : CollatzResearch.WordTrace tailWord_956962 prefixEnd_956962 436783532522657880421349 := by
  unfold tailWord_956962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8725817889774396235724285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23268847706065056628598093 8725817889774396235724285)
  ·
    refine ⟨3272181708665398588396607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8725817889774396235724285 3272181708665398588396607)
    ·
      refine ⟨4908272562998097882594911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3272181708665398588396607 4908272562998097882594911)
      ·
        refine ⟨7362408844497146823892367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4908272562998097882594911 7362408844497146823892367)
        ·
          refine ⟨11043613266745720235838551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362408844497146823892367 11043613266745720235838551)
          ·
            refine ⟨16565419900118580353757827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11043613266745720235838551 16565419900118580353757827)
            ·
              refine ⟨24848129850177870530636741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16565419900118580353757827 24848129850177870530636741)
              ·
                refine ⟨4659024346908350724494389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24848129850177870530636741 4659024346908350724494389)
                ·
                  refine ⟨436783532522657880421349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4659024346908350724494389 436783532522657880421349)
                  ·
                    rfl

theorem cell20_956962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_956962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956962 prefixEnd_956962 := by exact prefixLift 956962
  have htrace : WordTrace (prefixWord ++ tailWord_956962) baseStart_956962 baseEnd_956962 := by
    simpa [prefixWord, tailWord_956962, baseEnd_956962] using wordTrace_append hprefix tailTrace_956962
  have hstable : (prefixWord ++ tailWord_956962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956962).length < 2 ^ (prefixWord ++ tailWord_956962).sum := by decide
  have hdescent : baseEnd_956962 < baseStart_956962 := by decide
  rcases family_descends (prefixWord ++ tailWord_956962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956982 : List Nat := [5, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_956982 : Nat := 118140960795 + 956982 * 2 ^ 59
def prefixEnd_956982 : Nat := 4983230072969 + 3 ^ 40 * 956982 * 2
def baseEnd_956982 : Nat := 436792661067626699754601

theorem tailTrace_956982 : CollatzResearch.WordTrace tailWord_956982 prefixEnd_956982 436792661067626699754601 := by
  unfold tailWord_956982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181500063689070522414075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23269334012683418905750133 2181500063689070522414075)
  ·
    refine ⟨3272250095533605783621113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2181500063689070522414075 3272250095533605783621113)
    ·
      refine ⟨2454187571650204337715835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3272250095533605783621113 2454187571650204337715835)
      ·
        refine ⟨3681281357475306506573753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454187571650204337715835 3681281357475306506573753)
        ·
          refine ⟨2760961018106479879930315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3681281357475306506573753 2760961018106479879930315)
          ·
            refine ⟨4141441527159719819895473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760961018106479879930315 4141441527159719819895473)
            ·
              refine ⟨3106081145369789864921605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4141441527159719819895473 3106081145369789864921605)
              ·
                refine ⟨582390214756835599672801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3106081145369789864921605 582390214756835599672801)
                ·
                  refine ⟨436792661067626699754601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582390214756835599672801 436792661067626699754601)
                  ·
                    rfl

theorem cell20_956982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_956982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956982 prefixEnd_956982 := by exact prefixLift 956982
  have htrace : WordTrace (prefixWord ++ tailWord_956982) baseStart_956982 baseEnd_956982 := by
    simpa [prefixWord, tailWord_956982, baseEnd_956982] using wordTrace_append hprefix tailTrace_956982
  have hstable : (prefixWord ++ tailWord_956982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956982).length < 2 ^ (prefixWord ++ tailWord_956982).sum := by decide
  have hdescent : baseEnd_956982 < baseStart_956982 := by decide
  rcases family_descends (prefixWord ++ tailWord_956982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956986 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_956986 : Nat := 118140960795 + 956986 * 2 ^ 59
def prefixEnd_956986 : Nat := 4983230072969 + 3 ^ 40 * 956986 * 2
def baseEnd_956986 : Nat := 436794486776620463621251

theorem tailTrace_956986 : CollatzResearch.WordTrace tailWord_956986 prefixEnd_956986 436794486776620463621251 := by
  unfold tailWord_956986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8726036727752659260442703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23269431274007091361180541 8726036727752659260442703)
  ·
    refine ⟨13089055091628988890664055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8726036727752659260442703 13089055091628988890664055)
    ·
      refine ⟨19633582637443483335996083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13089055091628988890664055 19633582637443483335996083)
      ·
        refine ⟨29450373956165225003994125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19633582637443483335996083 29450373956165225003994125)
        ·
          refine ⟨11043890233561959376497797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29450373956165225003994125 11043890233561959376497797)
          ·
            refine ⟨2070729418792867383093337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11043890233561959376497797 2070729418792867383093337)
            ·
              refine ⟨1553047064094650537320003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2070729418792867383093337 1553047064094650537320003)
              ·
                refine ⟨2329570596141975805980005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553047064094650537320003 2329570596141975805980005)
                ·
                  refine ⟨436794486776620463621251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329570596141975805980005 436794486776620463621251)
                  ·
                    rfl

theorem cell20_956986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_956986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956986 prefixEnd_956986 := by exact prefixLift 956986
  have htrace : WordTrace (prefixWord ++ tailWord_956986) baseStart_956986 baseEnd_956986 := by
    simpa [prefixWord, tailWord_956986, baseEnd_956986] using wordTrace_append hprefix tailTrace_956986
  have hstable : (prefixWord ++ tailWord_956986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956986).length < 2 ^ (prefixWord ++ tailWord_956986).sum := by decide
  have hdescent : baseEnd_956986 < baseStart_956986 := by decide
  rcases family_descends (prefixWord ++ tailWord_956986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957000 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 3]
def baseStart_957000 : Nat := 118140960795 + 957000 * 2 ^ 59
def prefixEnd_957000 : Nat := 4983230072969 + 3 ^ 40 * 957000 * 2
def baseEnd_957000 : Nat := 436800876758098637154527

theorem tailTrace_957000 : CollatzResearch.WordTrace tailWord_957000 prefixEnd_957000 436800876758098637154527 := by
  unfold tailWord_957000
  simp only [CollatzResearch.WordTrace]
  refine ⟨17452328766479958716390227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23269771688639944955186969 17452328766479958716390227)
  ·
    refine ⟨26178493149719938074585341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17452328766479958716390227 26178493149719938074585341)
    ·
      refine ⟨9816934931144976777969503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26178493149719938074585341 9816934931144976777969503)
      ·
        refine ⟨14725402396717465166954255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9816934931144976777969503 14725402396717465166954255)
        ·
          refine ⟨22088103595076197750431383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14725402396717465166954255 22088103595076197750431383)
          ·
            refine ⟨33132155392614296625647075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22088103595076197750431383 33132155392614296625647075)
            ·
              refine ⟨49698233088921444938470613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33132155392614296625647075 49698233088921444938470613)
              ·
                refine ⟨1164802338021596365745405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49698233088921444938470613 1164802338021596365745405)
                ·
                  refine ⟨436800876758098637154527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164802338021596365745405 436800876758098637154527)
                  ·
                    rfl

theorem cell20_957000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_957000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957000 prefixEnd_957000 := by exact prefixLift 957000
  have htrace : WordTrace (prefixWord ++ tailWord_957000) baseStart_957000 baseEnd_957000 := by
    simpa [prefixWord, tailWord_957000, baseEnd_957000] using wordTrace_append hprefix tailTrace_957000
  have hstable : (prefixWord ++ tailWord_957000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957000).length < 2 ^ (prefixWord ++ tailWord_957000).sum := by decide
  have hdescent : baseEnd_957000 < baseStart_957000 := by decide
  rcases family_descends (prefixWord ++ tailWord_957000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957007 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_957007 : Nat := 118140960795 + 957007 * 2 ^ 59
def prefixEnd_957007 : Nat := 4983230072969 + 3 ^ 40 * 957007 * 2
def baseEnd_957007 : Nat := 436804071748837723921165

theorem tailTrace_957007 : CollatzResearch.WordTrace tailWord_957007 prefixEnd_957007 436804071748837723921165 := by
  unfold tailWord_957007
  simp only [CollatzResearch.WordTrace]
  refine ⟨34904912843934557628285275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23269941895956371752190183 34904912843934557628285275)
  ·
    refine ⟨52357369265901836442427913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34904912843934557628285275 52357369265901836442427913)
    ·
      refine ⟨39268026949426377331820935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52357369265901836442427913 39268026949426377331820935)
      ·
        refine ⟨58902040424139565997731403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39268026949426377331820935 58902040424139565997731403)
        ·
          refine ⟨88353060636209348996597105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58902040424139565997731403 88353060636209348996597105)
          ·
            refine ⟨66264795477157011747447829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88353060636209348996597105 66264795477157011747447829)
            ·
              refine ⟨3106162287991734925661617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66264795477157011747447829 3106162287991734925661617)
              ·
                refine ⟨2329621715993801194246213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106162287991734925661617 2329621715993801194246213)
                ·
                  refine ⟨436804071748837723921165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329621715993801194246213 436804071748837723921165)
                  ·
                    rfl

theorem cell20_957007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_957007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957007 prefixEnd_957007 := by exact prefixLift 957007
  have htrace : WordTrace (prefixWord ++ tailWord_957007) baseStart_957007 baseEnd_957007 := by
    simpa [prefixWord, tailWord_957007, baseEnd_957007] using wordTrace_append hprefix tailTrace_957007
  have hstable : (prefixWord ++ tailWord_957007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957007).length < 2 ^ (prefixWord ++ tailWord_957007).sum := by decide
  have hdescent : baseEnd_957007 < baseStart_957007 := by decide
  rcases family_descends (prefixWord ++ tailWord_957007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957052 : List Nat := [2, 2, 2, 1, 1, 2, 3, 7]
def baseStart_957052 : Nat := 118140960795 + 957052 * 2 ^ 59
def prefixEnd_957052 : Nat := 4983230072969 + 3 ^ 40 * 957052 * 2
def baseEnd_957052 : Nat := 145608203658339189140327

theorem tailTrace_957052 : CollatzResearch.WordTrace tailWord_957052 prefixEnd_957052 145608203658339189140327 := by
  unfold tailWord_957052
  simp only [CollatzResearch.WordTrace]
  refine ⟨17453277064385765156836705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23271036085847686875782273 17453277064385765156836705)
  ·
    refine ⟨13089957798289323867627529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17453277064385765156836705 13089957798289323867627529)
    ·
      refine ⟨9817468348716992900720647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13089957798289323867627529 9817468348716992900720647)
      ·
        refine ⟨14726202523075489351080971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9817468348716992900720647 14726202523075489351080971)
        ·
          refine ⟨22089303784613234026621457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14726202523075489351080971 22089303784613234026621457)
          ·
            refine ⟨16566977838459925519966093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22089303784613234026621457 16566977838459925519966093)
            ·
              refine ⟨6212616689422472069987285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16566977838459925519966093 6212616689422472069987285)
              ·
                refine ⟨145608203658339189140327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6212616689422472069987285 145608203658339189140327)
                ·
                  rfl

theorem cell20_957052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_957052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957052 prefixEnd_957052 := by exact prefixLift 957052
  have htrace : WordTrace (prefixWord ++ tailWord_957052) baseStart_957052 baseEnd_957052 := by
    simpa [prefixWord, tailWord_957052, baseEnd_957052] using wordTrace_append hprefix tailTrace_957052
  have hstable : (prefixWord ++ tailWord_957052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957052).length < 2 ^ (prefixWord ++ tailWord_957052).sum := by decide
  have hdescent : baseEnd_957052 < baseStart_957052 := by decide
  rcases family_descends (prefixWord ++ tailWord_957052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957090 : List Nat := [3, 3, 1, 13]
def baseStart_957090 : Nat := 118140960795 + 957090 * 2 ^ 59
def prefixEnd_957090 : Nat := 4983230072969 + 3 ^ 40 * 957090 * 2
def baseEnd_957090 : Nat := 1797703519384602157013

theorem tailTrace_957090 : CollatzResearch.WordTrace tailWord_957090 prefixEnd_957090 1797703519384602157013 := by
  unfold tailWord_957090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8726985025658465700889181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23271960068422575202371149 8726985025658465700889181)
  ·
    refine ⟨3272619384621924637833443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8726985025658465700889181 3272619384621924637833443)
    ·
      refine ⟨4908929076932886956750165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3272619384621924637833443 4908929076932886956750165)
      ·
        refine ⟨1797703519384602157013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4908929076932886956750165 1797703519384602157013)
        ·
          rfl

theorem cell20_957090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 13].length) (baseStart_957090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957090 prefixEnd_957090 := by exact prefixLift 957090
  have htrace : WordTrace (prefixWord ++ tailWord_957090) baseStart_957090 baseEnd_957090 := by
    simpa [prefixWord, tailWord_957090, baseEnd_957090] using wordTrace_append hprefix tailTrace_957090
  have hstable : (prefixWord ++ tailWord_957090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957090).length < 2 ^ (prefixWord ++ tailWord_957090).sum := by decide
  have hdescent : baseEnd_957090 < baseStart_957090 := by decide
  rcases family_descends (prefixWord ++ tailWord_957090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957107 : List Nat := [1, 1, 1, 2, 3, 6, 1, 5]
def baseStart_957107 : Nat := 118140960795 + 957107 * 2 ^ 59
def prefixEnd_957107 : Nat := 4983230072969 + 3 ^ 40 * 957107 * 2
def baseEnd_957107 : Nat := 145616571491227273529141

theorem tailTrace_957107 : CollatzResearch.WordTrace tailWord_957107 prefixEnd_957107 145616571491227273529141 := by
  unfold tailWord_957107
  simp only [CollatzResearch.WordTrace]
  refine ⟨34908560143572274706925575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23272373429048183137950383 34908560143572274706925575)
  ·
    refine ⟨52362840215358412060388363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34908560143572274706925575 52362840215358412060388363)
    ·
      refine ⟨78544260323037618090582545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52362840215358412060388363 78544260323037618090582545)
      ·
        refine ⟨58908195242278213567936909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78544260323037618090582545 58908195242278213567936909)
        ·
          refine ⟨22090573215854330087976341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58908195242278213567936909 22090573215854330087976341)
          ·
            refine ⟨1035495619493171722873891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22090573215854330087976341 1035495619493171722873891)
            ·
              refine ⟨1553243429239757584310837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035495619493171722873891 1553243429239757584310837)
              ·
                refine ⟨145616571491227273529141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1553243429239757584310837 145616571491227273529141)
                ·
                  rfl

theorem cell20_957107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 5].length) (baseStart_957107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957107 prefixEnd_957107 := by exact prefixLift 957107
  have htrace : WordTrace (prefixWord ++ tailWord_957107) baseStart_957107 baseEnd_957107 := by
    simpa [prefixWord, tailWord_957107, baseEnd_957107] using wordTrace_append hprefix tailTrace_957107
  have hstable : (prefixWord ++ tailWord_957107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957107).length < 2 ^ (prefixWord ++ tailWord_957107).sum := by decide
  have hdescent : baseEnd_957107 < baseStart_957107 := by decide
  rcases family_descends (prefixWord ++ tailWord_957107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957114 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_957114 : Nat := 118140960795 + 957114 * 2 ^ 59
def prefixEnd_957114 : Nat := 4983230072969 + 3 ^ 40 * 957114 * 2
def baseEnd_957114 : Nat := 436852909464420907354061

theorem tailTrace_957114 : CollatzResearch.WordTrace tailWord_957114 prefixEnd_957114 436852909464420907354061 := by
  unfold tailWord_957114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8727203863636728725607599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23272543636364609934953597 8727203863636728725607599)
  ·
    refine ⟨13090805795455093088411399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8727203863636728725607599 13090805795455093088411399)
    ·
      refine ⟨19636208693182639632617099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13090805795455093088411399 19636208693182639632617099)
      ·
        refine ⟨29454313039773959448925649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19636208693182639632617099 29454313039773959448925649)
        ·
          refine ⟨22090734779830469586694237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29454313039773959448925649 22090734779830469586694237)
          ·
            refine ⟨8284025542436426095010339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22090734779830469586694237 8284025542436426095010339)
            ·
              refine ⟨12426038313654639142515509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284025542436426095010339 12426038313654639142515509)
              ·
                refine ⟨1164941091905122419610829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12426038313654639142515509 1164941091905122419610829)
                ·
                  refine ⟨436852909464420907354061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164941091905122419610829 436852909464420907354061)
                  ·
                    rfl

theorem cell20_957114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_957114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957114 prefixEnd_957114 := by exact prefixLift 957114
  have htrace : WordTrace (prefixWord ++ tailWord_957114) baseStart_957114 baseEnd_957114 := by
    simpa [prefixWord, tailWord_957114, baseEnd_957114] using wordTrace_append hprefix tailTrace_957114
  have hstable : (prefixWord ++ tailWord_957114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957114).length < 2 ^ (prefixWord ++ tailWord_957114).sum := by decide
  have hdescent : baseEnd_957114 < baseStart_957114 := by decide
  rcases family_descends (prefixWord ++ tailWord_957114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957124 : List Nat := [2, 3, 3, 1, 1, 3, 3, 4]
def baseStart_957124 : Nat := 118140960795 + 957124 * 2 ^ 59
def prefixEnd_957124 : Nat := 4983230072969 + 3 ^ 40 * 957124 * 2
def baseEnd_957124 : Nat := 145619157912301772340229

theorem tailTrace_957124 : CollatzResearch.WordTrace tailWord_957124 prefixEnd_957124 145619157912301772340229 := by
  unfold tailWord_957124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17454590092255343305147213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23272786789673791073529617 17454590092255343305147213)
  ·
    refine ⟨6545471284595753739430205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17454590092255343305147213 6545471284595753739430205)
    ·
      refine ⟨2454551731723407652286327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6545471284595753739430205 2454551731723407652286327)
      ·
        refine ⟨3681827597585111478429491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454551731723407652286327 3681827597585111478429491)
        ·
          refine ⟨5522741396377667217644237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681827597585111478429491 5522741396377667217644237)
          ·
            refine ⟨2071028023641625206616589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5522741396377667217644237 2071028023641625206616589)
            ·
              refine ⟨776635508865609452481221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2071028023641625206616589 776635508865609452481221)
              ·
                refine ⟨145619157912301772340229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 776635508865609452481221 145619157912301772340229)
                ·
                  rfl

theorem cell20_957124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_957124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957124 prefixEnd_957124 := by exact prefixLift 957124
  have htrace : WordTrace (prefixWord ++ tailWord_957124) baseStart_957124 baseEnd_957124 := by
    simpa [prefixWord, tailWord_957124, baseEnd_957124] using wordTrace_append hprefix tailTrace_957124
  have hstable : (prefixWord ++ tailWord_957124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957124).length < 2 ^ (prefixWord ++ tailWord_957124).sum := by decide
  have hdescent : baseEnd_957124 < baseStart_957124 := by decide
  rcases family_descends (prefixWord ++ tailWord_957124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957148 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 3]
def baseStart_957148 : Nat := 118140960795 + 957148 * 2 ^ 59
def prefixEnd_957148 : Nat := 4983230072969 + 3 ^ 40 * 957148 * 2
def baseEnd_957148 : Nat := 436868427990867900220589

theorem tailTrace_957148 : CollatzResearch.WordTrace tailWord_957148 prefixEnd_957148 436868427990867900220589 := by
  unfold tailWord_957148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455027768211869354584049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23273370357615825806112065 17455027768211869354584049)
  ·
    refine ⟨13091270826158902015938037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17455027768211869354584049 13091270826158902015938037)
    ·
      refine ⟨1227306639952397063994191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13091270826158902015938037 1227306639952397063994191)
      ·
        refine ⟨1840959959928595595991287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227306639952397063994191 1840959959928595595991287)
        ·
          refine ⟨2761439939892893393986931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840959959928595595991287 2761439939892893393986931)
          ·
            refine ⟨4142159909839340090980397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761439939892893393986931 4142159909839340090980397)
            ·
              refine ⟨1553309966189752534117649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4142159909839340090980397 1553309966189752534117649)
              ·
                refine ⟨1164982474642314400588237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553309966189752534117649 1164982474642314400588237)
                ·
                  refine ⟨436868427990867900220589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164982474642314400588237 436868427990867900220589)
                  ·
                    rfl

theorem cell20_957148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_957148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957148 prefixEnd_957148 := by exact prefixLift 957148
  have htrace : WordTrace (prefixWord ++ tailWord_957148) baseStart_957148 baseEnd_957148 := by
    simpa [prefixWord, tailWord_957148, baseEnd_957148] using wordTrace_append hprefix tailTrace_957148
  have hstable : (prefixWord ++ tailWord_957148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957148).length < 2 ^ (prefixWord ++ tailWord_957148).sum := by decide
  have hdescent : baseEnd_957148 < baseStart_957148 := by decide
  rcases family_descends (prefixWord ++ tailWord_957148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957155 : List Nat := [1, 1, 1, 7, 1, 1, 2, 4, 2]
def baseStart_957155 : Nat := 118140960795 + 957155 * 2 ^ 59
def prefixEnd_957155 : Nat := 4983230072969 + 3 ^ 40 * 957155 * 2
def baseEnd_957155 : Nat := 436871622981606986987227

theorem tailTrace_957155 : CollatzResearch.WordTrace tailWord_957155 prefixEnd_957155 436871622981606986987227 := by
  unfold tailWord_957155
  simp only [CollatzResearch.WordTrace]
  refine ⟨34910310847398378904672919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23273540564932252603115279 34910310847398378904672919)
  ·
    refine ⟨52365466271097568357009379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34910310847398378904672919 52365466271097568357009379)
    ·
      refine ⟨78548199406646352535514069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52365466271097568357009379 78548199406646352535514069)
      ·
        refine ⟨1840973423593273887551111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 78548199406646352535514069 1840973423593273887551111)
        ·
          refine ⟨2761460135389910831326667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840973423593273887551111 2761460135389910831326667)
          ·
            refine ⟨4142190203084866246990001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761460135389910831326667 4142190203084866246990001)
            ·
              refine ⟨3106642652313649685242501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142190203084866246990001 3106642652313649685242501)
              ·
                refine ⟨582495497308809315982969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3106642652313649685242501 582495497308809315982969)
                ·
                  refine ⟨436871622981606986987227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582495497308809315982969 436871622981606986987227)
                  ·
                    rfl

theorem cell20_957155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 2].length) (baseStart_957155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957155 prefixEnd_957155 := by exact prefixLift 957155
  have htrace : WordTrace (prefixWord ++ tailWord_957155) baseStart_957155 baseEnd_957155 := by
    simpa [prefixWord, tailWord_957155, baseEnd_957155] using wordTrace_append hprefix tailTrace_957155
  have hstable : (prefixWord ++ tailWord_957155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957155).length < 2 ^ (prefixWord ++ tailWord_957155).sum := by decide
  have hdescent : baseEnd_957155 < baseStart_957155 := by decide
  rcases family_descends (prefixWord ++ tailWord_957155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957169 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 3]
def baseStart_957169 : Nat := 118140960795 + 957169 * 2 ^ 59
def prefixEnd_957169 : Nat := 4983230072969 + 3 ^ 40 * 957169 * 2
def baseEnd_957169 : Nat := 436878012963085160520503

theorem tailTrace_957169 : CollatzResearch.WordTrace tailWord_957169 prefixEnd_957169 436878012963085160520503 := by
  unfold tailWord_957169
  simp only [CollatzResearch.WordTrace]
  refine ⟨34910821469347659295682561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23273880979565106197121707 34910821469347659295682561)
  ·
    refine ⟨26183116102010744471761921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34910821469347659295682561 26183116102010744471761921)
    ·
      refine ⟨19637337076508058353821441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26183116102010744471761921 19637337076508058353821441)
      ·
        refine ⟨14728002807381043765366081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19637337076508058353821441 14728002807381043765366081)
        ·
          refine ⟨11046002105535782824024561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14728002807381043765366081 11046002105535782824024561)
          ·
            refine ⟨8284501579151837118018421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11046002105535782824024561 8284501579151837118018421)
            ·
              refine ⟨776672023045484729814227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8284501579151837118018421 776672023045484729814227)
              ·
                refine ⟨1165008034568227094721341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776672023045484729814227 1165008034568227094721341)
                ·
                  refine ⟨436878012963085160520503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165008034568227094721341 436878012963085160520503)
                  ·
                    rfl

theorem cell20_957169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_957169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957169 prefixEnd_957169 := by exact prefixLift 957169
  have htrace : WordTrace (prefixWord ++ tailWord_957169) baseStart_957169 baseEnd_957169 := by
    simpa [prefixWord, tailWord_957169, baseEnd_957169] using wordTrace_append hprefix tailTrace_957169
  have hstable : (prefixWord ++ tailWord_957169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957169).length < 2 ^ (prefixWord ++ tailWord_957169).sum := by decide
  have hdescent : baseEnd_957169 < baseStart_957169 := by decide
  rcases family_descends (prefixWord ++ tailWord_957169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957228 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 3]
def baseStart_957228 : Nat := 118140960795 + 957228 * 2 ^ 59
def prefixEnd_957228 : Nat := 4983230072969 + 3 ^ 40 * 957228 * 2
def baseEnd_957228 : Nat := 436904942170743177553595

theorem tailTrace_957228 : CollatzResearch.WordTrace tailWord_957228 prefixEnd_957228 436904942170743177553595 := by
  unfold tailWord_957228
  simp only [CollatzResearch.WordTrace]
  refine ⟨17456486688066956186040169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23275315584089274914720225 17456486688066956186040169)
  ·
    refine ⟨13092365016050217139530127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17456486688066956186040169 13092365016050217139530127)
    ·
      refine ⟨19638547524075325709295191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13092365016050217139530127 19638547524075325709295191)
      ·
        refine ⟨29457821286112988563942787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19638547524075325709295191 29457821286112988563942787)
        ·
          refine ⟨44186731929169482845914181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29457821286112988563942787 44186731929169482845914181)
          ·
            refine ⟨8285012236719278033608909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44186731929169482845914181 8285012236719278033608909)
            ·
              refine ⟨3106879588769729262603341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8285012236719278033608909 3106879588769729262603341)
              ·
                refine ⟨1165079845788648473476253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3106879588769729262603341 1165079845788648473476253)
                ·
                  refine ⟨436904942170743177553595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165079845788648473476253 436904942170743177553595)
                  ·
                    rfl

theorem cell20_957228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_957228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957228 prefixEnd_957228 := by exact prefixLift 957228
  have htrace : WordTrace (prefixWord ++ tailWord_957228) baseStart_957228 baseEnd_957228 := by
    simpa [prefixWord, tailWord_957228, baseEnd_957228] using wordTrace_append hprefix tailTrace_957228
  have hstable : (prefixWord ++ tailWord_957228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957228).length < 2 ^ (prefixWord ++ tailWord_957228).sum := by decide
  have hdescent : baseEnd_957228 < baseStart_957228 := by decide
  rcases family_descends (prefixWord ++ tailWord_957228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957265 : List Nat := [1, 2, 2, 1, 7, 1, 2, 2, 2]
def baseStart_957265 : Nat := 118140960795 + 957265 * 2 ^ 59
def prefixEnd_957265 : Nat := 4983230072969 + 3 ^ 40 * 957265 * 2
def baseEnd_957265 : Nat := 436921829978935493320111

theorem tailTrace_957265 : CollatzResearch.WordTrace tailWord_957265 prefixEnd_957265 436921829978935493320111 := by
  unfold tailWord_957265
  simp only [CollatzResearch.WordTrace]
  refine ⟨34914322876999867691177249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23276215251333245127451499 34914322876999867691177249)
  ·
    refine ⟨26185742157749900768382937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34914322876999867691177249 26185742157749900768382937)
    ·
      refine ⟨19639306618312425576287203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26185742157749900768382937 19639306618312425576287203)
      ·
        refine ⟨29458959927468638364430805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19639306618312425576287203 29458959927468638364430805)
        ·
          refine ⟨690444373300046211666347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 29458959927468638364430805 690444373300046211666347)
          ·
            refine ⟨1035666559950069317499521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690444373300046211666347 1035666559950069317499521)
            ·
              refine ⟨776749919962551988124641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1035666559950069317499521 776749919962551988124641)
              ·
                refine ⟨582562439971913991093481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776749919962551988124641 582562439971913991093481)
                ·
                  refine ⟨436921829978935493320111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582562439971913991093481 436921829978935493320111)
                  ·
                    rfl

theorem cell20_957265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_957265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957265 prefixEnd_957265 := by exact prefixLift 957265
  have htrace : WordTrace (prefixWord ++ tailWord_957265) baseStart_957265 baseEnd_957265 := by
    simpa [prefixWord, tailWord_957265, baseEnd_957265] using wordTrace_append hprefix tailTrace_957265
  have hstable : (prefixWord ++ tailWord_957265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957265).length < 2 ^ (prefixWord ++ tailWord_957265).sum := by decide
  have hdescent : baseEnd_957265 < baseStart_957265 := by decide
  rcases family_descends (prefixWord ++ tailWord_957265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957276 : List Nat := [2, 2, 4, 2, 1, 3, 1, 5]
def baseStart_957276 : Nat := 118140960795 + 957276 * 2 ^ 59
def prefixEnd_957276 : Nat := 4983230072969 + 3 ^ 40 * 957276 * 2
def baseEnd_957276 : Nat := 145642283559556114651133

theorem tailTrace_957276 : CollatzResearch.WordTrace tailWord_957276 prefixEnd_957276 145642283559556114651133 := by
  unfold tailWord_957276
  simp only [CollatzResearch.WordTrace]
  refine ⟨17457362039980008284913841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23276482719973344379885121 17457362039980008284913841)
  ·
    refine ⟨13093021529985006213685381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17457362039980008284913841 13093021529985006213685381)
    ·
      refine ⟨2454941536872188665066009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13093021529985006213685381 2454941536872188665066009)
      ·
        refine ⟨1841206152654141498799507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2454941536872188665066009 1841206152654141498799507)
        ·
          refine ⟨2761809228981212248199261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841206152654141498799507 2761809228981212248199261)
          ·
            refine ⟨1035678460867954593074723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2761809228981212248199261 1035678460867954593074723)
            ·
              refine ⟨1553517691301931889612085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035678460867954593074723 1553517691301931889612085)
              ·
                refine ⟨145642283559556114651133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1553517691301931889612085 145642283559556114651133)
                ·
                  rfl

theorem cell20_957276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_957276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957276 prefixEnd_957276 := by exact prefixLift 957276
  have htrace : WordTrace (prefixWord ++ tailWord_957276) baseStart_957276 baseEnd_957276 := by
    simpa [prefixWord, tailWord_957276, baseEnd_957276] using wordTrace_append hprefix tailTrace_957276
  have hstable : (prefixWord ++ tailWord_957276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957276).length < 2 ^ (prefixWord ++ tailWord_957276).sum := by decide
  have hdescent : baseEnd_957276 < baseStart_957276 := by decide
  rcases family_descends (prefixWord ++ tailWord_957276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957297 : List Nat := [1, 2, 2, 2, 1, 5, 3, 4]
def baseStart_957297 : Nat := 118140960795 + 957297 * 2 ^ 59
def prefixEnd_957297 : Nat := 4983230072969 + 3 ^ 40 * 957297 * 2
def baseEnd_957297 : Nat := 145645478550295201417771

theorem tailTrace_957297 : CollatzResearch.WordTrace tailWord_957297 prefixEnd_957297 145645478550295201417771 := by
  unfold tailWord_957297
  simp only [CollatzResearch.WordTrace]
  refine ⟨34915490012883937156342145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23276993341922624770894763 34915490012883937156342145)
  ·
    refine ⟨26186617509662952867256609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34915490012883937156342145 26186617509662952867256609)
    ·
      refine ⟨19639963132247214650442457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26186617509662952867256609 19639963132247214650442457)
      ·
        refine ⟨14729972349185410987831843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19639963132247214650442457 14729972349185410987831843)
        ·
          refine ⟨22094958523778116481747765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14729972349185410987831843 22094958523778116481747765)
          ·
            refine ⟨2071402361604198420163853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22094958523778116481747765 2071402361604198420163853)
            ·
              refine ⟨776775885601574407561445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2071402361604198420163853 776775885601574407561445)
              ·
                refine ⟨145645478550295201417771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 776775885601574407561445 145645478550295201417771)
                ·
                  rfl

theorem cell20_957297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 4].length) (baseStart_957297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957297 prefixEnd_957297 := by exact prefixLift 957297
  have htrace : WordTrace (prefixWord ++ tailWord_957297) baseStart_957297 baseEnd_957297 := by
    simpa [prefixWord, tailWord_957297, baseEnd_957297] using wordTrace_append hprefix tailTrace_957297
  have hstable : (prefixWord ++ tailWord_957297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957297).length < 2 ^ (prefixWord ++ tailWord_957297).sum := by decide
  have hdescent : baseEnd_957297 < baseStart_957297 := by decide
  rcases family_descends (prefixWord ++ tailWord_957297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957321 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 3]
def baseStart_957321 : Nat := 118140960795 + 957321 * 2 ^ 59
def prefixEnd_957321 : Nat := 4983230072969 + 3 ^ 40 * 957321 * 2
def baseEnd_957321 : Nat := 436947389904848187453215

theorem tailTrace_957321 : CollatzResearch.WordTrace tailWord_957321 prefixEnd_957321 436947389904848187453215 := by
  unfold tailWord_957321
  simp only [CollatzResearch.WordTrace]
  refine ⟨34916365364796989255215817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23277576909864659503477211 34916365364796989255215817)
  ·
    refine ⟨26187274023597741941411863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34916365364796989255215817 26187274023597741941411863)
    ·
      refine ⟨39280911035396612912117795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26187274023597741941411863 39280911035396612912117795)
      ·
        refine ⟨58921366553094919368176693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39280911035396612912117795 58921366553094919368176693)
        ·
          refine ⟨5523878114352648690766565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58921366553094919368176693 5523878114352648690766565)
          ·
            refine ⟨1035727146441121629518731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5523878114352648690766565 1035727146441121629518731)
            ·
              refine ⟨1553590719661682444278097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035727146441121629518731 1553590719661682444278097)
              ·
                refine ⟨1165193039746261833208573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553590719661682444278097 1165193039746261833208573)
                ·
                  refine ⟨436947389904848187453215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165193039746261833208573 436947389904848187453215)
                  ·
                    rfl

theorem cell20_957321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_957321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957321 prefixEnd_957321 := by exact prefixLift 957321
  have htrace : WordTrace (prefixWord ++ tailWord_957321) baseStart_957321 baseEnd_957321 := by
    simpa [prefixWord, tailWord_957321, baseEnd_957321] using wordTrace_append hprefix tailTrace_957321
  have hstable : (prefixWord ++ tailWord_957321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957321).length < 2 ^ (prefixWord ++ tailWord_957321).sum := by decide
  have hdescent : baseEnd_957321 < baseStart_957321 := by decide
  rcases family_descends (prefixWord ++ tailWord_957321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957334 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_957334 : Nat := 118140960795 + 957334 * 2 ^ 59
def prefixEnd_957334 : Nat := 4983230072969 + 3 ^ 40 * 957334 * 2
def baseEnd_957334 : Nat := 436953323459077920019829

theorem tailTrace_957334 : CollatzResearch.WordTrace tailWord_957334 prefixEnd_957334 436953323459077920019829 := by
  unfold tailWord_957334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182302469609368279714941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23277893009166594983626037 2182302469609368279714941)
  ·
    refine ⟨818363426103513104893103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2182302469609368279714941 818363426103513104893103)
    ·
      refine ⟨1227545139155269657339655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 818363426103513104893103 1227545139155269657339655)
      ·
        refine ⟨1841317708732904486009483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227545139155269657339655 1841317708732904486009483)
        ·
          refine ⟨2761976563099356729014225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841317708732904486009483 2761976563099356729014225)
          ·
            refine ⟨2071482422324517546760669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2761976563099356729014225 2071482422324517546760669)
            ·
              refine ⟨776805908371694080035251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2071482422324517546760669 776805908371694080035251)
              ·
                refine ⟨1165208862557541120052877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776805908371694080035251 1165208862557541120052877)
                ·
                  refine ⟨436953323459077920019829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165208862557541120052877 436953323459077920019829)
                  ·
                    rfl

theorem cell20_957334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_957334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957334 prefixEnd_957334 := by exact prefixLift 957334
  have htrace : WordTrace (prefixWord ++ tailWord_957334) baseStart_957334 baseEnd_957334 := by
    simpa [prefixWord, tailWord_957334, baseEnd_957334] using wordTrace_append hprefix tailTrace_957334
  have hstable : (prefixWord ++ tailWord_957334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957334).length < 2 ^ (prefixWord ++ tailWord_957334).sum := by decide
  have hdescent : baseEnd_957334 < baseStart_957334 := by decide
  rcases family_descends (prefixWord ++ tailWord_957334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957338 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_957338 : Nat := 118140960795 + 957338 * 2 ^ 59
def prefixEnd_957338 : Nat := 4983230072969 + 3 ^ 40 * 957338 * 2
def baseEnd_957338 : Nat := 436955149168071683886479

theorem tailTrace_957338 : CollatzResearch.WordTrace tailWord_957338 prefixEnd_957338 436955149168071683886479 := by
  unfold tailWord_957338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8729246351433850289646167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23277990270490267439056445 8729246351433850289646167)
  ·
    refine ⟨13093869527150775434469251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8729246351433850289646167 13093869527150775434469251)
    ·
      refine ⟨19640804290726163151703877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13093869527150775434469251 19640804290726163151703877)
      ·
        refine ⟨3682650804511155590944477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19640804290726163151703877 3682650804511155590944477)
        ·
          refine ⟨1380994051691683346604179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3682650804511155590944477 1380994051691683346604179)
          ·
            refine ⟨2071491077537525019906269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380994051691683346604179 2071491077537525019906269)
            ·
              refine ⟨776809154076571882464851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2071491077537525019906269 776809154076571882464851)
              ·
                refine ⟨1165213731114857823697277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776809154076571882464851 1165213731114857823697277)
                ·
                  refine ⟨436955149168071683886479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165213731114857823697277 436955149168071683886479)
                  ·
                    rfl

theorem cell20_957338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_957338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957338 prefixEnd_957338 := by exact prefixLift 957338
  have htrace : WordTrace (prefixWord ++ tailWord_957338) baseStart_957338 baseEnd_957338 := by
    simpa [prefixWord, tailWord_957338, baseEnd_957338] using wordTrace_append hprefix tailTrace_957338
  have hstable : (prefixWord ++ tailWord_957338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957338).length < 2 ^ (prefixWord ++ tailWord_957338).sum := by decide
  have hdescent : baseEnd_957338 < baseStart_957338 := by decide
  rcases family_descends (prefixWord ++ tailWord_957338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957373 : List Nat := [1, 4, 1, 2, 4, 2, 6]
def baseStart_957373 : Nat := 118140960795 + 957373 * 2 ^ 59
def prefixEnd_957373 : Nat := 4983230072969 + 3 ^ 40 * 957373 * 2
def baseEnd_957373 : Nat := 48552347124640790857741

theorem tailTrace_957373 : CollatzResearch.WordTrace tailWord_957373 prefixEnd_957373 48552347124640790857741 := by
  unfold tailWord_957373
  simp only [CollatzResearch.WordTrace]
  refine ⟨34918261960608602136108773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23278841307072401424072515 34918261960608602136108773)
  ·
    refine ⟨6547174117614112900520395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34918261960608602136108773 6547174117614112900520395)
    ·
      refine ⟨9820761176421169350780593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6547174117614112900520395 9820761176421169350780593)
      ·
        refine ⟨7365570882315877013085445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9820761176421169350780593 7365570882315877013085445)
        ·
          refine ⟨1381044540434226939953521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7365570882315877013085445 1381044540434226939953521)
          ·
            refine ⟨1035783405325670204965141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381044540434226939953521 1035783405325670204965141)
            ·
              refine ⟨48552347124640790857741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1035783405325670204965141 48552347124640790857741)
              ·
                rfl

theorem cell20_957373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 6].length) (baseStart_957373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957373 prefixEnd_957373 := by exact prefixLift 957373
  have htrace : WordTrace (prefixWord ++ tailWord_957373) baseStart_957373 baseEnd_957373 := by
    simpa [prefixWord, tailWord_957373, baseEnd_957373] using wordTrace_append hprefix tailTrace_957373
  have hstable : (prefixWord ++ tailWord_957373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957373).length < 2 ^ (prefixWord ++ tailWord_957373).sum := by decide
  have hdescent : baseEnd_957373 < baseStart_957373 := by decide
  rcases family_descends (prefixWord ++ tailWord_957373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957387 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 4]
def baseStart_957387 : Nat := 118140960795 + 957387 * 2 ^ 59
def prefixEnd_957387 : Nat := 4983230072969 + 3 ^ 40 * 957387 * 2
def baseEnd_957387 : Nat := 436977514103245291252945

theorem tailTrace_957387 : CollatzResearch.WordTrace tailWord_957387 prefixEnd_957387 436977514103245291252945 := by
  unfold tailWord_957387
  simp only [CollatzResearch.WordTrace]
  refine ⟨34918772582557882527118415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23279181721705255018078943 34918772582557882527118415)
  ·
    refine ⟨52378158873836823790677623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34918772582557882527118415 52378158873836823790677623)
    ·
      refine ⟨78567238310755235686016435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52378158873836823790677623 78567238310755235686016435)
      ·
        refine ⟨117850857466132853529024653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78567238310755235686016435 117850857466132853529024653)
        ·
          refine ⟨44194071549799820073384245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117850857466132853529024653 44194071549799820073384245)
          ·
            refine ⟨4143194207793733131879773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44194071549799820073384245 4143194207793733131879773)
            ·
              refine ⟨1553697827922649924454915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4143194207793733131879773 1553697827922649924454915)
              ·
                refine ⟨2330546741883974886682373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553697827922649924454915 2330546741883974886682373)
                ·
                  refine ⟨436977514103245291252945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2330546741883974886682373 436977514103245291252945)
                  ·
                    rfl

theorem cell20_957387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_957387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957387 prefixEnd_957387 := by exact prefixLift 957387
  have htrace : WordTrace (prefixWord ++ tailWord_957387) baseStart_957387 baseEnd_957387 := by
    simpa [prefixWord, tailWord_957387, baseEnd_957387] using wordTrace_append hprefix tailTrace_957387
  have hstable : (prefixWord ++ tailWord_957387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957387).length < 2 ^ (prefixWord ++ tailWord_957387).sum := by decide
  have hdescent : baseEnd_957387 < baseStart_957387 := by decide
  rcases family_descends (prefixWord ++ tailWord_957387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957389 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 3]
def baseStart_957389 : Nat := 118140960795 + 957389 * 2 ^ 59
def prefixEnd_957389 : Nat := 4983230072969 + 3 ^ 40 * 957389 * 2
def baseEnd_957389 : Nat := 436978426957742173186271

theorem tailTrace_957389 : CollatzResearch.WordTrace tailWord_957389 prefixEnd_957389 436978426957742173186271 := by
  unfold tailWord_957389
  simp only [CollatzResearch.WordTrace]
  refine ⟨34918845528550636868691221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23279230352367091245794147 34918845528550636868691221)
  ·
    refine ⟨1636820884150811103219901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34918845528550636868691221 1636820884150811103219901)
    ·
      refine ⟨613807831556554163707463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1636820884150811103219901 613807831556554163707463)
      ·
        refine ⟨920711747334831245561195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613807831556554163707463 920711747334831245561195)
        ·
          refine ⟨1381067621002246868341793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920711747334831245561195 1381067621002246868341793)
          ·
            refine ⟨1035800715751685151256345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381067621002246868341793 1035800715751685151256345)
            ·
              refine ⟨776850536813763863442259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1035800715751685151256345 776850536813763863442259)
              ·
                refine ⟨1165275805220645795163389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776850536813763863442259 1165275805220645795163389)
                ·
                  refine ⟨436978426957742173186271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165275805220645795163389 436978426957742173186271)
                  ·
                    rfl

theorem cell20_957389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_957389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957389 prefixEnd_957389 := by exact prefixLift 957389
  have htrace : WordTrace (prefixWord ++ tailWord_957389) baseStart_957389 baseEnd_957389 := by
    simpa [prefixWord, tailWord_957389, baseEnd_957389] using wordTrace_append hprefix tailTrace_957389
  have hstable : (prefixWord ++ tailWord_957389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957389).length < 2 ^ (prefixWord ++ tailWord_957389).sum := by decide
  have hdescent : baseEnd_957389 < baseStart_957389 := by decide
  rcases family_descends (prefixWord ++ tailWord_957389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957397 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 3]
def baseStart_957397 : Nat := 118140960795 + 957397 * 2 ^ 59
def prefixEnd_957397 : Nat := 4983230072969 + 3 ^ 40 * 957397 * 2
def baseEnd_957397 : Nat := 436982078375729700919571

theorem tailTrace_957397 : CollatzResearch.WordTrace tailWord_957397 prefixEnd_957397 436982078375729700919571 := by
  unfold tailWord_957397
  simp only [CollatzResearch.WordTrace]
  refine ⟨34919137312521654234982445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23279424875014436156654963 34919137312521654234982445)
  ·
    refine ⟨13094676492195620338118417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34919137312521654234982445 13094676492195620338118417)
    ·
      refine ⟨9821007369146715253588813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13094676492195620338118417 9821007369146715253588813)
      ·
        refine ⟨3682877763430018220095805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9821007369146715253588813 3682877763430018220095805)
        ·
          refine ⟨1381079161286256832535927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3682877763430018220095805 1381079161286256832535927)
          ·
            refine ⟨2071618741929385248803891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381079161286256832535927 2071618741929385248803891)
            ·
              refine ⟨3107428112894077873205837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071618741929385248803891 3107428112894077873205837)
              ·
                refine ⟨1165285542335279202452189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3107428112894077873205837 1165285542335279202452189)
                ·
                  refine ⟨436982078375729700919571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165285542335279202452189 436982078375729700919571)
                  ·
                    rfl

theorem cell20_957397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_957397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957397 prefixEnd_957397 := by exact prefixLift 957397
  have htrace : WordTrace (prefixWord ++ tailWord_957397) baseStart_957397 baseEnd_957397 := by
    simpa [prefixWord, tailWord_957397, baseEnd_957397] using wordTrace_append hprefix tailTrace_957397
  have hstable : (prefixWord ++ tailWord_957397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957397).length < 2 ^ (prefixWord ++ tailWord_957397).sum := by decide
  have hdescent : baseEnd_957397 < baseStart_957397 := by decide
  rcases family_descends (prefixWord ++ tailWord_957397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957438 : List Nat := [4, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_957438 : Nat := 118140960795 + 957438 * 2 ^ 59
def prefixEnd_957438 : Nat := 4983230072969 + 3 ^ 40 * 957438 * 2
def baseEnd_957438 : Nat := 437000791892915780552737

theorem tailTrace_957438 : CollatzResearch.WordTrace tailWord_957438 prefixEnd_957438 437000791892915780552737 := by
  unfold tailWord_957438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4365079088171639779653121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23280421803582078824816645 4365079088171639779653121)
  ·
    refine ⟨3273809316128729834739841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4365079088171639779653121 3273809316128729834739841)
    ·
      refine ⟨2455356987096547376054881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3273809316128729834739841 2455356987096547376054881)
      ·
        refine ⟨1841517740322410532041161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2455356987096547376054881 1841517740322410532041161)
        ·
          refine ⟨1381138305241807899030871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1841517740322410532041161 1381138305241807899030871)
          ·
            refine ⟨2071707457862711848546307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381138305241807899030871 2071707457862711848546307)
            ·
              refine ⟨3107561186794067772819461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071707457862711848546307 3107561186794067772819461)
              ·
                refine ⟨582667722523887707403649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3107561186794067772819461 582667722523887707403649)
                ·
                  refine ⟨437000791892915780552737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582667722523887707403649 437000791892915780552737)
                  ·
                    rfl

theorem cell20_957438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_957438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957438 prefixEnd_957438 := by exact prefixLift 957438
  have htrace : WordTrace (prefixWord ++ tailWord_957438) baseStart_957438 baseEnd_957438 := by
    simpa [prefixWord, tailWord_957438, baseEnd_957438] using wordTrace_append hprefix tailTrace_957438
  have hstable : (prefixWord ++ tailWord_957438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957438).length < 2 ^ (prefixWord ++ tailWord_957438).sum := by decide
  have hdescent : baseEnd_957438 < baseStart_957438 := by decide
  rcases family_descends (prefixWord ++ tailWord_957438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957463 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 6]
def baseStart_957463 : Nat := 118140960795 + 957463 * 2 ^ 59
def prefixEnd_957463 : Nat := 4983230072969 + 3 ^ 40 * 957463 * 2
def baseEnd_957463 : Nat := 437012202574126804719301

theorem tailTrace_957463 : CollatzResearch.WordTrace tailWord_957463 prefixEnd_957463 437012202574126804719301 := by
  unfold tailWord_957463
  simp only [CollatzResearch.WordTrace]
  refine ⟨34921544530282547506885043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23281029686855031671256695 34921544530282547506885043)
  ·
    refine ⟨52382316795423821260327565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34921544530282547506885043 52382316795423821260327565)
    ·
      refine ⟨19643368798283932972622837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52382316795423821260327565 19643368798283932972622837)
      ·
        refine ⟨1841565824839118716183391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19643368798283932972622837 1841565824839118716183391)
        ·
          refine ⟨2762348737258678074275087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841565824839118716183391 2762348737258678074275087)
          ·
            refine ⟨4143523105888017111412631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762348737258678074275087 4143523105888017111412631)
            ·
              refine ⟨6215284658832025667118947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143523105888017111412631 6215284658832025667118947)
              ·
                refine ⟨9322926988248038500678421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215284658832025667118947 9322926988248038500678421)
                ·
                  refine ⟨437012202574126804719301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9322926988248038500678421 437012202574126804719301)
                  ·
                    rfl

theorem cell20_957463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_957463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957463 prefixEnd_957463 := by exact prefixLift 957463
  have htrace : WordTrace (prefixWord ++ tailWord_957463) baseStart_957463 baseEnd_957463 := by
    simpa [prefixWord, tailWord_957463, baseEnd_957463] using wordTrace_append hprefix tailTrace_957463
  have hstable : (prefixWord ++ tailWord_957463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957463).length < 2 ^ (prefixWord ++ tailWord_957463).sum := by decide
  have hdescent : baseEnd_957463 < baseStart_957463 := by decide
  rcases family_descends (prefixWord ++ tailWord_957463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957477 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_957477 : Nat := 118140960795 + 957477 * 2 ^ 59
def prefixEnd_957477 : Nat := 4983230072969 + 3 ^ 40 * 957477 * 2
def baseEnd_957477 : Nat := 437018592555604978252577

theorem tailTrace_957477 : CollatzResearch.WordTrace tailWord_957477 prefixEnd_957477 437018592555604978252577 := by
  unfold tailWord_957477
  simp only [CollatzResearch.WordTrace]
  refine ⟨34922055152231827897894685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23281370101487885265263123 34922055152231827897894685)
  ·
    refine ⟨13095770682086935461710507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34922055152231827897894685 13095770682086935461710507)
    ·
      refine ⟨19643656023130403192565761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13095770682086935461710507 19643656023130403192565761)
      ·
        refine ⟨14732742017347802394424321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19643656023130403192565761 14732742017347802394424321)
        ·
          refine ⟨11049556513010851795818241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14732742017347802394424321 11049556513010851795818241)
          ·
            refine ⟨8287167384758138846863681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11049556513010851795818241 8287167384758138846863681)
            ·
              refine ⟨6215375538568604135147761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8287167384758138846863681 6215375538568604135147761)
              ·
                refine ⟨4661531653926453101360821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6215375538568604135147761 4661531653926453101360821)
                ·
                  refine ⟨437018592555604978252577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4661531653926453101360821 437018592555604978252577)
                  ·
                    rfl

theorem cell20_957477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_957477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957477 prefixEnd_957477 := by exact prefixLift 957477
  have htrace : WordTrace (prefixWord ++ tailWord_957477) baseStart_957477 baseEnd_957477 := by
    simpa [prefixWord, tailWord_957477, baseEnd_957477] using wordTrace_append hprefix tailTrace_957477
  have hstable : (prefixWord ++ tailWord_957477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957477).length < 2 ^ (prefixWord ++ tailWord_957477).sum := by decide
  have hdescent : baseEnd_957477 < baseStart_957477 := by decide
  rcases family_descends (prefixWord ++ tailWord_957477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957484 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_957484 : Nat := 118140960795 + 957484 * 2 ^ 59
def prefixEnd_957484 : Nat := 4983230072969 + 3 ^ 40 * 957484 * 2
def baseEnd_957484 : Nat := 437021787546344065019215

theorem tailTrace_957484 : CollatzResearch.WordTrace tailWord_957484 prefixEnd_957484 437021787546344065019215 := by
  unfold tailWord_957484
  simp only [CollatzResearch.WordTrace]
  refine ⟨17461155231603234046699753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23281540308804312062266337 17461155231603234046699753)
  ·
    refine ⟨13095866423702425535024815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17461155231603234046699753 13095866423702425535024815)
    ·
      refine ⟨19643799635553638302537223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13095866423702425535024815 19643799635553638302537223)
      ·
        refine ⟨29465699453330457453805835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19643799635553638302537223 29465699453330457453805835)
        ·
          refine ⟨44198549179995686180708753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29465699453330457453805835 44198549179995686180708753)
          ·
            refine ⟨33148911884996764635531565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44198549179995686180708753 33148911884996764635531565)
            ·
              refine ⟨12430841956873786738324337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33148911884996764635531565 12430841956873786738324337)
              ·
                refine ⟨9323131467655340053743253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12430841956873786738324337 9323131467655340053743253)
                ·
                  refine ⟨437021787546344065019215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9323131467655340053743253 437021787546344065019215)
                  ·
                    rfl

theorem cell20_957484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_957484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957484 prefixEnd_957484 := by exact prefixLift 957484
  have htrace : WordTrace (prefixWord ++ tailWord_957484) baseStart_957484 baseEnd_957484 := by
    simpa [prefixWord, tailWord_957484, baseEnd_957484] using wordTrace_append hprefix tailTrace_957484
  have hstable : (prefixWord ++ tailWord_957484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957484).length < 2 ^ (prefixWord ++ tailWord_957484).sum := by decide
  have hdescent : baseEnd_957484 < baseStart_957484 := by decide
  rcases family_descends (prefixWord ++ tailWord_957484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957501 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_957501 : Nat := 118140960795 + 957501 * 2 ^ 59
def prefixEnd_957501 : Nat := 4983230072969 + 3 ^ 40 * 957501 * 2
def baseEnd_957501 : Nat := 437029546809567561452479

theorem tailTrace_957501 : CollatzResearch.WordTrace tailWord_957501 prefixEnd_957501 437029546809567561452479 := by
  unfold tailWord_957501
  simp only [CollatzResearch.WordTrace]
  refine ⟨34922930504144879996768357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23281953669429919997845571 34922930504144879996768357)
  ·
    refine ⟨6548049469527164999394067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34922930504144879996768357 6548049469527164999394067)
    ·
      refine ⟨9822074204290747499091101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6548049469527164999394067 9822074204290747499091101)
      ·
        refine ⟨3683277826609030312159163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9822074204290747499091101 3683277826609030312159163)
        ·
          refine ⟨5524916739913545468238745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3683277826609030312159163 5524916739913545468238745)
          ·
            refine ⟨4143687554935159101179059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5524916739913545468238745 4143687554935159101179059)
            ·
              refine ⟨6215531332402738651768589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143687554935159101179059 6215531332402738651768589)
              ·
                refine ⟨2330824249651026994413221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6215531332402738651768589 2330824249651026994413221)
                ·
                  refine ⟨437029546809567561452479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2330824249651026994413221 437029546809567561452479)
                  ·
                    rfl

theorem cell20_957501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_957501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957501 prefixEnd_957501 := by exact prefixLift 957501
  have htrace : WordTrace (prefixWord ++ tailWord_957501) baseStart_957501 baseEnd_957501 := by
    simpa [prefixWord, tailWord_957501, baseEnd_957501] using wordTrace_append hprefix tailTrace_957501
  have hstable : (prefixWord ++ tailWord_957501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957501).length < 2 ^ (prefixWord ++ tailWord_957501).sum := by decide
  have hdescent : baseEnd_957501 < baseStart_957501 := by decide
  rcases family_descends (prefixWord ++ tailWord_957501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957511 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 3]
def baseStart_957511 : Nat := 118140960795 + 957511 * 2 ^ 59
def prefixEnd_957511 : Nat := 4983230072969 + 3 ^ 40 * 957511 * 2
def baseEnd_957511 : Nat := 437034111082051971119105

theorem tailTrace_957511 : CollatzResearch.WordTrace tailWord_957511 prefixEnd_957511 437034111082051971119105 := by
  unfold tailWord_957511
  simp only [CollatzResearch.WordTrace]
  refine ⟨34923295234108651704632387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23282196822739101136421591 34923295234108651704632387)
  ·
    refine ⟨52384942851162977556948581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34923295234108651704632387 52384942851162977556948581)
    ·
      refine ⟨9822176784593058291927859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52384942851162977556948581 9822176784593058291927859)
      ·
        refine ⟨14733265176889587437891789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9822176784593058291927859 14733265176889587437891789)
        ·
          refine ⟨5524974441333595289209421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14733265176889587437891789 5524974441333595289209421)
          ·
            refine ⟨2071865415500098233453533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5524974441333595289209421 2071865415500098233453533)
            ·
              refine ⟨776949530812536837545075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2071865415500098233453533 776949530812536837545075)
              ·
                refine ⟨1165424296218805256317613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776949530812536837545075 1165424296218805256317613)
                ·
                  refine ⟨437034111082051971119105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165424296218805256317613 437034111082051971119105)
                  ·
                    rfl

theorem cell20_957511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 3].length) (baseStart_957511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957511 prefixEnd_957511 := by exact prefixLift 957511
  have htrace : WordTrace (prefixWord ++ tailWord_957511) baseStart_957511 baseEnd_957511 := by
    simpa [prefixWord, tailWord_957511, baseEnd_957511] using wordTrace_append hprefix tailTrace_957511
  have hstable : (prefixWord ++ tailWord_957511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957511).length < 2 ^ (prefixWord ++ tailWord_957511).sum := by decide
  have hdescent : baseEnd_957511 < baseStart_957511 := by decide
  rcases family_descends (prefixWord ++ tailWord_957511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957546 : List Nat := [3, 1, 3, 2, 2, 1, 8]
def baseStart_957546 : Nat := 118140960795 + 957546 * 2 ^ 59
def prefixEnd_957546 : Nat := 4983230072969 + 3 ^ 40 * 957546 * 2
def baseEnd_957546 : Nat := 48561120670638600550255

theorem tailTrace_957546 : CollatzResearch.WordTrace tailWord_957546 prefixEnd_957546 48561120670638600550255 := by
  unfold tailWord_957546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731142947245463170539123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23283047859321235121437661 8731142947245463170539123)
  ·
    refine ⟨13096714420868194755808685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8731142947245463170539123 13096714420868194755808685)
    ·
      refine ⟨4911267907825573033428257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13096714420868194755808685 4911267907825573033428257)
      ·
        refine ⟨3683450930869179775071193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4911267907825573033428257 3683450930869179775071193)
        ·
          refine ⟨2762588198151884831303395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3683450930869179775071193 2762588198151884831303395)
          ·
            refine ⟨4143882297227827246955093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762588198151884831303395 4143882297227827246955093)
            ·
              refine ⟨48561120670638600550255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4143882297227827246955093 48561120670638600550255)
              ·
                rfl

theorem cell20_957546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 8].length) (baseStart_957546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957546 prefixEnd_957546 := by exact prefixLift 957546
  have htrace : WordTrace (prefixWord ++ tailWord_957546) baseStart_957546 baseEnd_957546 := by
    simpa [prefixWord, tailWord_957546, baseEnd_957546] using wordTrace_append hprefix tailTrace_957546
  have hstable : (prefixWord ++ tailWord_957546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957546).length < 2 ^ (prefixWord ++ tailWord_957546).sum := by decide
  have hdescent : baseEnd_957546 < baseStart_957546 := by decide
  rcases family_descends (prefixWord ++ tailWord_957546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957605 : List Nat := [1, 3, 1, 2, 1, 12]
def baseStart_957605 : Nat := 118140960795 + 957605 * 2 ^ 59
def prefixEnd_957605 : Nat := 4983230072969 + 3 ^ 40 * 957605 * 2
def baseEnd_957605 : Nat := 16188037601607608221681

theorem tailTrace_957605 : CollatzResearch.WordTrace tailWord_957605 prefixEnd_957605 16188037601607608221681 := by
  unfold tailWord_957605
  simp only [CollatzResearch.WordTrace]
  refine ⟨34926723695768105758554269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23284482463845403839036179 34926723695768105758554269)
  ·
    refine ⟨13097521385913039659457851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34926723695768105758554269 13097521385913039659457851)
    ·
      refine ⟨19646282078869559489186777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13097521385913039659457851 19646282078869559489186777)
      ·
        refine ⟨14734711559152169616890083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19646282078869559489186777 14734711559152169616890083)
        ·
          refine ⟨22102067338728254425335125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14734711559152169616890083 22102067338728254425335125)
          ·
            refine ⟨16188037601607608221681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22102067338728254425335125 16188037601607608221681)
            ·
              rfl

theorem cell20_957605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 12].length) (baseStart_957605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957605 prefixEnd_957605 := by exact prefixLift 957605
  have htrace : WordTrace (prefixWord ++ tailWord_957605) baseStart_957605 baseEnd_957605 := by
    simpa [prefixWord, tailWord_957605, baseEnd_957605] using wordTrace_append hprefix tailTrace_957605
  have hstable : (prefixWord ++ tailWord_957605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957605).length < 2 ^ (prefixWord ++ tailWord_957605).sum := by decide
  have hdescent : baseEnd_957605 < baseStart_957605 := by decide
  rcases family_descends (prefixWord ++ tailWord_957605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957645 : List Nat := [1, 6, 2, 2, 1, 1, 2, 3, 2]
def baseStart_957645 : Nat := 118140960795 + 957645 * 2 ^ 59
def prefixEnd_957645 : Nat := 4983230072969 + 3 ^ 40 * 957645 * 2
def baseEnd_957645 : Nat := 437095272333343060651891

theorem tailTrace_957645 : CollatzResearch.WordTrace tailWord_957645 prefixEnd_957645 437095272333343060651891 := by
  unfold tailWord_957645
  simp only [CollatzResearch.WordTrace]
  refine ⟨34928182615623192590010389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23285455077082128393340259 34928182615623192590010389)
  ·
    refine ⟨1637258560107337152656737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34928182615623192590010389 1637258560107337152656737)
    ·
      refine ⟨1227943920080502864492553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1637258560107337152656737 1227943920080502864492553)
      ·
        refine ⟨920957940060377148369415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1227943920080502864492553 920957940060377148369415)
        ·
          refine ⟨1381436910090565722554123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920957940060377148369415 1381436910090565722554123)
          ·
            refine ⟨2072155365135848583831185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381436910090565722554123 2072155365135848583831185)
            ·
              refine ⟨1554116523851886437873389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2072155365135848583831185 1554116523851886437873389)
              ·
                refine ⟨582793696444457414202521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1554116523851886437873389 582793696444457414202521)
                ·
                  refine ⟨437095272333343060651891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582793696444457414202521 437095272333343060651891)
                  ·
                    rfl

theorem cell20_957645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_957645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957645 prefixEnd_957645 := by exact prefixLift 957645
  have htrace : WordTrace (prefixWord ++ tailWord_957645) baseStart_957645 baseEnd_957645 := by
    simpa [prefixWord, tailWord_957645, baseEnd_957645] using wordTrace_append hprefix tailTrace_957645
  have hstable : (prefixWord ++ tailWord_957645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957645).length < 2 ^ (prefixWord ++ tailWord_957645).sum := by decide
  have hdescent : baseEnd_957645 < baseStart_957645 := by decide
  rcases family_descends (prefixWord ++ tailWord_957645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957681 : List Nat := [1, 2, 2, 2, 2, 1, 1, 9]
def baseStart_957681 : Nat := 118140960795 + 957681 * 2 ^ 59
def prefixEnd_957681 : Nat := 4983230072969 + 3 ^ 40 * 957681 * 2
def baseEnd_957681 : Nat := 145703901238095645150581

theorem tailTrace_957681 : CollatzResearch.WordTrace tailWord_957681 prefixEnd_957681 145703901238095645150581 := by
  unfold tailWord_957681
  simp only [CollatzResearch.WordTrace]
  refine ⟨34929495643492770738320897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23286330428995180492213931 34929495643492770738320897)
  ·
    refine ⟨26197121732619578053740673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34929495643492770738320897 26197121732619578053740673)
    ·
      refine ⟨19647841299464683540305505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26197121732619578053740673 19647841299464683540305505)
      ·
        refine ⟨14735880974598512655229129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19647841299464683540305505 14735880974598512655229129)
        ·
          refine ⟨11051910730948884491421847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14735880974598512655229129 11051910730948884491421847)
          ·
            refine ⟨16577866096423326737132771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11051910730948884491421847 16577866096423326737132771)
            ·
              refine ⟨24866799144634990105699157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16577866096423326737132771 24866799144634990105699157)
              ·
                refine ⟨145703901238095645150581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24866799144634990105699157 145703901238095645150581)
                ·
                  rfl

theorem cell20_957681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_957681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957681 prefixEnd_957681 := by exact prefixLift 957681
  have htrace : WordTrace (prefixWord ++ tailWord_957681) baseStart_957681 baseEnd_957681 := by
    simpa [prefixWord, tailWord_957681, baseEnd_957681] using wordTrace_append hprefix tailTrace_957681
  have hstable : (prefixWord ++ tailWord_957681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957681).length < 2 ^ (prefixWord ++ tailWord_957681).sum := by decide
  have hdescent : baseEnd_957681 < baseStart_957681 := by decide
  rcases family_descends (prefixWord ++ tailWord_957681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957694 : List Nat := [4, 2, 2, 1, 1, 4, 2, 4]
def baseStart_957694 : Nat := 118140960795 + 957694 * 2 ^ 59
def prefixEnd_957694 : Nat := 4983230072969 + 3 ^ 40 * 957694 * 2
def baseEnd_957694 : Nat := 145705879089505556006119

theorem tailTrace_957694 : CollatzResearch.WordTrace tailWord_957694 prefixEnd_957694 145705879089505556006119 := by
  unfold tailWord_957694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4366246224055709244818017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23286646528297115972362757 4366246224055709244818017)
  ·
    refine ⟨3274684668041781933613513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4366246224055709244818017 3274684668041781933613513)
    ·
      refine ⟨2456013501031336450210135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3274684668041781933613513 2456013501031336450210135)
      ·
        refine ⟨3684020251547004675315203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456013501031336450210135 3684020251547004675315203)
        ·
          refine ⟨5526030377320507012972805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684020251547004675315203 5526030377320507012972805)
          ·
            refine ⟨1036130695747595064932401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5526030377320507012972805 1036130695747595064932401)
            ·
              refine ⟨777098021810696298699301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036130695747595064932401 777098021810696298699301)
              ·
                refine ⟨145705879089505556006119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 777098021810696298699301 145705879089505556006119)
                ·
                  rfl

theorem cell20_957694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_957694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957694 prefixEnd_957694 := by exact prefixLift 957694
  have htrace : WordTrace (prefixWord ++ tailWord_957694) baseStart_957694 baseEnd_957694 := by
    simpa [prefixWord, tailWord_957694, baseEnd_957694] using wordTrace_append hprefix tailTrace_957694
  have hstable : (prefixWord ++ tailWord_957694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957694).length < 2 ^ (prefixWord ++ tailWord_957694).sum := by decide
  have hdescent : baseEnd_957694 < baseStart_957694 := by decide
  rcases family_descends (prefixWord ++ tailWord_957694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957704 : List Nat := [2, 1, 3, 2, 5, 1, 1, 3, 2]
def baseStart_957704 : Nat := 118140960795 + 957704 * 2 ^ 59
def prefixEnd_957704 : Nat := 4983230072969 + 3 ^ 40 * 957704 * 2
def baseEnd_957704 : Nat := 437122201541001077684983

theorem tailTrace_957704 : CollatzResearch.WordTrace tailWord_957704 prefixEnd_957704 437122201541001077684983 := by
  unfold tailWord_957704
  simp only [CollatzResearch.WordTrace]
  refine ⟨17465167261204722833204083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23286889681606297110938777 17465167261204722833204083)
  ·
    refine ⟨26197750891807084249806125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17465167261204722833204083 26197750891807084249806125)
    ·
      refine ⟨9824156584427656593677297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26197750891807084249806125 9824156584427656593677297)
      ·
        refine ⟨7368117438320742445257973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9824156584427656593677297 7368117438320742445257973)
        ·
          refine ⟨690761009842569604242935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7368117438320742445257973 690761009842569604242935)
          ·
            refine ⟨1036141514763854406364403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690761009842569604242935 1036141514763854406364403)
            ·
              refine ⟨1554212272145781609546605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036141514763854406364403 1554212272145781609546605)
              ·
                refine ⟨582829602054668103579977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1554212272145781609546605 582829602054668103579977)
                ·
                  refine ⟨437122201541001077684983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582829602054668103579977 437122201541001077684983)
                  ·
                    rfl

theorem cell20_957704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_957704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957704 prefixEnd_957704 := by exact prefixLift 957704
  have htrace : WordTrace (prefixWord ++ tailWord_957704) baseStart_957704 baseEnd_957704 := by
    simpa [prefixWord, tailWord_957704, baseEnd_957704] using wordTrace_append hprefix tailTrace_957704
  have hstable : (prefixWord ++ tailWord_957704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957704).length < 2 ^ (prefixWord ++ tailWord_957704).sum := by decide
  have hdescent : baseEnd_957704 < baseStart_957704 := by decide
  rcases family_descends (prefixWord ++ tailWord_957704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957708 : List Nat := [2, 2, 1, 2, 2, 3, 3, 3, 2]
def baseStart_957708 : Nat := 118140960795 + 957708 * 2 ^ 59
def prefixEnd_957708 : Nat := 4983230072969 + 3 ^ 40 * 957708 * 2
def baseEnd_957708 : Nat := 437124027249994841551633

theorem tailTrace_957708 : CollatzResearch.WordTrace tailWord_957708 prefixEnd_957708 437124027249994841551633 := by
  unfold tailWord_957708
  simp only [CollatzResearch.WordTrace]
  refine ⟨17465240207197477174776889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23286986942929969566369185 17465240207197477174776889)
  ·
    refine ⟨13098930155398107881082667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17465240207197477174776889 13098930155398107881082667)
    ·
      refine ⟨19648395233097161821624001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13098930155398107881082667 19648395233097161821624001)
      ·
        refine ⟨14736296424822871366218001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19648395233097161821624001 14736296424822871366218001)
        ·
          refine ⟨11052222318617153524663501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14736296424822871366218001 11052222318617153524663501)
          ·
            refine ⟨4144583369481432571748813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11052222318617153524663501 4144583369481432571748813)
            ·
              refine ⟨1554218763555537214405805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4144583369481432571748813 1554218763555537214405805)
              ·
                refine ⟨582832036333326455402177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1554218763555537214405805 582832036333326455402177)
                ·
                  refine ⟨437124027249994841551633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582832036333326455402177 437124027249994841551633)
                  ·
                    rfl

theorem cell20_957708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_957708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957708 prefixEnd_957708 := by exact prefixLift 957708
  have htrace : WordTrace (prefixWord ++ tailWord_957708) baseStart_957708 baseEnd_957708 := by
    simpa [prefixWord, tailWord_957708, baseEnd_957708] using wordTrace_append hprefix tailTrace_957708
  have hstable : (prefixWord ++ tailWord_957708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957708).length < 2 ^ (prefixWord ++ tailWord_957708).sum := by decide
  have hdescent : baseEnd_957708 < baseStart_957708 := by decide
  rcases family_descends (prefixWord ++ tailWord_957708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957736 : List Nat := [2, 1, 5, 1, 2, 1, 1, 7]
def baseStart_957736 : Nat := 118140960795 + 957736 * 2 ^ 59
def prefixEnd_957736 : Nat := 4983230072969 + 3 ^ 40 * 957736 * 2
def baseEnd_957736 : Nat := 145712269070983729539395

theorem tailTrace_957736 : CollatzResearch.WordTrace tailWord_957736 prefixEnd_957736 145712269070983729539395 := by
  unfold tailWord_957736
  simp only [CollatzResearch.WordTrace]
  refine ⟨17465750829146757565786531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23287667772195676754382041 17465750829146757565786531)
  ·
    refine ⟨26198626243720136348679797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17465750829146757565786531 26198626243720136348679797)
    ·
      refine ⟨2456121210348762782688731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26198626243720136348679797 2456121210348762782688731)
      ·
        refine ⟨3684181815523144174033097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456121210348762782688731 3684181815523144174033097)
        ·
          refine ⟨2763136361642358130524823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3684181815523144174033097 2763136361642358130524823)
          ·
            refine ⟨4144704542463537195787235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2763136361642358130524823 4144704542463537195787235)
            ·
              refine ⟨6217056813695305793680853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144704542463537195787235 6217056813695305793680853)
              ·
                refine ⟨145712269070983729539395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6217056813695305793680853 145712269070983729539395)
                ·
                  rfl

theorem cell20_957736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_957736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957736 prefixEnd_957736 := by exact prefixLift 957736
  have htrace : WordTrace (prefixWord ++ tailWord_957736) baseStart_957736 baseEnd_957736 := by
    simpa [prefixWord, tailWord_957736, baseEnd_957736] using wordTrace_append hprefix tailTrace_957736
  have hstable : (prefixWord ++ tailWord_957736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957736).length < 2 ^ (prefixWord ++ tailWord_957736).sum := by decide
  have hdescent : baseEnd_957736 < baseStart_957736 := by decide
  rcases family_descends (prefixWord ++ tailWord_957736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957805 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 4]
def baseStart_957805 : Nat := 118140960795 + 957805 * 2 ^ 59
def prefixEnd_957805 : Nat := 4983230072969 + 3 ^ 40 * 957805 * 2
def baseEnd_957805 : Nat := 437168300693093615317903

theorem tailTrace_957805 : CollatzResearch.WordTrace tailWord_957805 prefixEnd_957805 437168300693093615317903 := by
  unfold tailWord_957805
  simp only [CollatzResearch.WordTrace]
  refine ⟨34934018295043539915834869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23289345530029026610556579 34934018295043539915834869)
  ·
    refine ⟨3275064215160331867109519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34934018295043539915834869 3275064215160331867109519)
    ·
      refine ⟨4912596322740497800664279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3275064215160331867109519 4912596322740497800664279)
      ·
        refine ⟨7368894484110746700996419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912596322740497800664279 7368894484110746700996419)
        ·
          refine ⟨11053341726166120051494629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368894484110746700996419 11053341726166120051494629)
          ·
            refine ⟨2072501573656147509655243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11053341726166120051494629 2072501573656147509655243)
            ·
              refine ⟨3108752360484221264482865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072501573656147509655243 3108752360484221264482865)
              ·
                refine ⟨2331564270363165948362149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3108752360484221264482865 2331564270363165948362149)
                ·
                  refine ⟨437168300693093615317903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2331564270363165948362149 437168300693093615317903)
                  ·
                    rfl

theorem cell20_957805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_957805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957805 prefixEnd_957805 := by exact prefixLift 957805
  have htrace : WordTrace (prefixWord ++ tailWord_957805) baseStart_957805 baseEnd_957805 := by
    simpa [prefixWord, tailWord_957805, baseEnd_957805] using wordTrace_append hprefix tailTrace_957805
  have hstable : (prefixWord ++ tailWord_957805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957805).length < 2 ^ (prefixWord ++ tailWord_957805).sum := by decide
  have hdescent : baseEnd_957805 < baseStart_957805 := by decide
  rcases family_descends (prefixWord ++ tailWord_957805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957853 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 3]
def baseStart_957853 : Nat := 118140960795 + 957853 * 2 ^ 59
def prefixEnd_957853 : Nat := 4983230072969 + 3 ^ 40 * 957853 * 2
def baseEnd_957853 : Nat := 437190209201018781717707

theorem tailTrace_957853 : CollatzResearch.WordTrace tailWord_957853 prefixEnd_957853 437190209201018781717707 := by
  unfold tailWord_957853
  simp only [CollatzResearch.WordTrace]
  refine ⟨34935768998869644113582213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23290512665913096075721475 34935768998869644113582213)
  ·
    refine ⟨6550456687288058271296665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34935768998869644113582213 6550456687288058271296665)
    ·
      refine ⟨4912842515466043703472499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6550456687288058271296665 4912842515466043703472499)
      ·
        refine ⟨7369263773199065555208749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912842515466043703472499 7369263773199065555208749)
        ·
          refine ⟨2763473914949649583203281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7369263773199065555208749 2763473914949649583203281)
          ·
            refine ⟨2072605436212237187402461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2763473914949649583203281 2072605436212237187402461)
            ·
              refine ⟨777227038579588945275923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2072605436212237187402461 777227038579588945275923)
              ·
                refine ⟨1165840557869383417913885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777227038579588945275923 1165840557869383417913885)
                ·
                  refine ⟨437190209201018781717707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165840557869383417913885 437190209201018781717707)
                  ·
                    rfl

theorem cell20_957853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_957853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957853 prefixEnd_957853 := by exact prefixLift 957853
  have htrace : WordTrace (prefixWord ++ tailWord_957853) baseStart_957853 baseEnd_957853 := by
    simpa [prefixWord, tailWord_957853, baseEnd_957853] using wordTrace_append hprefix tailTrace_957853
  have hstable : (prefixWord ++ tailWord_957853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957853).length < 2 ^ (prefixWord ++ tailWord_957853).sum := by decide
  have hdescent : baseEnd_957853 < baseStart_957853 := by decide
  rcases family_descends (prefixWord ++ tailWord_957853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957877 : List Nat := [1, 3, 3, 2, 2, 3, 1, 3, 2]
def baseStart_957877 : Nat := 118140960795 + 957877 * 2 ^ 59
def prefixEnd_957877 : Nat := 4983230072969 + 3 ^ 40 * 957877 * 2
def baseEnd_957877 : Nat := 437201163454981364917609

theorem tailTrace_957877 : CollatzResearch.WordTrace tailWord_957877 prefixEnd_957877 437201163454981364917609 := by
  unfold tailWord_957877
  simp only [CollatzResearch.WordTrace]
  refine ⟨34936644350782696212455885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23291096233855130808303923 34936644350782696212455885)
  ·
    refine ⟨13101241631543511079670957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34936644350782696212455885 13101241631543511079670957)
    ·
      refine ⟨4912965611828816654876609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13101241631543511079670957 4912965611828816654876609)
      ·
        refine ⟨3684724208871612491157457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4912965611828816654876609 3684724208871612491157457)
        ·
          refine ⟨2763543156653709368368093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3684724208871612491157457 2763543156653709368368093)
          ·
            refine ⟨1036328683745141013138035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2763543156653709368368093 1036328683745141013138035)
            ·
              refine ⟨1554493025617711519707053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036328683745141013138035 1554493025617711519707053)
              ·
                refine ⟨582934884606641819890145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1554493025617711519707053 582934884606641819890145)
                ·
                  refine ⟨437201163454981364917609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582934884606641819890145 437201163454981364917609)
                  ·
                    rfl

theorem cell20_957877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_957877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957877 prefixEnd_957877 := by exact prefixLift 957877
  have htrace : WordTrace (prefixWord ++ tailWord_957877) baseStart_957877 baseEnd_957877 := by
    simpa [prefixWord, tailWord_957877, baseEnd_957877] using wordTrace_append hprefix tailTrace_957877
  have hstable : (prefixWord ++ tailWord_957877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957877).length < 2 ^ (prefixWord ++ tailWord_957877).sum := by decide
  have hdescent : baseEnd_957877 < baseStart_957877 := by decide
  rcases family_descends (prefixWord ++ tailWord_957877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957890 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 4]
def baseStart_957890 : Nat := 118140960795 + 957890 * 2 ^ 59
def prefixEnd_957890 : Nat := 4983230072969 + 3 ^ 40 * 957890 * 2
def baseEnd_957890 : Nat := 437207097009211097484223

theorem tailTrace_957890 : CollatzResearch.WordTrace tailWord_957890 prefixEnd_957890 437207097009211097484223 := by
  unfold tailWord_957890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8734279624933899858169781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23291412333157066288452749 8734279624933899858169781)
  ·
    refine ⟨818838714837553111703417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8734279624933899858169781 818838714837553111703417)
    ·
      refine ⟨614129036128164833777563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818838714837553111703417 614129036128164833777563)
      ·
        refine ⟨921193554192247250666345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614129036128164833777563 921193554192247250666345)
        ·
          refine ⟨690895165644185437999759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921193554192247250666345 690895165644185437999759)
          ·
            refine ⟨1036342748466278156999639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690895165644185437999759 1036342748466278156999639)
            ·
              refine ⟨1554514122699417235499459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036342748466278156999639 1554514122699417235499459)
              ·
                refine ⟨2331771184049125853249189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554514122699417235499459 2331771184049125853249189)
                ·
                  refine ⟨437207097009211097484223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2331771184049125853249189 437207097009211097484223)
                  ·
                    rfl

theorem cell20_957890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_957890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957890 prefixEnd_957890 := by exact prefixLift 957890
  have htrace : WordTrace (prefixWord ++ tailWord_957890) baseStart_957890 baseEnd_957890 := by
    simpa [prefixWord, tailWord_957890, baseEnd_957890] using wordTrace_append hprefix tailTrace_957890
  have hstable : (prefixWord ++ tailWord_957890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957890).length < 2 ^ (prefixWord ++ tailWord_957890).sum := by decide
  have hdescent : baseEnd_957890 < baseStart_957890 := by decide
  rcases family_descends (prefixWord ++ tailWord_957890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957895 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 3]
def baseStart_957895 : Nat := 118140960795 + 957895 * 2 ^ 59
def prefixEnd_957895 : Nat := 4983230072969 + 3 ^ 40 * 957895 * 2
def baseEnd_957895 : Nat := 437209379145453302317535

theorem tailTrace_957895 : CollatzResearch.WordTrace tailWord_957895 prefixEnd_957895 437209379145453302317535 := by
  unfold tailWord_957895
  simp only [CollatzResearch.WordTrace]
  refine ⟨34937300864717485286611139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23291533909811656857740759 34937300864717485286611139)
  ·
    refine ⟨52405951297076227929916709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34937300864717485286611139 52405951297076227929916709)
    ·
      refine ⟨9826115868201792736859383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52405951297076227929916709 9826115868201792736859383)
      ·
        refine ⟨14739173802302689105289075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9826115868201792736859383 14739173802302689105289075)
        ·
          refine ⟨22108760703454033657933613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14739173802302689105289075 22108760703454033657933613)
          ·
            refine ⟨8290785263795262621725105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22108760703454033657933613 8290785263795262621725105)
            ·
              refine ⟨6218088947846446966293829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8290785263795262621725105 6218088947846446966293829)
              ·
                refine ⟨1165891677721208806180093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6218088947846446966293829 1165891677721208806180093)
                ·
                  refine ⟨437209379145453302317535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165891677721208806180093 437209379145453302317535)
                  ·
                    rfl

theorem cell20_957895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 3].length) (baseStart_957895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957895 prefixEnd_957895 := by exact prefixLift 957895
  have htrace : WordTrace (prefixWord ++ tailWord_957895) baseStart_957895 baseEnd_957895 := by
    simpa [prefixWord, tailWord_957895, baseEnd_957895] using wordTrace_append hprefix tailTrace_957895
  have hstable : (prefixWord ++ tailWord_957895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957895).length < 2 ^ (prefixWord ++ tailWord_957895).sum := by decide
  have hdescent : baseEnd_957895 < baseStart_957895 := by decide
  rcases family_descends (prefixWord ++ tailWord_957895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957908 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 3]
def baseStart_957908 : Nat := 118140960795 + 957908 * 2 ^ 59
def prefixEnd_957908 : Nat := 4983230072969 + 3 ^ 40 * 957908 * 2
def baseEnd_957908 : Nat := 437215312699683034884149

theorem tailTrace_957908 : CollatzResearch.WordTrace tailWord_957908 prefixEnd_957908 437215312699683034884149 := by
  unfold tailWord_957908
  simp only [CollatzResearch.WordTrace]
  refine ⟨17468887506835194253417189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23291850009113592337889585 17468887506835194253417189)
  ·
    refine ⟨3275416407531598922515723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17468887506835194253417189 3275416407531598922515723)
    ·
      refine ⟨4913124611297398383773585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3275416407531598922515723 4913124611297398383773585)
      ·
        refine ⟨3684843458473048787830189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4913124611297398383773585 3684843458473048787830189)
        ·
          refine ⟨1381816296927393295436321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3684843458473048787830189 1381816296927393295436321)
          ·
            refine ⟨1036362222695544971577241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381816296927393295436321 1036362222695544971577241)
            ·
              refine ⟨777271667021658728682931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036362222695544971577241 777271667021658728682931)
              ·
                refine ⟨1165907500532488093024397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777271667021658728682931 1165907500532488093024397)
                ·
                  refine ⟨437215312699683034884149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165907500532488093024397 437215312699683034884149)
                  ·
                    rfl

theorem cell20_957908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_957908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957908 prefixEnd_957908 := by exact prefixLift 957908
  have htrace : WordTrace (prefixWord ++ tailWord_957908) baseStart_957908 baseEnd_957908 := by
    simpa [prefixWord, tailWord_957908, baseEnd_957908] using wordTrace_append hprefix tailTrace_957908
  have hstable : (prefixWord ++ tailWord_957908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957908).length < 2 ^ (prefixWord ++ tailWord_957908).sum := by decide
  have hdescent : baseEnd_957908 < baseStart_957908 := by decide
  rcases family_descends (prefixWord ++ tailWord_957908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957912 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 3]
def baseStart_957912 : Nat := 118140960795 + 957912 * 2 ^ 59
def prefixEnd_957912 : Nat := 4983230072969 + 3 ^ 40 * 957912 * 2
def baseEnd_957912 : Nat := 437217138408676798750799

theorem tailTrace_957912 : CollatzResearch.WordTrace tailWord_957912 prefixEnd_957912 437217138408676798750799 := by
  unfold tailWord_957912
  simp only [CollatzResearch.WordTrace]
  refine ⟨17468960452827948594989995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23291947270437264793319993 17468960452827948594989995)
  ·
    refine ⟨26203440679241922892484993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17468960452827948594989995 26203440679241922892484993)
    ·
      refine ⟨19652580509431442169363745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26203440679241922892484993 19652580509431442169363745)
      ·
        refine ⟨14739435382073581627022809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19652580509431442169363745 14739435382073581627022809)
        ·
          refine ⟨11054576536555186220267107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14739435382073581627022809 11054576536555186220267107)
          ·
            refine ⟨16581864804832779330400661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11054576536555186220267107 16581864804832779330400661)
            ·
              refine ⟨777274912726536531112531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16581864804832779330400661 777274912726536531112531)
              ·
                refine ⟨1165912369089804796668797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777274912726536531112531 1165912369089804796668797)
                ·
                  refine ⟨437217138408676798750799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165912369089804796668797 437217138408676798750799)
                  ·
                    rfl

theorem cell20_957912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_957912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957912 prefixEnd_957912 := by exact prefixLift 957912
  have htrace : WordTrace (prefixWord ++ tailWord_957912) baseStart_957912 baseEnd_957912 := by
    simpa [prefixWord, tailWord_957912, baseEnd_957912] using wordTrace_append hprefix tailTrace_957912
  have hstable : (prefixWord ++ tailWord_957912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957912).length < 2 ^ (prefixWord ++ tailWord_957912).sum := by decide
  have hdescent : baseEnd_957912 < baseStart_957912 := by decide
  rcases family_descends (prefixWord ++ tailWord_957912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957971 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 3]
def baseStart_957971 : Nat := 118140960795 + 957971 * 2 ^ 59
def prefixEnd_957971 : Nat := 4983230072969 + 3 ^ 40 * 957971 * 2
def baseEnd_957971 : Nat := 437244067616334815783891

theorem tailTrace_957971 : CollatzResearch.WordTrace tailWord_957971 prefixEnd_957971 437244067616334815783891 := by
  unfold tailWord_957971
  simp only [CollatzResearch.WordTrace]
  refine ⟨34940072812442150266377767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23293381874961433510918511 34940072812442150266377767)
  ·
    refine ⟨52410109218663225399566651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34940072812442150266377767 52410109218663225399566651)
    ·
      refine ⟨78615163827994838099349977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52410109218663225399566651 78615163827994838099349977)
      ·
        refine ⟨58961372870996128574512483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78615163827994838099349977 58961372870996128574512483)
        ·
          refine ⟨88442059306494192861768725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58961372870996128574512483 88442059306494192861768725)
          ·
            refine ⟨4145721529991915290395409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88442059306494192861768725 4145721529991915290395409)
            ·
              refine ⟨3109291147493936467796557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4145721529991915290395409 3109291147493936467796557)
              ·
                refine ⟨1165984180310226175423709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3109291147493936467796557 1165984180310226175423709)
                ·
                  refine ⟨437244067616334815783891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165984180310226175423709 437244067616334815783891)
                  ·
                    rfl

theorem cell20_957971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 3].length) (baseStart_957971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_957971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_957971 prefixEnd_957971 := by exact prefixLift 957971
  have htrace : WordTrace (prefixWord ++ tailWord_957971) baseStart_957971 baseEnd_957971 := by
    simpa [prefixWord, tailWord_957971, baseEnd_957971] using wordTrace_append hprefix tailTrace_957971
  have hstable : (prefixWord ++ tailWord_957971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957971).length < 2 ^ (prefixWord ++ tailWord_957971).sum := by decide
  have hdescent : baseEnd_957971 < baseStart_957971 := by decide
  rcases family_descends (prefixWord ++ tailWord_957971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958009 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 5]
def baseStart_958009 : Nat := 118140960795 + 958009 * 2 ^ 59
def prefixEnd_958009 : Nat := 4983230072969 + 3 ^ 40 * 958009 * 2
def baseEnd_958009 : Nat := 437261411851775572517069

theorem tailTrace_958009 : CollatzResearch.WordTrace tailWord_958009 prefixEnd_958009 437261411851775572517069 := by
  unfold tailWord_958009
  simp only [CollatzResearch.WordTrace]
  refine ⟨34941458786304482756261081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23294305857536321837507387 34941458786304482756261081)
  ·
    refine ⟨26206094089728362067195811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34941458786304482756261081 26206094089728362067195811)
    ·
      refine ⟨39309141134592543100793717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26206094089728362067195811 39309141134592543100793717)
      ·
        refine ⟨3685231981368050915699411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39309141134592543100793717 3685231981368050915699411)
        ·
          refine ⟨5527847972052076373549117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685231981368050915699411 5527847972052076373549117)
          ·
            refine ⟨2072942989519528640080919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5527847972052076373549117 2072942989519528640080919)
            ·
              refine ⟨3109414484279292960121379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072942989519528640080919 3109414484279292960121379)
              ·
                refine ⟨4664121726418939440182069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109414484279292960121379 4664121726418939440182069)
                ·
                  refine ⟨437261411851775572517069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4664121726418939440182069 437261411851775572517069)
                  ·
                    rfl

theorem cell20_958009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_958009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958009 prefixEnd_958009 := by exact prefixLift 958009
  have htrace : WordTrace (prefixWord ++ tailWord_958009) baseStart_958009 baseEnd_958009 := by
    simpa [prefixWord, tailWord_958009, baseEnd_958009] using wordTrace_append hprefix tailTrace_958009
  have hstable : (prefixWord ++ tailWord_958009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958009).length < 2 ^ (prefixWord ++ tailWord_958009).sum := by decide
  have hdescent : baseEnd_958009 < baseStart_958009 := by decide
  rcases family_descends (prefixWord ++ tailWord_958009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958026 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_958026 : Nat := 118140960795 + 958026 * 2 ^ 59
def prefixEnd_958026 : Nat := 4983230072969 + 3 ^ 40 * 958026 * 2
def baseEnd_958026 : Nat := 437269171114999068950333

theorem tailTrace_958026 : CollatzResearch.WordTrace tailWord_958026 prefixEnd_958026 437269171114999068950333 := by
  unfold tailWord_958026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735519706810723664907483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23294719218161929773086621 8735519706810723664907483)
  ·
    refine ⟨13103279560216085497361225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8735519706810723664907483 13103279560216085497361225)
    ·
      refine ⟨9827459670162064123020919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13103279560216085497361225 9827459670162064123020919)
      ·
        refine ⟨14741189505243096184531379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827459670162064123020919 14741189505243096184531379)
        ·
          refine ⟨22111784257864644276797069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14741189505243096184531379 22111784257864644276797069)
          ·
            refine ⟨8291919096699241603798901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22111784257864644276797069 8291919096699241603798901)
            ·
              refine ⟨777367415315553900356147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8291919096699241603798901 777367415315553900356147)
              ·
                refine ⟨1166051122973330850534221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777367415315553900356147 1166051122973330850534221)
                ·
                  refine ⟨437269171114999068950333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166051122973330850534221 437269171114999068950333)
                  ·
                    rfl

theorem cell20_958026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_958026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958026 prefixEnd_958026 := by exact prefixLift 958026
  have htrace : WordTrace (prefixWord ++ tailWord_958026) baseStart_958026 baseEnd_958026 := by
    simpa [prefixWord, tailWord_958026, baseEnd_958026] using wordTrace_append hprefix tailTrace_958026
  have hstable : (prefixWord ++ tailWord_958026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958026).length < 2 ^ (prefixWord ++ tailWord_958026).sum := by decide
  have hdescent : baseEnd_958026 < baseStart_958026 := by decide
  rcases family_descends (prefixWord ++ tailWord_958026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958081 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 3]
def baseStart_958081 : Nat := 118140960795 + 958081 * 2 ^ 59
def prefixEnd_958081 : Nat := 4983230072969 + 3 ^ 40 * 958081 * 2
def baseEnd_958081 : Nat := 437294274613663322116775

theorem tailTrace_958081 : CollatzResearch.WordTrace tailWord_958081 prefixEnd_958081 437294274613663322116775 := by
  unfold tailWord_958081
  simp only [CollatzResearch.WordTrace]
  refine ⟨34944084842043639052882097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23296056561362426035254731 34944084842043639052882097)
  ·
    refine ⟨26208063631532729289661573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34944084842043639052882097 26208063631532729289661573)
    ·
      refine ⟨4914011930912386741811545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26208063631532729289661573 4914011930912386741811545)
      ·
        refine ⟨3685508948184290056358659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4914011930912386741811545 3685508948184290056358659)
        ·
          refine ⟨5528263422276435084537989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685508948184290056358659 5528263422276435084537989)
          ·
            refine ⟨1036549391676831578350873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5528263422276435084537989 1036549391676831578350873)
            ·
              refine ⟨777412043757623683763155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036549391676831578350873 777412043757623683763155)
              ·
                refine ⟨1166118065636435525644733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777412043757623683763155 1166118065636435525644733)
                ·
                  refine ⟨437294274613663322116775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166118065636435525644733 437294274613663322116775)
                  ·
                    rfl

theorem cell20_958081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_958081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958081 prefixEnd_958081 := by exact prefixLift 958081
  have htrace : WordTrace (prefixWord ++ tailWord_958081) baseStart_958081 baseEnd_958081 := by
    simpa [prefixWord, tailWord_958081, baseEnd_958081] using wordTrace_append hprefix tailTrace_958081
  have hstable : (prefixWord ++ tailWord_958081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958081).length < 2 ^ (prefixWord ++ tailWord_958081).sum := by decide
  have hdescent : baseEnd_958081 < baseStart_958081 := by decide
  rcases family_descends (prefixWord ++ tailWord_958081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958085 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 3]
def baseStart_958085 : Nat := 118140960795 + 958085 * 2 ^ 59
def prefixEnd_958085 : Nat := 4983230072969 + 3 ^ 40 * 958085 * 2
def baseEnd_958085 : Nat := 437296100322657085983425

theorem tailTrace_958085 : CollatzResearch.WordTrace tailWord_958085 prefixEnd_958085 437296100322657085983425 := by
  unfold tailWord_958085
  simp only [CollatzResearch.WordTrace]
  refine ⟨34944230734029147736027709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23296153822686098490685139 34944230734029147736027709)
  ·
    refine ⟨13104086525260930401010391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34944230734029147736027709 13104086525260930401010391)
    ·
      refine ⟨19656129787891395601515587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13104086525260930401010391 19656129787891395601515587)
      ·
        refine ⟨29484194681837093402273381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19656129787891395601515587 29484194681837093402273381)
        ·
          refine ⟨5528286502844455012926259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29484194681837093402273381 5528286502844455012926259)
          ·
            refine ⟨8292429754266682519389389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528286502844455012926259 8292429754266682519389389)
            ·
              refine ⟨3109661157850005944771021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8292429754266682519389389 3109661157850005944771021)
              ·
                refine ⟨1166122934193752229289133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3109661157850005944771021 1166122934193752229289133)
                ·
                  refine ⟨437296100322657085983425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166122934193752229289133 437296100322657085983425)
                  ·
                    rfl

theorem cell20_958085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_958085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958085 prefixEnd_958085 := by exact prefixLift 958085
  have htrace : WordTrace (prefixWord ++ tailWord_958085) baseStart_958085 baseEnd_958085 := by
    simpa [prefixWord, tailWord_958085, baseEnd_958085] using wordTrace_append hprefix tailTrace_958085
  have hstable : (prefixWord ++ tailWord_958085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958085).length < 2 ^ (prefixWord ++ tailWord_958085).sum := by decide
  have hdescent : baseEnd_958085 < baseStart_958085 := by decide
  rcases family_descends (prefixWord ++ tailWord_958085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958109 : List Nat := [1, 4, 2, 1, 1, 1, 1, 7, 2]
def baseStart_958109 : Nat := 118140960795 + 958109 * 2 ^ 59
def prefixEnd_958109 : Nat := 4983230072969 + 3 ^ 40 * 958109 * 2
def baseEnd_958109 : Nat := 437307054576619669183327

theorem tailTrace_958109 : CollatzResearch.WordTrace tailWord_958109 prefixEnd_958109 437307054576619669183327 := by
  unfold tailWord_958109
  simp only [CollatzResearch.WordTrace]
  refine ⟨34945106085942199834901381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23296737390628133223267587 34945106085942199834901381)
  ·
    refine ⟨6552207391114162469044009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34945106085942199834901381 6552207391114162469044009)
    ·
      refine ⟨4914155543335621851783007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6552207391114162469044009 4914155543335621851783007)
      ·
        refine ⟨7371233315003432777674511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4914155543335621851783007 7371233315003432777674511)
        ·
          refine ⟨11056849972505149166511767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371233315003432777674511 11056849972505149166511767)
          ·
            refine ⟨16585274958757723749767651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11056849972505149166511767 16585274958757723749767651)
            ·
              refine ⟨24877912438136585624651477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16585274958757723749767651 24877912438136585624651477)
              ·
                refine ⟨583076072768826225577769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24877912438136585624651477 583076072768826225577769)
                ·
                  refine ⟨437307054576619669183327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583076072768826225577769 437307054576619669183327)
                  ·
                    rfl

theorem cell20_958109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_958109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958109 prefixEnd_958109 := by exact prefixLift 958109
  have htrace : WordTrace (prefixWord ++ tailWord_958109) baseStart_958109 baseEnd_958109 := by
    simpa [prefixWord, tailWord_958109, baseEnd_958109] using wordTrace_append hprefix tailTrace_958109
  have hstable : (prefixWord ++ tailWord_958109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958109).length < 2 ^ (prefixWord ++ tailWord_958109).sum := by decide
  have hdescent : baseEnd_958109 < baseStart_958109 := by decide
  rcases family_descends (prefixWord ++ tailWord_958109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958133 : List Nat := [1, 3, 3, 3, 2, 2, 1, 5]
def baseStart_958133 : Nat := 118140960795 + 958133 * 2 ^ 59
def prefixEnd_958133 : Nat := 4983230072969 + 3 ^ 40 * 958133 * 2
def baseEnd_958133 : Nat := 145772669610194084127743

theorem tailTrace_958133 : CollatzResearch.WordTrace tailWord_958133 prefixEnd_958133 145772669610194084127743 := by
  unfold tailWord_958133
  simp only [CollatzResearch.WordTrace]
  refine ⟨34945981437855251933775053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23297320958570167955850035 34945981437855251933775053)
  ·
    refine ⟨13104743039195719475165645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34945981437855251933775053 13104743039195719475165645)
    ·
      refine ⟨4914278639698394803187117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13104743039195719475165645 4914278639698394803187117)
      ·
        refine ⟨1842854489886898051195169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4914278639698394803187117 1842854489886898051195169)
        ·
          refine ⟨1382140867415173538396377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1842854489886898051195169 1382140867415173538396377)
          ·
            refine ⟨1036605650561380153797283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1382140867415173538396377 1036605650561380153797283)
            ·
              refine ⟨1554908475842070230695925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036605650561380153797283 1554908475842070230695925)
              ·
                refine ⟨145772669610194084127743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1554908475842070230695925 145772669610194084127743)
                ·
                  rfl

theorem cell20_958133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 5].length) (baseStart_958133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958133 prefixEnd_958133 := by exact prefixLift 958133
  have htrace : WordTrace (prefixWord ++ tailWord_958133) baseStart_958133 baseEnd_958133 := by
    simpa [prefixWord, tailWord_958133, baseEnd_958133] using wordTrace_append hprefix tailTrace_958133
  have hstable : (prefixWord ++ tailWord_958133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958133).length < 2 ^ (prefixWord ++ tailWord_958133).sum := by decide
  have hdescent : baseEnd_958133 < baseStart_958133 := by decide
  rcases family_descends (prefixWord ++ tailWord_958133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958137 : List Nat := [1, 2, 1, 4, 1, 1, 5, 5]
def baseStart_958137 : Nat := 118140960795 + 958137 * 2 ^ 59
def prefixEnd_958137 : Nat := 4983230072969 + 3 ^ 40 * 958137 * 2
def baseEnd_958137 : Nat := 145773278179858672083293

theorem tailTrace_958137 : CollatzResearch.WordTrace tailWord_958137 prefixEnd_958137 145773278179858672083293 := by
  unfold tailWord_958137
  simp only [CollatzResearch.WordTrace]
  refine ⟨34946127329840760616920665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23297418219893840411280443 34946127329840760616920665)
  ·
    refine ⟨26209595497380570462690499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34946127329840760616920665 26209595497380570462690499)
    ·
      refine ⟨39314393246070855694035749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26209595497380570462690499 39314393246070855694035749)
      ·
        refine ⟨7371448733638285442631703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39314393246070855694035749 7371448733638285442631703)
        ·
          refine ⟨11057173100457428163947555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371448733638285442631703 11057173100457428163947555)
          ·
            refine ⟨16585759650686142245921333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11057173100457428163947555 16585759650686142245921333)
            ·
              refine ⟨1554914967251825835555125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16585759650686142245921333 1554914967251825835555125)
              ·
                refine ⟨145773278179858672083293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1554914967251825835555125 145773278179858672083293)
                ·
                  rfl

theorem cell20_958137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_958137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958137 prefixEnd_958137 := by exact prefixLift 958137
  have htrace : WordTrace (prefixWord ++ tailWord_958137) baseStart_958137 baseEnd_958137 := by
    simpa [prefixWord, tailWord_958137, baseEnd_958137] using wordTrace_append hprefix tailTrace_958137
  have hstable : (prefixWord ++ tailWord_958137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958137).length < 2 ^ (prefixWord ++ tailWord_958137).sum := by decide
  have hdescent : baseEnd_958137 < baseStart_958137 := by decide
  rcases family_descends (prefixWord ++ tailWord_958137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958164 : List Nat := [2, 4, 1, 3, 1, 1, 1, 5, 2]
def baseStart_958164 : Nat := 118140960795 + 958164 * 2 ^ 59
def prefixEnd_958164 : Nat := 4983230072969 + 3 ^ 40 * 958164 * 2
def baseEnd_958164 : Nat := 437332158075283922349769

theorem tailTrace_958164 : CollatzResearch.WordTrace tailWord_958164 prefixEnd_958164 437332158075283922349769 := by
  unfold tailWord_958164
  simp only [CollatzResearch.WordTrace]
  refine ⟨17473556050371472114076773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23298074733828629485435697 17473556050371472114076773)
  ·
    refine ⟨3276291759444651021389395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17473556050371472114076773 3276291759444651021389395)
    ·
      refine ⟨4914437639166976532084093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3276291759444651021389395 4914437639166976532084093)
      ·
        refine ⟨1842914114687616199531535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4914437639166976532084093 1842914114687616199531535)
        ·
          refine ⟨2764371172031424299297303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1842914114687616199531535 2764371172031424299297303)
          ·
            refine ⟨4146556758047136448945955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764371172031424299297303 4146556758047136448945955)
            ·
              refine ⟨6219835137070704673418933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146556758047136448945955 6219835137070704673418933)
              ·
                refine ⟨583109544100378563133025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6219835137070704673418933 583109544100378563133025)
                ·
                  refine ⟨437332158075283922349769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583109544100378563133025 437332158075283922349769)
                  ·
                    rfl

theorem cell20_958164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_958164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958164 prefixEnd_958164 := by exact prefixLift 958164
  have htrace : WordTrace (prefixWord ++ tailWord_958164) baseStart_958164 baseEnd_958164 := by
    simpa [prefixWord, tailWord_958164, baseEnd_958164] using wordTrace_append hprefix tailTrace_958164
  have hstable : (prefixWord ++ tailWord_958164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958164).length < 2 ^ (prefixWord ++ tailWord_958164).sum := by decide
  have hdescent : baseEnd_958164 < baseStart_958164 := by decide
  rcases family_descends (prefixWord ++ tailWord_958164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958220 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_958220 : Nat := 118140960795 + 958220 * 2 ^ 59
def prefixEnd_958220 : Nat := 4983230072969 + 3 ^ 40 * 958220 * 2
def baseEnd_958220 : Nat := 437357718001196616482873

theorem tailTrace_958220 : CollatzResearch.WordTrace tailWord_958220 prefixEnd_958220 437357718001196616482873 := by
  unfold tailWord_958220
  simp only [CollatzResearch.WordTrace]
  refine ⟨17474577294270032896096057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23299436392360043861461409 17474577294270032896096057)
  ·
    refine ⟨13105932970702524672072043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17474577294270032896096057 13105932970702524672072043)
    ·
      refine ⟨19658899456053787008108065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13105932970702524672072043 19658899456053787008108065)
      ·
        refine ⟨14744174592040340256081049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19658899456053787008108065 14744174592040340256081049)
        ·
          refine ⟨11058130944030255192060787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14744174592040340256081049 11058130944030255192060787)
          ·
            refine ⟨16587196416045382788091181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058130944030255192060787 16587196416045382788091181)
            ·
              refine ⟨6220198656017018545534193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16587196416045382788091181 6220198656017018545534193)
              ·
                refine ⟨4665148992012763909150645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6220198656017018545534193 4665148992012763909150645)
                ·
                  refine ⟨437357718001196616482873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4665148992012763909150645 437357718001196616482873)
                  ·
                    rfl

theorem cell20_958220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_958220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958220 prefixEnd_958220 := by exact prefixLift 958220
  have htrace : WordTrace (prefixWord ++ tailWord_958220) baseStart_958220 baseEnd_958220 := by
    simpa [prefixWord, tailWord_958220, baseEnd_958220] using wordTrace_append hprefix tailTrace_958220
  have hstable : (prefixWord ++ tailWord_958220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958220).length < 2 ^ (prefixWord ++ tailWord_958220).sum := by decide
  have hdescent : baseEnd_958220 < baseStart_958220 := by decide
  rcases family_descends (prefixWord ++ tailWord_958220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958240 : List Nat := [2, 1, 1, 5, 1, 1, 5, 2, 2]
def baseStart_958240 : Nat := 118140960795 + 958240 * 2 ^ 59
def prefixEnd_958240 : Nat := 4983230072969 + 3 ^ 40 * 958240 * 2
def baseEnd_958240 : Nat := 437366846546165435816125

theorem tailTrace_958240 : CollatzResearch.WordTrace tailWord_958240 prefixEnd_958240 437366846546165435816125 := by
  unfold tailWord_958240
  simp only [CollatzResearch.WordTrace]
  refine ⟨17474942024233804603960087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23299922698978406138613449 17474942024233804603960087)
  ·
    refine ⟨26212413036350706905940131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17474942024233804603960087 26212413036350706905940131)
    ·
      refine ⟨39318619554526060358910197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26212413036350706905940131 39318619554526060358910197)
      ·
        refine ⟨3686120583236818158647831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39318619554526060358910197 3686120583236818158647831)
        ·
          refine ⟨5529180874855227237971747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3686120583236818158647831 5529180874855227237971747)
          ·
            refine ⟨8293771312282840856957621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5529180874855227237971747 8293771312282840856957621)
            ·
              refine ⟨777541060526516330339777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8293771312282840856957621 777541060526516330339777)
              ·
                refine ⟨583155795394887247754833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777541060526516330339777 583155795394887247754833)
                ·
                  refine ⟨437366846546165435816125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583155795394887247754833 437366846546165435816125)
                  ·
                    rfl

theorem cell20_958240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_958240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958240 prefixEnd_958240 := by exact prefixLift 958240
  have htrace : WordTrace (prefixWord ++ tailWord_958240) baseStart_958240 baseEnd_958240 := by
    simpa [prefixWord, tailWord_958240, baseEnd_958240] using wordTrace_append hprefix tailTrace_958240
  have hstable : (prefixWord ++ tailWord_958240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958240).length < 2 ^ (prefixWord ++ tailWord_958240).sum := by decide
  have hdescent : baseEnd_958240 < baseStart_958240 := by decide
  rcases family_descends (prefixWord ++ tailWord_958240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958292 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 3]
def baseStart_958292 : Nat := 118140960795 + 958292 * 2 ^ 59
def prefixEnd_958292 : Nat := 4983230072969 + 3 ^ 40 * 958292 * 2
def baseEnd_958292 : Nat := 437390580763084366082579

theorem tailTrace_958292 : CollatzResearch.WordTrace tailWord_958292 prefixEnd_958292 437390580763084366082579 := by
  unfold tailWord_958292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17475890322139611044406565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23301187096186148059208753 17475890322139611044406565)
  ·
    refine ⟨3276729435401177070826231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17475890322139611044406565 3276729435401177070826231)
    ·
      refine ⟨4915094153101765606239347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3276729435401177070826231 4915094153101765606239347)
      ·
        refine ⟨7372641229652648409359021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4915094153101765606239347 7372641229652648409359021)
        ·
          refine ⟨2764740461119743153509633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7372641229652648409359021 2764740461119743153509633)
          ·
            refine ⟨2073555345839807365132225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2764740461119743153509633 2073555345839807365132225)
            ·
              refine ⟨1555166509379855523849169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073555345839807365132225 1555166509379855523849169)
              ·
                refine ⟨1166374882034891642886877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555166509379855523849169 1166374882034891642886877)
                ·
                  refine ⟨437390580763084366082579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166374882034891642886877 437390580763084366082579)
                  ·
                    rfl

theorem cell20_958292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_958292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958292 prefixEnd_958292 := by exact prefixLift 958292
  have htrace : WordTrace (prefixWord ++ tailWord_958292) baseStart_958292 baseEnd_958292 := by
    simpa [prefixWord, tailWord_958292, baseEnd_958292] using wordTrace_append hprefix tailTrace_958292
  have hstable : (prefixWord ++ tailWord_958292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958292).length < 2 ^ (prefixWord ++ tailWord_958292).sum := by decide
  have hdescent : baseEnd_958292 < baseStart_958292 := by decide
  rcases family_descends (prefixWord ++ tailWord_958292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958295 : List Nat := [1, 1, 3, 2, 5, 2, 2, 2, 2]
def baseStart_958295 : Nat := 118140960795 + 958295 * 2 ^ 59
def prefixEnd_958295 : Nat := 4983230072969 + 3 ^ 40 * 958295 * 2
def baseEnd_958295 : Nat := 437391950044829688982567

theorem tailTrace_958295 : CollatzResearch.WordTrace tailWord_958295 prefixEnd_958295 437391950044829688982567 := by
  unfold tailWord_958295
  simp only [CollatzResearch.WordTrace]
  refine ⟨34951890063268353601172339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23301260042178902400781559 34951890063268353601172339)
  ·
    refine ⟨52427835094902530401758509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34951890063268353601172339 52427835094902530401758509)
    ·
      refine ⟨19660438160588448900659441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52427835094902530401758509 19660438160588448900659441)
      ·
        refine ⟨14745328620441336675494581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19660438160588448900659441 14745328620441336675494581)
        ·
          refine ⟨1382374558166375313327617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14745328620441336675494581 1382374558166375313327617)
          ·
            refine ⟨1036780918624781484995713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1382374558166375313327617 1036780918624781484995713)
            ·
              refine ⟨777585688968586113746785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036780918624781484995713 777585688968586113746785)
              ·
                refine ⟨583189266726439585310089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777585688968586113746785 583189266726439585310089)
                ·
                  refine ⟨437391950044829688982567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583189266726439585310089 437391950044829688982567)
                  ·
                    rfl

theorem cell20_958295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 2].length) (baseStart_958295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958295 prefixEnd_958295 := by exact prefixLift 958295
  have htrace : WordTrace (prefixWord ++ tailWord_958295) baseStart_958295 baseEnd_958295 := by
    simpa [prefixWord, tailWord_958295, baseEnd_958295] using wordTrace_append hprefix tailTrace_958295
  have hstable : (prefixWord ++ tailWord_958295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958295).length < 2 ^ (prefixWord ++ tailWord_958295).sum := by decide
  have hdescent : baseEnd_958295 < baseStart_958295 := by decide
  rcases family_descends (prefixWord ++ tailWord_958295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958306 : List Nat := [3, 3, 2, 1, 2, 1, 3, 5]
def baseStart_958306 : Nat := 118140960795 + 958306 * 2 ^ 59
def prefixEnd_958306 : Nat := 4983230072969 + 3 ^ 40 * 958306 * 2
def baseEnd_958306 : Nat := 145798990248187513205285

theorem tailTrace_958306 : CollatzResearch.WordTrace tailWord_958306 prefixEnd_958306 145798990248187513205285 := by
  unfold tailWord_958306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8738072816557125619955693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23301527510819001653215181 8738072816557125619955693)
  ·
    refine ⟨3276777306208922107483385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8738072816557125619955693 3276777306208922107483385)
    ·
      refine ⟨2457582979656691580612539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3276777306208922107483385 2457582979656691580612539)
      ·
        refine ⟨3686374469485037370918809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457582979656691580612539 3686374469485037370918809)
        ·
          refine ⟨2764780852113778028189107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3686374469485037370918809 2764780852113778028189107)
          ·
            refine ⟨4147171278170667042283661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764780852113778028189107 4147171278170667042283661)
            ·
              refine ⟨1555189229314000140856373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4147171278170667042283661 1555189229314000140856373)
              ·
                refine ⟨145798990248187513205285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1555189229314000140856373 145798990248187513205285)
                ·
                  rfl

theorem cell20_958306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_958306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958306 prefixEnd_958306 := by exact prefixLift 958306
  have htrace : WordTrace (prefixWord ++ tailWord_958306) baseStart_958306 baseEnd_958306 := by
    simpa [prefixWord, tailWord_958306, baseEnd_958306] using wordTrace_append hprefix tailTrace_958306
  have hstable : (prefixWord ++ tailWord_958306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958306).length < 2 ^ (prefixWord ++ tailWord_958306).sum := by decide
  have hdescent : baseEnd_958306 < baseStart_958306 := by decide
  rcases family_descends (prefixWord ++ tailWord_958306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958341 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_958341 : Nat := 118140960795 + 958341 * 2 ^ 59
def prefixEnd_958341 : Nat := 4983230072969 + 3 ^ 40 * 958341 * 2
def baseEnd_958341 : Nat := 437412945698257973449045

theorem tailTrace_958341 : CollatzResearch.WordTrace tailWord_958341 prefixEnd_958341 437412945698257973449045 := by
  unfold tailWord_958341
  simp only [CollatzResearch.WordTrace]
  refine ⟨34953567821101703457346877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23302378547401135638231251 34953567821101703457346877)
  ·
    refine ⟨13107587932913138796505079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34953567821101703457346877 13107587932913138796505079)
    ·
      refine ⟨19661381899369708194757619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13107587932913138796505079 19661381899369708194757619)
      ·
        refine ⟨29492072849054562292136429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19661381899369708194757619 29492072849054562292136429)
        ·
          refine ⟨11059527318395460859551161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29492072849054562292136429 11059527318395460859551161)
          ·
            refine ⟨8294645488796595644663371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11059527318395460859551161 8294645488796595644663371)
            ·
              refine ⟨12441968233194893466995057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8294645488796595644663371 12441968233194893466995057)
              ·
                refine ⟨9331476174896170100246293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12441968233194893466995057 9331476174896170100246293)
                ·
                  refine ⟨437412945698257973449045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9331476174896170100246293 437412945698257973449045)
                  ·
                    rfl

theorem cell20_958341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_958341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958341 prefixEnd_958341 := by exact prefixLift 958341
  have htrace : WordTrace (prefixWord ++ tailWord_958341) baseStart_958341 baseEnd_958341 := by
    simpa [prefixWord, tailWord_958341, baseEnd_958341] using wordTrace_append hprefix tailTrace_958341
  have hstable : (prefixWord ++ tailWord_958341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958341).length < 2 ^ (prefixWord ++ tailWord_958341).sum := by decide
  have hdescent : baseEnd_958341 < baseStart_958341 := by decide
  rcases family_descends (prefixWord ++ tailWord_958341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958354 : List Nat := [3, 2, 3, 2, 1, 1, 2, 4, 2]
def baseStart_958354 : Nat := 118140960795 + 958354 * 2 ^ 59
def prefixEnd_958354 : Nat := 4983230072969 + 3 ^ 40 * 958354 * 2
def baseEnd_958354 : Nat := 437418879252487706015659

theorem tailTrace_958354 : CollatzResearch.WordTrace tailWord_958354 prefixEnd_958354 437418879252487706015659 := by
  unfold tailWord_958354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8738510492513651669392529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23302694646703071118380077 8738510492513651669392529)
  ·
    refine ⟨6553882869385238752044397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8738510492513651669392529 6553882869385238752044397)
    ·
      refine ⟨2457706076019464532016649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6553882869385238752044397 2457706076019464532016649)
      ·
        refine ⟨1843279557014598399012487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2457706076019464532016649 1843279557014598399012487)
        ·
          refine ⟨2764919335521897598518731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843279557014598399012487 2764919335521897598518731)
          ·
            refine ⟨4147379003282846397778097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764919335521897598518731 4147379003282846397778097)
            ·
              refine ⟨3110534252462134798333573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4147379003282846397778097 3110534252462134798333573)
              ·
                refine ⟨583225172336650274687545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3110534252462134798333573 583225172336650274687545)
                ·
                  refine ⟨437418879252487706015659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583225172336650274687545 437418879252487706015659)
                  ·
                    rfl

theorem cell20_958354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_958354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958354 prefixEnd_958354 := by exact prefixLift 958354
  have htrace : WordTrace (prefixWord ++ tailWord_958354) baseStart_958354 baseEnd_958354 := by
    simpa [prefixWord, tailWord_958354, baseEnd_958354] using wordTrace_append hprefix tailTrace_958354
  have hstable : (prefixWord ++ tailWord_958354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958354).length < 2 ^ (prefixWord ++ tailWord_958354).sum := by decide
  have hdescent : baseEnd_958354 < baseStart_958354 := by decide
  rcases family_descends (prefixWord ++ tailWord_958354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958388 : List Nat := [2, 5, 2, 1, 2, 2, 1, 3, 2]
def baseStart_958388 : Nat := 118140960795 + 958388 * 2 ^ 59
def prefixEnd_958388 : Nat := 4983230072969 + 3 ^ 40 * 958388 * 2
def baseEnd_958388 : Nat := 437434397778934698882187

theorem tailTrace_958388 : CollatzResearch.WordTrace tailWord_958388 prefixEnd_958388 437434397778934698882187 := by
  unfold tailWord_958388
  simp only [CollatzResearch.WordTrace]
  refine ⟨17477641025965715242153909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23303521367954286989538545 17477641025965715242153909)
  ·
    refine ⟨1638528846184285803951929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17477641025965715242153909 1638528846184285803951929)
    ·
      refine ⟨1228896634638214352963947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1638528846184285803951929 1228896634638214352963947)
      ·
        refine ⟨1843344951957321529445921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1228896634638214352963947 1843344951957321529445921)
        ·
          refine ⟨1382508713967991147084441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1843344951957321529445921 1382508713967991147084441)
          ·
            refine ⟨1036881535475993360313331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1382508713967991147084441 1036881535475993360313331)
            ·
              refine ⟨1555322303213990040469997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036881535475993360313331 1555322303213990040469997)
              ·
                refine ⟨583245863705246265176249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1555322303213990040469997 583245863705246265176249)
                ·
                  refine ⟨437434397778934698882187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583245863705246265176249 437434397778934698882187)
                  ·
                    rfl

theorem cell20_958388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_958388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958388 prefixEnd_958388 := by exact prefixLift 958388
  have htrace : WordTrace (prefixWord ++ tailWord_958388) baseStart_958388 baseEnd_958388 := by
    simpa [prefixWord, tailWord_958388, baseEnd_958388] using wordTrace_append hprefix tailTrace_958388
  have hstable : (prefixWord ++ tailWord_958388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958388).length < 2 ^ (prefixWord ++ tailWord_958388).sum := by decide
  have hdescent : baseEnd_958388 < baseStart_958388 := by decide
  rcases family_descends (prefixWord ++ tailWord_958388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958410 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_958410 : Nat := 118140960795 + 958410 * 2 ^ 59
def prefixEnd_958410 : Nat := 4983230072969 + 3 ^ 40 * 958410 * 2
def baseEnd_958410 : Nat := 437444439178400400148763

theorem tailTrace_958410 : CollatzResearch.WordTrace tailWord_958410 prefixEnd_958410 437444439178400400148763 := by
  unfold tailWord_958410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8739021114462932060402171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23304056305234485494405789 8739021114462932060402171)
  ·
    refine ⟨13108531671694398090603257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8739021114462932060402171 13108531671694398090603257)
    ·
      refine ⟨9831398753770798567952443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13108531671694398090603257 9831398753770798567952443)
      ·
        refine ⟨14747098130656197851928665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9831398753770798567952443 14747098130656197851928665)
        ·
          refine ⟨11060323597992148388946499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14747098130656197851928665 11060323597992148388946499)
          ·
            refine ⟨16590485396988222583419749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11060323597992148388946499 16590485396988222583419749)
            ·
              refine ⟨3110716011935291734391203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16590485396988222583419749 3110716011935291734391203)
              ·
                refine ⟨4666074017902937601586805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110716011935291734391203 4666074017902937601586805)
                ·
                  refine ⟨437444439178400400148763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4666074017902937601586805 437444439178400400148763)
                  ·
                    rfl

theorem cell20_958410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_958410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958410 prefixEnd_958410 := by exact prefixLift 958410
  have htrace : WordTrace (prefixWord ++ tailWord_958410) baseStart_958410 baseEnd_958410 := by
    simpa [prefixWord, tailWord_958410, baseEnd_958410] using wordTrace_append hprefix tailTrace_958410
  have hstable : (prefixWord ++ tailWord_958410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958410).length < 2 ^ (prefixWord ++ tailWord_958410).sum := by decide
  have hdescent : baseEnd_958410 < baseStart_958410 := by decide
  rcases family_descends (prefixWord ++ tailWord_958410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958417 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_958417 : Nat := 118140960795 + 958417 * 2 ^ 59
def prefixEnd_958417 : Nat := 4983230072969 + 3 ^ 40 * 958417 * 2
def baseEnd_958417 : Nat := 437447634169139486915401

theorem tailTrace_958417 : CollatzResearch.WordTrace tailWord_958417 prefixEnd_958417 437447634169139486915401 := by
  unfold tailWord_958417
  simp only [CollatzResearch.WordTrace]
  refine ⟨34956339768826368437113505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23304226512550912291409003 34956339768826368437113505)
  ·
    refine ⟨26217254826619776327835129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34956339768826368437113505 26217254826619776327835129)
    ·
      refine ⟨19662941119964832245876347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26217254826619776327835129 19662941119964832245876347)
      ·
        refine ⟨29494411679947248368814521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19662941119964832245876347 29494411679947248368814521)
        ·
          refine ⟨22120808759960436276610891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29494411679947248368814521 22120808759960436276610891)
          ·
            refine ⟨33181213139940654414916337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22120808759960436276610891 33181213139940654414916337)
            ·
              refine ⟨24885909854955490811187253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33181213139940654414916337 24885909854955490811187253)
              ·
                refine ⟨2333054048902077263548805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24885909854955490811187253 2333054048902077263548805)
                ·
                  refine ⟨437447634169139486915401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2333054048902077263548805 437447634169139486915401)
                  ·
                    rfl

theorem cell20_958417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_958417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958417 prefixEnd_958417 := by exact prefixLift 958417
  have htrace : WordTrace (prefixWord ++ tailWord_958417) baseStart_958417 baseEnd_958417 := by
    simpa [prefixWord, tailWord_958417, baseEnd_958417] using wordTrace_append hprefix tailTrace_958417
  have hstable : (prefixWord ++ tailWord_958417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958417).length < 2 ^ (prefixWord ++ tailWord_958417).sum := by decide
  have hdescent : baseEnd_958417 < baseStart_958417 := by decide
  rcases family_descends (prefixWord ++ tailWord_958417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958465 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 3]
def baseStart_958465 : Nat := 118140960795 + 958465 * 2 ^ 59
def prefixEnd_958465 : Nat := 4983230072969 + 3 ^ 40 * 958465 * 2
def baseEnd_958465 : Nat := 437469542677064653315205

theorem tailTrace_958465 : CollatzResearch.WordTrace tailWord_958465 prefixEnd_958465 437469542677064653315205 := by
  unfold tailWord_958465
  simp only [CollatzResearch.WordTrace]
  refine ⟨34958090472652472634860849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23305393648434981756573899 34958090472652472634860849)
  ·
    refine ⟨26218567854489354476145637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34958090472652472634860849 26218567854489354476145637)
    ·
      refine ⟨4915981472716753964277307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26218567854489354476145637 4915981472716753964277307)
      ·
        refine ⟨7373972209075130946415961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4915981472716753964277307 7373972209075130946415961)
        ·
          refine ⟨5530479156806348209811971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7373972209075130946415961 5530479156806348209811971)
          ·
            refine ⟨8295718735209522314717957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5530479156806348209811971 8295718735209522314717957)
            ·
              refine ⟨1555447262851785434009617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8295718735209522314717957 1555447262851785434009617)
              ·
                refine ⟨1166585447138839075507213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555447262851785434009617 1166585447138839075507213)
                ·
                  refine ⟨437469542677064653315205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166585447138839075507213 437469542677064653315205)
                  ·
                    rfl

theorem cell20_958465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_958465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958465 prefixEnd_958465 := by exact prefixLift 958465
  have htrace : WordTrace (prefixWord ++ tailWord_958465) baseStart_958465 baseEnd_958465 := by
    simpa [prefixWord, tailWord_958465, baseEnd_958465] using wordTrace_append hprefix tailTrace_958465
  have hstable : (prefixWord ++ tailWord_958465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958465).length < 2 ^ (prefixWord ++ tailWord_958465).sum := by decide
  have hdescent : baseEnd_958465 < baseStart_958465 := by decide
  rcases family_descends (prefixWord ++ tailWord_958465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958506 : List Nat := [3, 1, 4, 1, 2, 2, 2, 3, 2]
def baseStart_958506 : Nat := 118140960795 + 958506 * 2 ^ 59
def prefixEnd_958506 : Nat := 4983230072969 + 3 ^ 40 * 958506 * 2
def baseEnd_958506 : Nat := 437488256194250732948371

theorem tailTrace_958506 : CollatzResearch.WordTrace tailWord_958506 prefixEnd_958506 437488256194250732948371 := by
  unfold tailWord_958506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8739896466375984159275843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23306390577002624424735581 8739896466375984159275843)
  ·
    refine ⟨13109844699563976238913765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8739896466375984159275843 13109844699563976238913765)
    ·
      refine ⟨2458095881168245544796331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13109844699563976238913765 2458095881168245544796331)
      ·
        refine ⟨3687143821752368317194497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458095881168245544796331 3687143821752368317194497)
        ·
          refine ⟨2765357866314276237895873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3687143821752368317194497 2765357866314276237895873)
          ·
            refine ⟨2074018399735707178421905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2765357866314276237895873 2074018399735707178421905)
            ·
              refine ⟨1555513799801780383816429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074018399735707178421905 1555513799801780383816429)
              ·
                refine ⟨583317674925667643931161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1555513799801780383816429 583317674925667643931161)
                ·
                  refine ⟨437488256194250732948371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583317674925667643931161 437488256194250732948371)
                  ·
                    rfl

theorem cell20_958506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_958506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958506 prefixEnd_958506 := by exact prefixLift 958506
  have htrace : WordTrace (prefixWord ++ tailWord_958506) baseStart_958506 baseEnd_958506 := by
    simpa [prefixWord, tailWord_958506, baseEnd_958506] using wordTrace_append hprefix tailTrace_958506
  have hstable : (prefixWord ++ tailWord_958506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958506).length < 2 ^ (prefixWord ++ tailWord_958506).sum := by decide
  have hdescent : baseEnd_958506 < baseStart_958506 := by decide
  rcases family_descends (prefixWord ++ tailWord_958506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958516 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 3]
def baseStart_958516 : Nat := 118140960795 + 958516 * 2 ^ 59
def prefixEnd_958516 : Nat := 4983230072969 + 3 ^ 40 * 958516 * 2
def baseEnd_958516 : Nat := 437492820466735142614997

theorem tailTrace_958516 : CollatzResearch.WordTrace tailWord_958516 prefixEnd_958516 437492820466735142614997 := by
  unfold tailWord_958516
  simp only [CollatzResearch.WordTrace]
  refine ⟨17479975297733854172483701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23306633730311805563311601 17479975297733854172483701)
  ·
    refine ⟨1638747684162548828670347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17479975297733854172483701 1638747684162548828670347)
    ·
      refine ⟨2458121526243823243005521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1638747684162548828670347 2458121526243823243005521)
      ·
        refine ⟨1843591144682867432254141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2458121526243823243005521 1843591144682867432254141)
        ·
          refine ⟨691346679256075287095303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1843591144682867432254141 691346679256075287095303)
          ·
            refine ⟨1037020018884112930642955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691346679256075287095303 1037020018884112930642955)
            ·
              refine ⟨1555530028326169395964433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037020018884112930642955 1555530028326169395964433)
              ·
                refine ⟨1166647521244627046973325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555530028326169395964433 1166647521244627046973325)
                ·
                  refine ⟨437492820466735142614997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166647521244627046973325 437492820466735142614997)
                  ·
                    rfl

theorem cell20_958516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_958516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958516 prefixEnd_958516 := by exact prefixLift 958516
  have htrace : WordTrace (prefixWord ++ tailWord_958516) baseStart_958516 baseEnd_958516 := by
    simpa [prefixWord, tailWord_958516, baseEnd_958516] using wordTrace_append hprefix tailTrace_958516
  have hstable : (prefixWord ++ tailWord_958516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958516).length < 2 ^ (prefixWord ++ tailWord_958516).sum := by decide
  have hdescent : baseEnd_958516 < baseStart_958516 := by decide
  rcases family_descends (prefixWord ++ tailWord_958516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958520 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 3]
def baseStart_958520 : Nat := 118140960795 + 958520 * 2 ^ 59
def prefixEnd_958520 : Nat := 4983230072969 + 3 ^ 40 * 958520 * 2
def baseEnd_958520 : Nat := 437494646175728906481647

theorem tailTrace_958520 : CollatzResearch.WordTrace tailWord_958520 prefixEnd_958520 437494646175728906481647 := by
  unfold tailWord_958520
  simp only [CollatzResearch.WordTrace]
  refine ⟨17480048243726608514056507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23306730991635478018742009 17480048243726608514056507)
  ·
    refine ⟨26220072365589912771084761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17480048243726608514056507 26220072365589912771084761)
    ·
      refine ⟨19665054274192434578313571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26220072365589912771084761 19665054274192434578313571)
      ·
        refine ⟨29497581411288651867470357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19665054274192434578313571 29497581411288651867470357)
        ·
          refine ⟨1382699128654155556287673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29497581411288651867470357 1382699128654155556287673)
          ·
            refine ⟨1037024346490616667215755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1382699128654155556287673 1037024346490616667215755)
            ·
              refine ⟨1555536519735925000823633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037024346490616667215755 1555536519735925000823633)
              ·
                refine ⟨1166652389801943750617725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555536519735925000823633 1166652389801943750617725)
                ·
                  refine ⟨437494646175728906481647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166652389801943750617725 437494646175728906481647)
                  ·
                    rfl

theorem cell20_958520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_958520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958520 prefixEnd_958520 := by exact prefixLift 958520
  have htrace : WordTrace (prefixWord ++ tailWord_958520) baseStart_958520 baseEnd_958520 := by
    simpa [prefixWord, tailWord_958520, baseEnd_958520] using wordTrace_append hprefix tailTrace_958520
  have hstable : (prefixWord ++ tailWord_958520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958520).length < 2 ^ (prefixWord ++ tailWord_958520).sum := by decide
  have hdescent : baseEnd_958520 < baseStart_958520 := by decide
  rcases family_descends (prefixWord ++ tailWord_958520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958524 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_958524 : Nat := 118140960795 + 958524 * 2 ^ 59
def prefixEnd_958524 : Nat := 4983230072969 + 3 ^ 40 * 958524 * 2
def baseEnd_958524 : Nat := 437496471884722670348297

theorem tailTrace_958524 : CollatzResearch.WordTrace tailWord_958524 prefixEnd_958524 437496471884722670348297 := by
  unfold tailWord_958524
  simp only [CollatzResearch.WordTrace]
  refine ⟨17480121189719362855629313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23306828252959150474172417 17480121189719362855629313)
  ·
    refine ⟨13110090892289522141721985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17480121189719362855629313 13110090892289522141721985)
    ·
      refine ⟨9832568169217141606291489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13110090892289522141721985 9832568169217141606291489)
      ·
        refine ⟨7374426126912856204718617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9832568169217141606291489 7374426126912856204718617)
        ·
          refine ⟨5530819595184642153538963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7374426126912856204718617 5530819595184642153538963)
          ·
            refine ⟨8296229392776963230308445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5530819595184642153538963 8296229392776963230308445)
            ·
              refine ⟨3111086022291361211365667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8296229392776963230308445 3111086022291361211365667)
              ·
                refine ⟨4666629033437041817048501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111086022291361211365667 4666629033437041817048501)
                ·
                  refine ⟨437496471884722670348297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4666629033437041817048501 437496471884722670348297)
                  ·
                    rfl

theorem cell20_958524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_958524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958524 prefixEnd_958524 := by exact prefixLift 958524
  have htrace : WordTrace (prefixWord ++ tailWord_958524) baseStart_958524 baseEnd_958524 := by
    simpa [prefixWord, tailWord_958524, baseEnd_958524] using wordTrace_append hprefix tailTrace_958524
  have hstable : (prefixWord ++ tailWord_958524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958524).length < 2 ^ (prefixWord ++ tailWord_958524).sum := by decide
  have hdescent : baseEnd_958524 < baseStart_958524 := by decide
  rcases family_descends (prefixWord ++ tailWord_958524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958534 : List Nat := [6, 1, 1, 1, 1, 1, 2, 7]
def baseStart_958534 : Nat := 118140960795 + 958534 * 2 ^ 59
def prefixEnd_958534 : Nat := 4983230072969 + 3 ^ 40 * 958534 * 2
def baseEnd_958534 : Nat := 145833678719069026671641

theorem tailTrace_958534 : CollatzResearch.WordTrace tailWord_958534 prefixEnd_958534 145833678719069026671641 := by
  unfold tailWord_958534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092518972168828044347583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23307071406268331612748437 1092518972168828044347583)
  ·
    refine ⟨1638778458253242066521375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1092518972168828044347583 1638778458253242066521375)
    ·
      refine ⟨2458167687379863099782063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1638778458253242066521375 2458167687379863099782063)
      ·
        refine ⟨3687251531069794649673095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458167687379863099782063 3687251531069794649673095)
        ·
          refine ⟨5530877296604691974509643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687251531069794649673095 5530877296604691974509643)
          ·
            refine ⟨8296315944907037961764465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5530877296604691974509643 8296315944907037961764465)
            ·
              refine ⟨6222236958680278471323349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8296315944907037961764465 6222236958680278471323349)
              ·
                refine ⟨145833678719069026671641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6222236958680278471323349 145833678719069026671641)
                ·
                  rfl

theorem cell20_958534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_958534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958534 prefixEnd_958534 := by exact prefixLift 958534
  have htrace : WordTrace (prefixWord ++ tailWord_958534) baseStart_958534 baseEnd_958534 := by
    simpa [prefixWord, tailWord_958534, baseEnd_958534] using wordTrace_append hprefix tailTrace_958534
  have hstable : (prefixWord ++ tailWord_958534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958534).length < 2 ^ (prefixWord ++ tailWord_958534).sum := by decide
  have hdescent : baseEnd_958534 < baseStart_958534 := by decide
  rcases family_descends (prefixWord ++ tailWord_958534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958538 : List Nat := [3, 1, 2, 1, 1, 2, 1, 9]
def baseStart_958538 : Nat := 118140960795 + 958538 * 2 ^ 59
def prefixEnd_958538 : Nat := 4983230072969 + 3 ^ 40 * 958538 * 2
def baseEnd_958538 : Nat := 145834287288733614627191

theorem tailTrace_958538 : CollatzResearch.WordTrace tailWord_958538 prefixEnd_958538 145834287288733614627191 := by
  unfold tailWord_958538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8740188250347001525567067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23307168667592004068178845 8740188250347001525567067)
  ·
    refine ⟨13110282375520502288350601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8740188250347001525567067 13110282375520502288350601)
    ·
      refine ⟨9832711781640376716262951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13110282375520502288350601 9832711781640376716262951)
      ·
        refine ⟨14749067672460565074394427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9832711781640376716262951 14749067672460565074394427)
        ·
          refine ⟨22123601508690847611591641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14749067672460565074394427 22123601508690847611591641)
          ·
            refine ⟨16592701131518135708693731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22123601508690847611591641 16592701131518135708693731)
            ·
              refine ⟨24889051697277203563040597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16592701131518135708693731 24889051697277203563040597)
              ·
                refine ⟨145834287288733614627191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24889051697277203563040597 145834287288733614627191)
                ·
                  rfl

theorem cell20_958538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_958538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958538 prefixEnd_958538 := by exact prefixLift 958538
  have htrace : WordTrace (prefixWord ++ tailWord_958538) baseStart_958538 baseEnd_958538 := by
    simpa [prefixWord, tailWord_958538, baseEnd_958538] using wordTrace_append hprefix tailTrace_958538
  have hstable : (prefixWord ++ tailWord_958538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958538).length < 2 ^ (prefixWord ++ tailWord_958538).sum := by decide
  have hdescent : baseEnd_958538 < baseStart_958538 := by decide
  rcases family_descends (prefixWord ++ tailWord_958538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958565 : List Nat := [1, 3, 1, 3, 2, 2, 3, 3, 2]
def baseStart_958565 : Nat := 118140960795 + 958565 * 2 ^ 59
def prefixEnd_958565 : Nat := 4983230072969 + 3 ^ 40 * 958565 * 2
def baseEnd_958565 : Nat := 437515185401908749981463

theorem tailTrace_958565 : CollatzResearch.WordTrace tailWord_958565 prefixEnd_958565 437515185401908749981463 := by
  unfold tailWord_958565
  simp only [CollatzResearch.WordTrace]
  refine ⟨34961737772290189713501149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23307825181526793142334099 34961737772290189713501149)
  ·
    refine ⟨13110651664608821142562931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34961737772290189713501149 13110651664608821142562931)
    ·
      refine ⟨19665977496913231713844397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13110651664608821142562931 19665977496913231713844397)
      ·
        refine ⟨7374741561342461892691649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19665977496913231713844397 7374741561342461892691649)
        ·
          refine ⟨5531056171006846419518737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7374741561342461892691649 5531056171006846419518737)
          ·
            refine ⟨4148292128255134814639053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5531056171006846419518737 4148292128255134814639053)
            ·
              refine ⟨1555609548095675555489645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4148292128255134814639053 1555609548095675555489645)
              ·
                refine ⟨583353580535878333308617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1555609548095675555489645 583353580535878333308617)
                ·
                  refine ⟨437515185401908749981463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583353580535878333308617 437515185401908749981463)
                  ·
                    rfl

theorem cell20_958565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_958565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958565 prefixEnd_958565 := by exact prefixLift 958565
  have htrace : WordTrace (prefixWord ++ tailWord_958565) baseStart_958565 baseEnd_958565 := by
    simpa [prefixWord, tailWord_958565, baseEnd_958565] using wordTrace_append hprefix tailTrace_958565
  have hstable : (prefixWord ++ tailWord_958565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958565).length < 2 ^ (prefixWord ++ tailWord_958565).sum := by decide
  have hdescent : baseEnd_958565 < baseStart_958565 := by decide
  rcases family_descends (prefixWord ++ tailWord_958565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958576 : List Nat := [2, 1, 1, 1, 5, 2, 8]
def baseStart_958576 : Nat := 118140960795 + 958576 * 2 ^ 59
def prefixEnd_958576 : Nat := 4983230072969 + 3 ^ 40 * 958576 * 2
def baseEnd_958576 : Nat := 48613356233515733401639

theorem tailTrace_958576 : CollatzResearch.WordTrace tailWord_958576 prefixEnd_958576 48613356233515733401639 := by
  unfold tailWord_958576
  simp only [CollatzResearch.WordTrace]
  refine ⟨17481069487625169296075791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23308092650166892394767721 17481069487625169296075791)
  ·
    refine ⟨26221604231437753944113687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17481069487625169296075791 26221604231437753944113687)
    ·
      refine ⟨39332406347156630916170531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26221604231437753944113687 39332406347156630916170531)
      ·
        refine ⟨58998609520734946374255797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39332406347156630916170531 58998609520734946374255797)
        ·
          refine ⟨5531119642568901222586481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58998609520734946374255797 5531119642568901222586481)
          ·
            refine ⟨4148339731926675916939861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5531119642568901222586481 4148339731926675916939861)
            ·
              refine ⟨48613356233515733401639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4148339731926675916939861 48613356233515733401639)
              ·
                rfl

theorem cell20_958576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 8].length) (baseStart_958576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958576 prefixEnd_958576 := by exact prefixLift 958576
  have htrace : WordTrace (prefixWord ++ tailWord_958576) baseStart_958576 baseEnd_958576 := by
    simpa [prefixWord, tailWord_958576, baseEnd_958576] using wordTrace_append hprefix tailTrace_958576
  have hstable : (prefixWord ++ tailWord_958576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958576).length < 2 ^ (prefixWord ++ tailWord_958576).sum := by decide
  have hdescent : baseEnd_958576 < baseStart_958576 := by decide
  rcases family_descends (prefixWord ++ tailWord_958576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958631 : List Nat := [1, 1, 6, 2, 2, 8]
def baseStart_958631 : Nat := 118140960795 + 958631 * 2 ^ 59
def prefixEnd_958631 : Nat := 4983230072969 + 3 ^ 40 * 958631 * 2
def baseEnd_958631 : Nat := 16205381837048364954859

theorem tailTrace_958631 : CollatzResearch.WordTrace tailWord_958631 prefixEnd_958631 16205381837048364954859 := by
  unfold tailWord_958631
  simp only [CollatzResearch.WordTrace]
  refine ⟨34964144990051082985403747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23309429993367388656935831 34964144990051082985403747)
  ·
    refine ⟨52446217485076624478105621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34964144990051082985403747 52446217485076624478105621)
    ·
      refine ⟨2458416444612966772411201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52446217485076624478105621 2458416444612966772411201)
      ·
        refine ⟨1843812333459725079308401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2458416444612966772411201 1843812333459725079308401)
        ·
          refine ⟨1382859250094793809481301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1843812333459725079308401 1382859250094793809481301)
          ·
            refine ⟨16205381837048364954859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1382859250094793809481301 16205381837048364954859)
            ·
              rfl

theorem cell20_958631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 8].length) (baseStart_958631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958631 prefixEnd_958631 := by exact prefixLift 958631
  have htrace : WordTrace (prefixWord ++ tailWord_958631) baseStart_958631 baseEnd_958631 := by
    simpa [prefixWord, tailWord_958631, baseEnd_958631] using wordTrace_append hprefix tailTrace_958631
  have hstable : (prefixWord ++ tailWord_958631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958631).length < 2 ^ (prefixWord ++ tailWord_958631).sum := by decide
  have hdescent : baseEnd_958631 < baseStart_958631 := by decide
  rcases family_descends (prefixWord ++ tailWord_958631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958637 : List Nat := [1, 5, 2, 1, 2, 3, 2, 2, 2]
def baseStart_958637 : Nat := 118140960795 + 958637 * 2 ^ 59
def prefixEnd_958637 : Nat := 4983230072969 + 3 ^ 40 * 958637 * 2
def baseEnd_958637 : Nat := 437548048163796499581169

theorem tailTrace_958637 : CollatzResearch.WordTrace tailWord_958637 prefixEnd_958637 437548048163796499581169 := by
  unfold tailWord_958637
  simp only [CollatzResearch.WordTrace]
  refine ⟨34964363828029346010122165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23309575885352897340081443 34964363828029346010122165)
  ·
    refine ⟨3277909108877751188448953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34964363828029346010122165 3277909108877751188448953)
    ·
      refine ⟨2458431831658313391336715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3277909108877751188448953 2458431831658313391336715)
      ·
        refine ⟨3687647747487470087005073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458431831658313391336715 3687647747487470087005073)
        ·
          refine ⟨2765735810615602565253805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3687647747487470087005073 2765735810615602565253805)
          ·
            refine ⟨1037150928980850961970177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2765735810615602565253805 1037150928980850961970177)
            ·
              refine ⟨777863196735638221477633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037150928980850961970177 777863196735638221477633)
              ·
                refine ⟨583397397551728666108225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777863196735638221477633 583397397551728666108225)
                ·
                  refine ⟨437548048163796499581169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583397397551728666108225 437548048163796499581169)
                  ·
                    rfl

theorem cell20_958637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_958637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958637 prefixEnd_958637 := by exact prefixLift 958637
  have htrace : WordTrace (prefixWord ++ tailWord_958637) baseStart_958637 baseEnd_958637 := by
    simpa [prefixWord, tailWord_958637, baseEnd_958637] using wordTrace_append hprefix tailTrace_958637
  have hstable : (prefixWord ++ tailWord_958637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958637).length < 2 ^ (prefixWord ++ tailWord_958637).sum := by decide
  have hdescent : baseEnd_958637 < baseStart_958637 := by decide
  rcases family_descends (prefixWord ++ tailWord_958637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958658 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_958658 : Nat := 118140960795 + 958658 * 2 ^ 59
def prefixEnd_958658 : Nat := 4983230072969 + 3 ^ 40 * 958658 * 2
def baseEnd_958658 : Nat := 437557633136013759881083

theorem tailTrace_958658 : CollatzResearch.WordTrace tailWord_958658 prefixEnd_958658 437557633136013759881083 := by
  unfold tailWord_958658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8741282440238316649159157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23310086507302177731091085 8741282440238316649159157)
  ·
    refine ⟨819495228772342185858671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8741282440238316649159157 819495228772342185858671)
    ·
      refine ⟨1229242843158513278788007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819495228772342185858671 1229242843158513278788007)
      ·
        refine ⟨1843864264737769918182011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229242843158513278788007 1843864264737769918182011)
        ·
          refine ⟨2765796397106654877273017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843864264737769918182011 2765796397106654877273017)
          ·
            refine ⟨2074347297829991157954763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2765796397106654877273017 2074347297829991157954763)
            ·
              refine ⟨3111520946744986736932145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074347297829991157954763 3111520946744986736932145)
              ·
                refine ⟨2333640710058740052699109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3111520946744986736932145 2333640710058740052699109)
                ·
                  refine ⟨437557633136013759881083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2333640710058740052699109 437557633136013759881083)
                  ·
                    rfl

theorem cell20_958658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_958658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958658 prefixEnd_958658 := by exact prefixLift 958658
  have htrace : WordTrace (prefixWord ++ tailWord_958658) baseStart_958658 baseEnd_958658 := by
    simpa [prefixWord, tailWord_958658, baseEnd_958658] using wordTrace_append hprefix tailTrace_958658
  have hstable : (prefixWord ++ tailWord_958658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958658).length < 2 ^ (prefixWord ++ tailWord_958658).sum := by decide
  have hdescent : baseEnd_958658 < baseStart_958658 := by decide
  rcases family_descends (prefixWord ++ tailWord_958658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958693 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 3]
def baseStart_958693 : Nat := 118140960795 + 958693 * 2 ^ 59
def prefixEnd_958693 : Nat := 4983230072969 + 3 ^ 40 * 958693 * 2
def baseEnd_958693 : Nat := 437573608089709193714273

theorem tailTrace_958693 : CollatzResearch.WordTrace tailWord_958693 prefixEnd_958693 437573608089709193714273 := by
  unfold tailWord_958693
  simp only [CollatzResearch.WordTrace]
  refine ⟨34966406315826467574160733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23310937543884311716107155 34966406315826467574160733)
  ·
    refine ⟨13112402368434925340310275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34966406315826467574160733 13112402368434925340310275)
    ·
      refine ⟨19668603552652388010465413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13112402368434925340310275 19668603552652388010465413)
      ·
        refine ⟨3687863166122322751962265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19668603552652388010465413 3687863166122322751962265)
        ·
          refine ⟨2765897374591742063971699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3687863166122322751962265 2765897374591742063971699)
          ·
            refine ⟨4148846061887613095957549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765897374591742063971699 4148846061887613095957549)
            ·
              refine ⟨1555817273207854910984081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4148846061887613095957549 1555817273207854910984081)
              ·
                refine ⟨1166862954905891183238061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555817273207854910984081 1166862954905891183238061)
                ·
                  refine ⟨437573608089709193714273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166862954905891183238061 437573608089709193714273)
                  ·
                    rfl

theorem cell20_958693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_958693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958693 prefixEnd_958693 := by exact prefixLift 958693
  have htrace : WordTrace (prefixWord ++ tailWord_958693) baseStart_958693 baseEnd_958693 := by
    simpa [prefixWord, tailWord_958693, baseEnd_958693] using wordTrace_append hprefix tailTrace_958693
  have hstable : (prefixWord ++ tailWord_958693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958693).length < 2 ^ (prefixWord ++ tailWord_958693).sum := by decide
  have hdescent : baseEnd_958693 < baseStart_958693 := by decide
  rcases family_descends (prefixWord ++ tailWord_958693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958697 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_958697 : Nat := 118140960795 + 958697 * 2 ^ 59
def prefixEnd_958697 : Nat := 4983230072969 + 3 ^ 40 * 958697 * 2
def baseEnd_958697 : Nat := 437575433798702957580923

theorem tailTrace_958697 : CollatzResearch.WordTrace tailWord_958697 prefixEnd_958697 437575433798702957580923 := by
  unfold tailWord_958697
  simp only [CollatzResearch.WordTrace]
  refine ⟨34966552207811976257306345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23311034805207984171537563 34966552207811976257306345)
  ·
    refine ⟨26224914155858982192979759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34966552207811976257306345 26224914155858982192979759)
    ·
      refine ⟨39337371233788473289469639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26224914155858982192979759 39337371233788473289469639)
      ·
        refine ⟨59006056850682709934204459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39337371233788473289469639 59006056850682709934204459)
        ·
          refine ⟨88509085276024064901306689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59006056850682709934204459 88509085276024064901306689)
          ·
            refine ⟨66381813957018048675980017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88509085276024064901306689 66381813957018048675980017)
            ·
              refine ⟨49786360467763536506985013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66381813957018048675980017 49786360467763536506985013)
              ·
                refine ⟨4667471293852831547529845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49786360467763536506985013 4667471293852831547529845)
                ·
                  refine ⟨437575433798702957580923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4667471293852831547529845 437575433798702957580923)
                  ·
                    rfl

theorem cell20_958697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_958697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958697 prefixEnd_958697 := by exact prefixLift 958697
  have htrace : WordTrace (prefixWord ++ tailWord_958697) baseStart_958697 baseEnd_958697 := by
    simpa [prefixWord, tailWord_958697, baseEnd_958697] using wordTrace_append hprefix tailTrace_958697
  have hstable : (prefixWord ++ tailWord_958697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958697).length < 2 ^ (prefixWord ++ tailWord_958697).sum := by decide
  have hdescent : baseEnd_958697 < baseStart_958697 := by decide
  rcases family_descends (prefixWord ++ tailWord_958697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958700 : List Nat := [2, 2, 1, 1, 2, 3, 1, 6, 2]
def baseStart_958700 : Nat := 118140960795 + 958700 * 2 ^ 59
def prefixEnd_958700 : Nat := 4983230072969 + 3 ^ 40 * 958700 * 2
def baseEnd_958700 : Nat := 437576803080448280480911

theorem tailTrace_958700 : CollatzResearch.WordTrace tailWord_958700 prefixEnd_958700 437576803080448280480911 := by
  unfold tailWord_958700
  simp only [CollatzResearch.WordTrace]
  refine ⟨17483330813400553884832777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23311107751200738513110369 17483330813400553884832777)
  ·
    refine ⟨13112498110050415413624583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17483330813400553884832777 13112498110050415413624583)
    ·
      refine ⟨19668747165075623120436875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13112498110050415413624583 19668747165075623120436875)
      ·
        refine ⟨29503120747613434680655313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19668747165075623120436875 29503120747613434680655313)
        ·
          refine ⟨22127340560710076010491485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29503120747613434680655313 22127340560710076010491485)
          ·
            refine ⟨8297752710266278503934307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22127340560710076010491485 8297752710266278503934307)
            ·
              refine ⟨12446629065399417755901461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8297752710266278503934307 12446629065399417755901461)
              ·
                refine ⟨583435737440597707307881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12446629065399417755901461 583435737440597707307881)
                ·
                  refine ⟨437576803080448280480911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583435737440597707307881 437576803080448280480911)
                  ·
                    rfl

theorem cell20_958700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_958700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958700 prefixEnd_958700 := by exact prefixLift 958700
  have htrace : WordTrace (prefixWord ++ tailWord_958700) baseStart_958700 baseEnd_958700 := by
    simpa [prefixWord, tailWord_958700, baseEnd_958700] using wordTrace_append hprefix tailTrace_958700
  have hstable : (prefixWord ++ tailWord_958700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958700).length < 2 ^ (prefixWord ++ tailWord_958700).sum := by decide
  have hdescent : baseEnd_958700 < baseStart_958700 := by decide
  rcases family_descends (prefixWord ++ tailWord_958700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958721 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_958721 : Nat := 118140960795 + 958721 * 2 ^ 59
def prefixEnd_958721 : Nat := 4983230072969 + 3 ^ 40 * 958721 * 2
def baseEnd_958721 : Nat := 437586388052665540780825

theorem tailTrace_958721 : CollatzResearch.WordTrace tailWord_958721 prefixEnd_958721 437586388052665540780825 := by
  unfold tailWord_958721
  simp only [CollatzResearch.WordTrace]
  refine ⟨34967427559725028356180017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23311618373150018904120011 34967427559725028356180017)
  ·
    refine ⟨26225570669793771267135013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34967427559725028356180017 26225570669793771267135013)
    ·
      refine ⟨4917294500586332112587815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26225570669793771267135013 4917294500586332112587815)
      ·
        refine ⟨7375941750879498168881723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917294500586332112587815 7375941750879498168881723)
        ·
          refine ⟨11063912626319247253322585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7375941750879498168881723 11063912626319247253322585)
          ·
            refine ⟨8297934469739435439991939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11063912626319247253322585 8297934469739435439991939)
            ·
              refine ⟨12446901704609153159987909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8297934469739435439991939 12446901704609153159987909)
              ·
                refine ⟨2333794069614216217497733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12446901704609153159987909 2333794069614216217497733)
                ·
                  refine ⟨437586388052665540780825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2333794069614216217497733 437586388052665540780825)
                  ·
                    rfl

theorem cell20_958721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_958721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958721 prefixEnd_958721 := by exact prefixLift 958721
  have htrace : WordTrace (prefixWord ++ tailWord_958721) baseStart_958721 baseEnd_958721 := by
    simpa [prefixWord, tailWord_958721, baseEnd_958721] using wordTrace_append hprefix tailTrace_958721
  have hstable : (prefixWord ++ tailWord_958721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958721).length < 2 ^ (prefixWord ++ tailWord_958721).sum := by decide
  have hdescent : baseEnd_958721 < baseStart_958721 := by decide
  rcases family_descends (prefixWord ++ tailWord_958721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958752 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_958752 : Nat := 118140960795 + 958752 * 2 ^ 59
def prefixEnd_958752 : Nat := 4983230072969 + 3 ^ 40 * 958752 * 2
def baseEnd_958752 : Nat := 437600537297367210747365

theorem tailTrace_958752 : CollatzResearch.WordTrace tailWord_958752 prefixEnd_958752 437600537297367210747365 := by
  unfold tailWord_958752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17484279111306360325279255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23312372148408480433705673 17484279111306360325279255)
  ·
    refine ⟨26226418666959540487918883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17484279111306360325279255 26226418666959540487918883)
    ·
      refine ⟨39339628000439310731878325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26226418666959540487918883 39339628000439310731878325)
      ·
        refine ⟨3688090125041185381113593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39339628000439310731878325 3688090125041185381113593)
        ·
          refine ⟨2766067593780889035835195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3688090125041185381113593 2766067593780889035835195)
          ·
            refine ⟨4149101390671333553752793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766067593780889035835195 4149101390671333553752793)
            ·
              refine ⟨3111826043003500165314595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149101390671333553752793 3111826043003500165314595)
              ·
                refine ⟨4667739064505250247971893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111826043003500165314595 4667739064505250247971893)
                ·
                  refine ⟨437600537297367210747365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4667739064505250247971893 437600537297367210747365)
                  ·
                    rfl

theorem cell20_958752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_958752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958752 prefixEnd_958752 := by exact prefixLift 958752
  have htrace : WordTrace (prefixWord ++ tailWord_958752) baseStart_958752 baseEnd_958752 := by
    simpa [prefixWord, tailWord_958752, baseEnd_958752] using wordTrace_append hprefix tailTrace_958752
  have hstable : (prefixWord ++ tailWord_958752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958752).length < 2 ^ (prefixWord ++ tailWord_958752).sum := by decide
  have hdescent : baseEnd_958752 < baseStart_958752 := by decide
  rcases family_descends (prefixWord ++ tailWord_958752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958755 : List Nat := [1, 1, 1, 4, 2, 2, 5, 2, 2]
def baseStart_958755 : Nat := 118140960795 + 958755 * 2 ^ 59
def prefixEnd_958755 : Nat := 4983230072969 + 3 ^ 40 * 958755 * 2
def baseEnd_958755 : Nat := 437601906579112533647353

theorem tailTrace_958755 : CollatzResearch.WordTrace tailWord_958755 prefixEnd_958755 437601906579112533647353 := by
  unfold tailWord_958755
  simp only [CollatzResearch.WordTrace]
  refine ⟨34968667641601852162917719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23312445094401234775278479 34968667641601852162917719)
  ·
    refine ⟨52453001462402778244376579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34968667641601852162917719 52453001462402778244376579)
    ·
      refine ⟨78679502193604167366564869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52453001462402778244376579 78679502193604167366564869)
      ·
        refine ⟨14752406661300781381230913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78679502193604167366564869 14752406661300781381230913)
        ·
          refine ⟨11064304995975586035923185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14752406661300781381230913 11064304995975586035923185)
          ·
            refine ⟨8298228746981689526942389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11064304995975586035923185 8298228746981689526942389)
            ·
              refine ⟨777958945029533393150849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8298228746981689526942389 777958945029533393150849)
              ·
                refine ⟨583469208772150044863137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777958945029533393150849 583469208772150044863137)
                ·
                  refine ⟨437601906579112533647353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583469208772150044863137 437601906579112533647353)
                  ·
                    rfl

theorem cell20_958755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 2].length) (baseStart_958755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958755 prefixEnd_958755 := by exact prefixLift 958755
  have htrace : WordTrace (prefixWord ++ tailWord_958755) baseStart_958755 baseEnd_958755 := by
    simpa [prefixWord, tailWord_958755, baseEnd_958755] using wordTrace_append hprefix tailTrace_958755
  have hstable : (prefixWord ++ tailWord_958755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958755).length < 2 ^ (prefixWord ++ tailWord_958755).sum := by decide
  have hdescent : baseEnd_958755 < baseStart_958755 := by decide
  rcases family_descends (prefixWord ++ tailWord_958755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958762 : List Nat := [3, 1, 4, 2, 2, 1, 2, 5]
def baseStart_958762 : Nat := 118140960795 + 958762 * 2 ^ 59
def prefixEnd_958762 : Nat := 4983230072969 + 3 ^ 40 * 958762 * 2
def baseEnd_958762 : Nat := 145868367189950540137997

theorem tailTrace_958762 : CollatzResearch.WordTrace tailWord_958762 prefixEnd_958762 145868367189950540137997 := by
  unfold tailWord_958762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8742230738144123089605635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23312615301717661572281693 8742230738144123089605635)
  ·
    refine ⟨13113346107216184634408453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8742230738144123089605635 13113346107216184634408453)
    ·
      refine ⟨2458752395103034618951585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13113346107216184634408453 2458752395103034618951585)
      ·
        refine ⟨1844064296327275964213689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2458752395103034618951585 1844064296327275964213689)
        ·
          refine ⟨1383048222245456973160267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1844064296327275964213689 1383048222245456973160267)
          ·
            refine ⟨2074572333368185459740401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383048222245456973160267 2074572333368185459740401)
            ·
              refine ⟨1555929250026139094805301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074572333368185459740401 1555929250026139094805301)
              ·
                refine ⟨145868367189950540137997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1555929250026139094805301 145868367189950540137997)
                ·
                  rfl

theorem cell20_958762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_958762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958762 prefixEnd_958762 := by exact prefixLift 958762
  have htrace : WordTrace (prefixWord ++ tailWord_958762) baseStart_958762 baseEnd_958762 := by
    simpa [prefixWord, tailWord_958762, baseEnd_958762] using wordTrace_append hprefix tailTrace_958762
  have hstable : (prefixWord ++ tailWord_958762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958762).length < 2 ^ (prefixWord ++ tailWord_958762).sum := by decide
  have hdescent : baseEnd_958762 < baseStart_958762 := by decide
  rcases family_descends (prefixWord ++ tailWord_958762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958769 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 3]
def baseStart_958769 : Nat := 118140960795 + 958769 * 2 ^ 59
def prefixEnd_958769 : Nat := 4983230072969 + 3 ^ 40 * 958769 * 2
def baseEnd_958769 : Nat := 437608296560590707180629

theorem tailTrace_958769 : CollatzResearch.WordTrace tailWord_958769 prefixEnd_958769 437608296560590707180629 := by
  unfold tailWord_958769
  simp only [CollatzResearch.WordTrace]
  refine ⟨34969178263551132553927361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23312785509034088369284907 34969178263551132553927361)
  ·
    refine ⟨26226883697663349415445521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34969178263551132553927361 26226883697663349415445521)
    ·
      refine ⟨19670162773247512061584141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26226883697663349415445521 19670162773247512061584141)
      ·
        refine ⟨7376311039967817023094053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19670162773247512061584141 7376311039967817023094053)
        ·
          refine ⟨1383058319993965691830135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7376311039967817023094053 1383058319993965691830135)
          ·
            refine ⟨2074587479990948537745203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383058319993965691830135 2074587479990948537745203)
            ·
              refine ⟨3111881219986422806617805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074587479990948537745203 3111881219986422806617805)
              ·
                refine ⟨1166955457494908552481677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3111881219986422806617805 1166955457494908552481677)
                ·
                  refine ⟨437608296560590707180629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166955457494908552481677 437608296560590707180629)
                  ·
                    rfl

theorem cell20_958769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_958769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958769 prefixEnd_958769 := by exact prefixLift 958769
  have htrace : WordTrace (prefixWord ++ tailWord_958769) baseStart_958769 baseEnd_958769 := by
    simpa [prefixWord, tailWord_958769, baseEnd_958769] using wordTrace_append hprefix tailTrace_958769
  have hstable : (prefixWord ++ tailWord_958769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958769).length < 2 ^ (prefixWord ++ tailWord_958769).sum := by decide
  have hdescent : baseEnd_958769 < baseStart_958769 := by decide
  rcases family_descends (prefixWord ++ tailWord_958769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958804 : List Nat := [2, 4, 1, 1, 2, 10]
def baseStart_958804 : Nat := 118140960795 + 958804 * 2 ^ 59
def prefixEnd_958804 : Nat := 4983230072969 + 3 ^ 40 * 958804 * 2
def baseEnd_958804 : Nat := 16208306352380968185697

theorem tailTrace_958804 : CollatzResearch.WordTrace tailWord_958804 prefixEnd_958804 16208306352380968185697 := by
  unfold tailWord_958804
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485227409212166765725733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23313636545616222354300977 17485227409212166765725733)
  ·
    refine ⟨3278480139227281268573575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17485227409212166765725733 3278480139227281268573575)
    ·
      refine ⟨4917720208840921902860363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278480139227281268573575 4917720208840921902860363)
      ·
        refine ⟨7376580313261382854290545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917720208840921902860363 7376580313261382854290545)
        ·
          refine ⟨5532435234946037140717909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7376580313261382854290545 5532435234946037140717909)
          ·
            refine ⟨16208306352380968185697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5532435234946037140717909 16208306352380968185697)
            ·
              rfl

theorem cell20_958804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 10].length) (baseStart_958804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958804 prefixEnd_958804 := by exact prefixLift 958804
  have htrace : WordTrace (prefixWord ++ tailWord_958804) baseStart_958804 baseEnd_958804 := by
    simpa [prefixWord, tailWord_958804, baseEnd_958804] using wordTrace_append hprefix tailTrace_958804
  have hstable : (prefixWord ++ tailWord_958804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958804).length < 2 ^ (prefixWord ++ tailWord_958804).sum := by decide
  have hdescent : baseEnd_958804 < baseStart_958804 := by decide
  rcases family_descends (prefixWord ++ tailWord_958804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958821 : List Nat := [1, 3, 1, 3, 1, 5, 1, 5]
def baseStart_958821 : Nat := 118140960795 + 958821 * 2 ^ 59
def prefixEnd_958821 : Nat := 4983230072969 + 3 ^ 40 * 958821 * 2
def baseEnd_958821 : Nat := 145877343592503212482361

theorem tailTrace_958821 : CollatzResearch.WordTrace tailWord_958821 prefixEnd_958821 145877343592503212482361 := by
  unfold tailWord_958821
  simp only [CollatzResearch.WordTrace]
  refine ⟨34971074859362745434820317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23314049906241830289880211 34971074859362745434820317)
  ·
    refine ⟨13114153072261029538057619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34971074859362745434820317 13114153072261029538057619)
    ·
      refine ⟨19671229608391544307086429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13114153072261029538057619 19671229608391544307086429)
      ·
        refine ⟨7376711103146829115157411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19671229608391544307086429 7376711103146829115157411)
        ·
          refine ⟨11065066654720243672736117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376711103146829115157411 11065066654720243672736117)
          ·
            refine ⟨1037349998880022844319011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11065066654720243672736117 1037349998880022844319011)
            ·
              refine ⟨1556024998320034266478517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037349998880022844319011 1556024998320034266478517)
              ·
                refine ⟨145877343592503212482361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1556024998320034266478517 145877343592503212482361)
                ·
                  rfl

theorem cell20_958821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 5].length) (baseStart_958821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958821 prefixEnd_958821 := by exact prefixLift 958821
  have htrace : WordTrace (prefixWord ++ tailWord_958821) baseStart_958821 baseEnd_958821 := by
    simpa [prefixWord, tailWord_958821, baseEnd_958821] using wordTrace_append hprefix tailTrace_958821
  have hstable : (prefixWord ++ tailWord_958821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958821).length < 2 ^ (prefixWord ++ tailWord_958821).sum := by decide
  have hdescent : baseEnd_958821 < baseStart_958821 := by decide
  rcases family_descends (prefixWord ++ tailWord_958821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958862 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_958862 : Nat := 118140960795 + 958862 * 2 ^ 59
def prefixEnd_958862 : Nat := 4983230072969 + 3 ^ 40 * 958862 * 2
def baseEnd_958862 : Nat := 437650744294695717080249

theorem tailTrace_958862 : CollatzResearch.WordTrace tailWord_958862 prefixEnd_958862 437650744294695717080249 := by
  unfold tailWord_958862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4371571281526776179632855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23315046834809472958041893 4371571281526776179632855)
  ·
    refine ⟨6557356922290164269449283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4371571281526776179632855 6557356922290164269449283)
    ·
      refine ⟨9836035383435246404173925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557356922290164269449283 9836035383435246404173925)
      ·
        refine ⟨1844256634394108700782611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9836035383435246404173925 1844256634394108700782611)
        ·
          refine ⟨2766384951591163051173917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844256634394108700782611 2766384951591163051173917)
          ·
            refine ⟨1037394356846686144190219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2766384951591163051173917 1037394356846686144190219)
            ·
              refine ⟨1556091535270029216285329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037394356846686144190219 1556091535270029216285329)
              ·
                refine ⟨1167068651452521912213997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556091535270029216285329 1167068651452521912213997)
                ·
                  refine ⟨437650744294695717080249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167068651452521912213997 437650744294695717080249)
                  ·
                    rfl

theorem cell20_958862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_958862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958862 prefixEnd_958862 := by exact prefixLift 958862
  have htrace : WordTrace (prefixWord ++ tailWord_958862) baseStart_958862 baseEnd_958862 := by
    simpa [prefixWord, tailWord_958862, baseEnd_958862] using wordTrace_append hprefix tailTrace_958862
  have hstable : (prefixWord ++ tailWord_958862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958862).length < 2 ^ (prefixWord ++ tailWord_958862).sum := by decide
  have hdescent : baseEnd_958862 < baseStart_958862 := by decide
  rcases family_descends (prefixWord ++ tailWord_958862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958873 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 4]
def baseStart_958873 : Nat := 118140960795 + 958873 * 2 ^ 59
def prefixEnd_958873 : Nat := 4983230072969 + 3 ^ 40 * 958873 * 2
def baseEnd_958873 : Nat := 437655764994428567713537

theorem tailTrace_958873 : CollatzResearch.WordTrace tailWord_958873 prefixEnd_958873 437655764994428567713537 := by
  unfold tailWord_958873
  simp only [CollatzResearch.WordTrace]
  refine ⟨34972971455174358315713273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23315314303449572210475515 34972971455174358315713273)
  ·
    refine ⟨26229728591380768736784955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34972971455174358315713273 26229728591380768736784955)
    ·
      refine ⟨39344592887071153105177433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26229728591380768736784955 39344592887071153105177433)
      ·
        refine ⟨29508444665303364828883075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39344592887071153105177433 29508444665303364828883075)
        ·
          refine ⟨44262666997955047243324613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29508444665303364828883075 44262666997955047243324613)
          ·
            refine ⟨8299250062116571358123365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44262666997955047243324613 8299250062116571358123365)
            ·
              refine ⟨1556109386646857129648131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8299250062116571358123365 1556109386646857129648131)
              ·
                refine ⟨2334164079970285694472197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556109386646857129648131 2334164079970285694472197)
                ·
                  refine ⟨437655764994428567713537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334164079970285694472197 437655764994428567713537)
                  ·
                    rfl

theorem cell20_958873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_958873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958873 prefixEnd_958873 := by exact prefixLift 958873
  have htrace : WordTrace (prefixWord ++ tailWord_958873) baseStart_958873 baseEnd_958873 := by
    simpa [prefixWord, tailWord_958873, baseEnd_958873] using wordTrace_append hprefix tailTrace_958873
  have hstable : (prefixWord ++ tailWord_958873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958873).length < 2 ^ (prefixWord ++ tailWord_958873).sum := by decide
  have hdescent : baseEnd_958873 < baseStart_958873 := by decide
  rcases family_descends (prefixWord ++ tailWord_958873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958883 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 3]
def baseStart_958883 : Nat := 118140960795 + 958883 * 2 ^ 59
def prefixEnd_958883 : Nat := 4983230072969 + 3 ^ 40 * 958883 * 2
def baseEnd_958883 : Nat := 437660329266912977380163

theorem tailTrace_958883 : CollatzResearch.WordTrace tailWord_958883 prefixEnd_958883 437660329266912977380163 := by
  unfold tailWord_958883
  simp only [CollatzResearch.WordTrace]
  refine ⟨34973336185138130023577303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23315557456758753349051535 34973336185138130023577303)
  ·
    refine ⟨52460004277707195035365955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34973336185138130023577303 52460004277707195035365955)
    ·
      refine ⟨78690006416560792553048933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52460004277707195035365955 78690006416560792553048933)
      ·
        refine ⟨14754376203105148603696675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78690006416560792553048933 14754376203105148603696675)
        ·
          refine ⟨22131564304657722905545013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14754376203105148603696675 22131564304657722905545013)
          ·
            refine ⟨2074834153561661522394845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22131564304657722905545013 2074834153561661522394845)
            ·
              refine ⟨778062807585623070898067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2074834153561661522394845 778062807585623070898067)
              ·
                refine ⟨1167094211378434606347101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778062807585623070898067 1167094211378434606347101)
                ·
                  refine ⟨437660329266912977380163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167094211378434606347101 437660329266912977380163)
                  ·
                    rfl

theorem cell20_958883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 3].length) (baseStart_958883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958883 prefixEnd_958883 := by exact prefixLift 958883
  have htrace : WordTrace (prefixWord ++ tailWord_958883) baseStart_958883 baseEnd_958883 := by
    simpa [prefixWord, tailWord_958883, baseEnd_958883] using wordTrace_append hprefix tailTrace_958883
  have hstable : (prefixWord ++ tailWord_958883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958883).length < 2 ^ (prefixWord ++ tailWord_958883).sum := by decide
  have hdescent : baseEnd_958883 < baseStart_958883 := by decide
  rcases family_descends (prefixWord ++ tailWord_958883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958893 : List Nat := [1, 5, 2, 2, 2, 2, 2, 4]
def baseStart_958893 : Nat := 118140960795 + 958893 * 2 ^ 59
def prefixEnd_958893 : Nat := 4983230072969 + 3 ^ 40 * 958893 * 2
def baseEnd_958893 : Nat := 145888297846465795682263

theorem tailTrace_958893 : CollatzResearch.WordTrace tailWord_958893 prefixEnd_958893 145888297846465795682263 := by
  unfold tailWord_958893
  simp only [CollatzResearch.WordTrace]
  refine ⟨34973700915101901731441333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23315800610067934487627555 34973700915101901731441333)
  ·
    refine ⟨3278784460790803287322625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34973700915101901731441333 3278784460790803287322625)
    ·
      refine ⟨2459088345593102465491969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3278784460790803287322625 2459088345593102465491969)
      ·
        refine ⟨1844316259194826849118977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2459088345593102465491969 1844316259194826849118977)
        ·
          refine ⟨1383237194396120136839233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1844316259194826849118977 1383237194396120136839233)
          ·
            refine ⟨1037427895797090102629425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383237194396120136839233 1037427895797090102629425)
            ·
              refine ⟨778070921847817576972069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037427895797090102629425 778070921847817576972069)
              ·
                refine ⟨145888297846465795682263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778070921847817576972069 145888297846465795682263)
                ·
                  rfl

theorem cell20_958893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 4].length) (baseStart_958893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958893 prefixEnd_958893 := by exact prefixLift 958893
  have htrace : WordTrace (prefixWord ++ tailWord_958893) baseStart_958893 baseEnd_958893 := by
    simpa [prefixWord, tailWord_958893, baseEnd_958893] using wordTrace_append hprefix tailTrace_958893
  have hstable : (prefixWord ++ tailWord_958893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958893).length < 2 ^ (prefixWord ++ tailWord_958893).sum := by decide
  have hdescent : baseEnd_958893 < baseStart_958893 := by decide
  rcases family_descends (prefixWord ++ tailWord_958893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958897 : List Nat := [1, 2, 2, 4, 1, 2, 4, 4]
def baseStart_958897 : Nat := 118140960795 + 958897 * 2 ^ 59
def prefixEnd_958897 : Nat := 4983230072969 + 3 ^ 40 * 958897 * 2
def baseEnd_958897 : Nat := 145888906416130383637813

theorem tailTrace_958897 : CollatzResearch.WordTrace tailWord_958897 prefixEnd_958897 145888906416130383637813 := by
  unfold tailWord_958897
  simp only [CollatzResearch.WordTrace]
  refine ⟨34973846807087410414586945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23315897871391606943057963 34973846807087410414586945)
  ·
    refine ⟨26230385105315557810940209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34973846807087410414586945 26230385105315557810940209)
    ·
      refine ⟨19672788828986668358205157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26230385105315557810940209 19672788828986668358205157)
      ·
        refine ⟨3688647905435000317163467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19672788828986668358205157 3688647905435000317163467)
        ·
          refine ⟨5532971858152500475745201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688647905435000317163467 5532971858152500475745201)
          ·
            refine ⟨4149728893614375356808901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5532971858152500475745201 4149728893614375356808901)
            ·
              refine ⟨778074167552695379401669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4149728893614375356808901 778074167552695379401669)
              ·
                refine ⟨145888906416130383637813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778074167552695379401669 145888906416130383637813)
                ·
                  rfl

theorem cell20_958897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 4].length) (baseStart_958897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958897 prefixEnd_958897 := by exact prefixLift 958897
  have htrace : WordTrace (prefixWord ++ tailWord_958897) baseStart_958897 baseEnd_958897 := by
    simpa [prefixWord, tailWord_958897, baseEnd_958897] using wordTrace_append hprefix tailTrace_958897
  have hstable : (prefixWord ++ tailWord_958897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958897).length < 2 ^ (prefixWord ++ tailWord_958897).sum := by decide
  have hdescent : baseEnd_958897 < baseStart_958897 := by decide
  rcases family_descends (prefixWord ++ tailWord_958897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958924 : List Nat := [2, 2, 1, 4, 3, 1, 3, 2, 2]
def baseStart_958924 : Nat := 118140960795 + 958924 * 2 ^ 59
def prefixEnd_958924 : Nat := 4983230072969 + 3 ^ 40 * 958924 * 2
def baseEnd_958924 : Nat := 437679042784099057013329

theorem tailTrace_958924 : CollatzResearch.WordTrace tailWord_958924 prefixEnd_958924 437679042784099057013329 := by
  unfold tailWord_958924
  simp only [CollatzResearch.WordTrace]
  refine ⟨17487415788994797012909913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23316554385326396017213217 17487415788994797012909913)
  ·
    refine ⟨13115561841746097759682435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17487415788994797012909913 13115561841746097759682435)
    ·
      refine ⟨19673342762619146639523653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13115561841746097759682435 19673342762619146639523653)
      ·
        refine ⟨3688751767991089994910685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19673342762619146639523653 3688751767991089994910685)
        ·
          refine ⟨1383281912996658748091507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3688751767991089994910685 1383281912996658748091507)
          ·
            refine ⟨2074922869494988122137261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383281912996658748091507 2074922869494988122137261)
            ·
              refine ⟨778096076060620545801473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2074922869494988122137261 778096076060620545801473)
              ·
                refine ⟨583572057045465409351105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778096076060620545801473 583572057045465409351105)
                ·
                  refine ⟨437679042784099057013329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583572057045465409351105 437679042784099057013329)
                  ·
                    rfl

theorem cell20_958924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_958924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958924 prefixEnd_958924 := by exact prefixLift 958924
  have htrace : WordTrace (prefixWord ++ tailWord_958924) baseStart_958924 baseEnd_958924 := by
    simpa [prefixWord, tailWord_958924, baseEnd_958924] using wordTrace_append hprefix tailTrace_958924
  have hstable : (prefixWord ++ tailWord_958924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958924).length < 2 ^ (prefixWord ++ tailWord_958924).sum := by decide
  have hdescent : baseEnd_958924 < baseStart_958924 := by decide
  rcases family_descends (prefixWord ++ tailWord_958924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958970 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_958970 : Nat := 118140960795 + 958970 * 2 ^ 59
def prefixEnd_958970 : Nat := 4983230072969 + 3 ^ 40 * 958970 * 2
def baseEnd_958970 : Nat := 437700038437527341479807

theorem tailTrace_958970 : CollatzResearch.WordTrace tailWord_958970 prefixEnd_958970 437700038437527341479807 := by
  unfold tailWord_958970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8744127333955735970498591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23317672890548629254662909 8744127333955735970498591)
  ·
    refine ⟨13116191000933603955747887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8744127333955735970498591 13116191000933603955747887)
    ·
      refine ⟨19674286501400405933621831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13116191000933603955747887 19674286501400405933621831)
      ·
        refine ⟨29511429752100608900432747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19674286501400405933621831 29511429752100608900432747)
        ·
          refine ⟨44267144628150913350649121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29511429752100608900432747 44267144628150913350649121)
          ·
            refine ⟨33200358471113185012986841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44267144628150913350649121 33200358471113185012986841)
            ·
              refine ⟨24900268853334888759740131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33200358471113185012986841 24900268853334888759740131)
              ·
                refine ⟨37350403280002333139610197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24900268853334888759740131 37350403280002333139610197)
                ·
                  refine ⟨437700038437527341479807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37350403280002333139610197 437700038437527341479807)
                  ·
                    rfl

theorem cell20_958970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_958970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958970 prefixEnd_958970 := by exact prefixLift 958970
  have htrace : WordTrace (prefixWord ++ tailWord_958970) baseStart_958970 baseEnd_958970 := by
    simpa [prefixWord, tailWord_958970, baseEnd_958970] using wordTrace_append hprefix tailTrace_958970
  have hstable : (prefixWord ++ tailWord_958970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958970).length < 2 ^ (prefixWord ++ tailWord_958970).sum := by decide
  have hdescent : baseEnd_958970 < baseStart_958970 := by decide
  rcases family_descends (prefixWord ++ tailWord_958970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958983 : List Nat := [1, 1, 4, 3, 3, 1, 1, 4, 2]
def baseStart_958983 : Nat := 118140960795 + 958983 * 2 ^ 59
def prefixEnd_958983 : Nat := 4983230072969 + 3 ^ 40 * 958983 * 2
def baseEnd_958983 : Nat := 437705971991757074046421

theorem tailTrace_958983 : CollatzResearch.WordTrace tailWord_958983 prefixEnd_958983 437705971991757074046421 := by
  unfold tailWord_958983
  simp only [CollatzResearch.WordTrace]
  refine ⟨34976983484775847102217603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23317988989850564734811735 34976983484775847102217603)
  ·
    refine ⟨52465475227163770653326405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34976983484775847102217603 52465475227163770653326405)
    ·
      refine ⟨9837276605093206997498701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52465475227163770653326405 9837276605093206997498701)
      ·
        refine ⟨3688978726909952624062013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9837276605093206997498701 3688978726909952624062013)
        ·
          refine ⟨1383367022591232234023255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3688978726909952624062013 1383367022591232234023255)
          ·
            refine ⟨2075050533886848351034883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383367022591232234023255 2075050533886848351034883)
            ·
              refine ⟨3112575800830272526552325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075050533886848351034883 3112575800830272526552325)
              ·
                refine ⟨583607962655676098728561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3112575800830272526552325 583607962655676098728561)
                ·
                  refine ⟨437705971991757074046421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583607962655676098728561 437705971991757074046421)
                  ·
                    rfl

theorem cell20_958983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 2].length) (baseStart_958983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_958983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_958983 prefixEnd_958983 := by exact prefixLift 958983
  have htrace : WordTrace (prefixWord ++ tailWord_958983) baseStart_958983 baseEnd_958983 := by
    simpa [prefixWord, tailWord_958983, baseEnd_958983] using wordTrace_append hprefix tailTrace_958983
  have hstable : (prefixWord ++ tailWord_958983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958983).length < 2 ^ (prefixWord ++ tailWord_958983).sum := by decide
  have hdescent : baseEnd_958983 < baseStart_958983 := by decide
  rcases family_descends (prefixWord ++ tailWord_958983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959011 : List Nat := [1, 1, 1, 4, 4, 2, 3, 4]
def baseStart_959011 : Nat := 118140960795 + 959011 * 2 ^ 59
def prefixEnd_959011 : Nat := 4983230072969 + 3 ^ 40 * 959011 * 2
def baseEnd_959011 : Nat := 145906250651571140370991

theorem tailTrace_959011 : CollatzResearch.WordTrace tailWord_959011 prefixEnd_959011 145906250651571140370991 := by
  unfold tailWord_959011
  simp only [CollatzResearch.WordTrace]
  refine ⟨34978004728674407884236887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23318669819116271922824591 34978004728674407884236887)
  ·
    refine ⟨52467007093011611826355331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34978004728674407884236887 52467007093011611826355331)
    ·
      refine ⟨78700510639517417739532997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52467007093011611826355331 78700510639517417739532997)
      ·
        refine ⟨14756345744909515826162437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78700510639517417739532997 14756345744909515826162437)
        ·
          refine ⟨2766814827170534217405457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14756345744909515826162437 2766814827170534217405457)
          ·
            refine ⟨2075111120377900663054093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2766814827170534217405457 2075111120377900663054093)
            ·
              refine ⟨778166670141712748645285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2075111120377900663054093 778166670141712748645285)
              ·
                refine ⟨145906250651571140370991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778166670141712748645285 145906250651571140370991)
                ·
                  rfl

theorem cell20_959011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 4].length) (baseStart_959011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959011 prefixEnd_959011 := by exact prefixLift 959011
  have htrace : WordTrace (prefixWord ++ tailWord_959011) baseStart_959011 baseEnd_959011 := by
    simpa [prefixWord, tailWord_959011, baseEnd_959011] using wordTrace_append hprefix tailTrace_959011
  have hstable : (prefixWord ++ tailWord_959011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959011).length < 2 ^ (prefixWord ++ tailWord_959011).sum := by decide
  have hdescent : baseEnd_959011 < baseStart_959011 := by decide
  rcases family_descends (prefixWord ++ tailWord_959011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959028 : List Nat := [2, 5, 1, 3, 1, 1, 7]
def baseStart_959028 : Nat := 118140960795 + 959028 * 2 ^ 59
def prefixEnd_959028 : Nat := 4983230072969 + 3 ^ 40 * 959028 * 2
def baseEnd_959028 : Nat := 48636279024215213060693

theorem tailTrace_959028 : CollatzResearch.WordTrace tailWord_959028 prefixEnd_959028 48636279024215213060693 := by
  unfold tailWord_959028
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489312384806409893802869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23319083179741879858403825 17489312384806409893802869)
  ·
    refine ⟨1639623036075600927544019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17489312384806409893802869 1639623036075600927544019)
    ·
      refine ⟨2459434554113401391316029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1639623036075600927544019 2459434554113401391316029)
      ·
        refine ⟨922287957792525521743511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2459434554113401391316029 922287957792525521743511)
        ·
          refine ⟨1383431936688788282615267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922287957792525521743511 1383431936688788282615267)
          ·
            refine ⟨2075147905033182423922901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383431936688788282615267 2075147905033182423922901)
            ·
              refine ⟨48636279024215213060693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2075147905033182423922901 48636279024215213060693)
              ·
                rfl

theorem cell20_959028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 7].length) (baseStart_959028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959028 prefixEnd_959028 := by exact prefixLift 959028
  have htrace : WordTrace (prefixWord ++ tailWord_959028) baseStart_959028 baseEnd_959028 := by
    simpa [prefixWord, tailWord_959028, baseEnd_959028] using wordTrace_append hprefix tailTrace_959028
  have hstable : (prefixWord ++ tailWord_959028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959028).length < 2 ^ (prefixWord ++ tailWord_959028).sum := by decide
  have hdescent : baseEnd_959028 < baseStart_959028 := by decide
  rcases family_descends (prefixWord ++ tailWord_959028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959039 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_959039 : Nat := 118140960795 + 959039 * 2 ^ 59
def prefixEnd_959039 : Nat := 4983230072969 + 3 ^ 40 * 959039 * 2
def baseEnd_959039 : Nat := 437731531917669768179525

theorem tailTrace_959039 : CollatzResearch.WordTrace tailWord_959039 prefixEnd_959039 437731531917669768179525 := by
  unfold tailWord_959039
  simp only [CollatzResearch.WordTrace]
  refine ⟨34979025972572968666256171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23319350648381979110837447 34979025972572968666256171)
  ·
    refine ⟨52468538958859452999384257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34979025972572968666256171 52468538958859452999384257)
    ·
      refine ⟨39351404219144589749538193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52468538958859452999384257 39351404219144589749538193)
      ·
        refine ⟨29513553164358442312153645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39351404219144589749538193 29513553164358442312153645)
        ·
          refine ⟨11067582436634415867057617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29513553164358442312153645 11067582436634415867057617)
          ·
            refine ⟨8300686827475811900293213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11067582436634415867057617 8300686827475811900293213)
            ·
              refine ⟨3112757560303429462609955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8300686827475811900293213 3112757560303429462609955)
              ·
                refine ⟨4669136340455144193914933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112757560303429462609955 4669136340455144193914933)
                ·
                  refine ⟨437731531917669768179525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4669136340455144193914933 437731531917669768179525)
                  ·
                    rfl

theorem cell20_959039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_959039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959039 prefixEnd_959039 := by exact prefixLift 959039
  have htrace : WordTrace (prefixWord ++ tailWord_959039) baseStart_959039 baseEnd_959039 := by
    simpa [prefixWord, tailWord_959039, baseEnd_959039] using wordTrace_append hprefix tailTrace_959039
  have hstable : (prefixWord ++ tailWord_959039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959039).length < 2 ^ (prefixWord ++ tailWord_959039).sum := by decide
  have hdescent : baseEnd_959039 < baseStart_959039 := by decide
  rcases family_descends (prefixWord ++ tailWord_959039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959084 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_959084 : Nat := 118140960795 + 959084 * 2 ^ 59
def prefixEnd_959084 : Nat := 4983230072969 + 3 ^ 40 * 959084 * 2
def baseEnd_959084 : Nat := 437752071143849611679341

theorem tailTrace_959084 : CollatzResearch.WordTrace tailWord_959084 prefixEnd_959084 437752071143849611679341 := by
  unfold tailWord_959084
  simp only [CollatzResearch.WordTrace]
  refine ⟨17490333628704970675822153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23320444838273294234429537 17490333628704970675822153)
  ·
    refine ⟨13117750221528728006866615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17490333628704970675822153 13117750221528728006866615)
    ·
      refine ⟨19676625332293092010299923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13117750221528728006866615 19676625332293092010299923)
      ·
        refine ⟨29514937998439638015449885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19676625332293092010299923 29514937998439638015449885)
        ·
          refine ⟨11068101749414864255793707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29514937998439638015449885 11068101749414864255793707)
          ·
            refine ⟨16602152624122296383690561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068101749414864255793707 16602152624122296383690561)
            ·
              refine ⟨12451614468091722287767921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16602152624122296383690561 12451614468091722287767921)
              ·
                refine ⟨9338710851068791715825941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12451614468091722287767921 9338710851068791715825941)
                ·
                  refine ⟨437752071143849611679341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9338710851068791715825941 437752071143849611679341)
                  ·
                    rfl

theorem cell20_959084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_959084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959084 prefixEnd_959084 := by exact prefixLift 959084
  have htrace : WordTrace (prefixWord ++ tailWord_959084) baseStart_959084 baseEnd_959084 := by
    simpa [prefixWord, tailWord_959084, baseEnd_959084] using wordTrace_append hprefix tailTrace_959084
  have hstable : (prefixWord ++ tailWord_959084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959084).length < 2 ^ (prefixWord ++ tailWord_959084).sum := by decide
  have hdescent : baseEnd_959084 < baseStart_959084 := by decide
  rcases family_descends (prefixWord ++ tailWord_959084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959097 : List Nat := [1, 2, 1, 3, 3, 3, 3, 2, 2]
def baseStart_959097 : Nat := 118140960795 + 959097 * 2 ^ 59
def prefixEnd_959097 : Nat := 4983230072969 + 3 ^ 40 * 959097 * 2
def baseEnd_959097 : Nat := 437758004698079344245955

theorem tailTrace_959097 : CollatzResearch.WordTrace tailWord_959097 prefixEnd_959097 437758004698079344245955 := by
  unfold tailWord_959097
  simp only [CollatzResearch.WordTrace]
  refine ⟨34981141406362844571867545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23320760937575229714578363 34981141406362844571867545)
  ·
    refine ⟨26235856054772133428900659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34981141406362844571867545 26235856054772133428900659)
    ·
      refine ⟨39353784082158200143350989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26235856054772133428900659 39353784082158200143350989)
      ·
        refine ⟨14757669030809325053756621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39353784082158200143350989 14757669030809325053756621)
        ·
          refine ⟨5534125886553496895158733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14757669030809325053756621 5534125886553496895158733)
          ·
            refine ⟨2075297207457561335684525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5534125886553496895158733 2075297207457561335684525)
            ·
              refine ⟨778236452796585500881697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2075297207457561335684525 778236452796585500881697)
              ·
                refine ⟨583677339597439125661273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778236452796585500881697 583677339597439125661273)
                ·
                  refine ⟨437758004698079344245955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583677339597439125661273 437758004698079344245955)
                  ·
                    rfl

theorem cell20_959097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_959097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959097 prefixEnd_959097 := by exact prefixLift 959097
  have htrace : WordTrace (prefixWord ++ tailWord_959097) baseStart_959097 baseEnd_959097 := by
    simpa [prefixWord, tailWord_959097, baseEnd_959097] using wordTrace_append hprefix tailTrace_959097
  have hstable : (prefixWord ++ tailWord_959097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959097).length < 2 ^ (prefixWord ++ tailWord_959097).sum := by decide
  have hdescent : baseEnd_959097 < baseStart_959097 := by decide
  rcases family_descends (prefixWord ++ tailWord_959097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959108 : List Nat := [2, 3, 2, 1, 3, 1, 1, 7]
def baseStart_959108 : Nat := 118140960795 + 959108 * 2 ^ 59
def prefixEnd_959108 : Nat := 4983230072969 + 3 ^ 40 * 959108 * 2
def baseEnd_959108 : Nat := 145921008465937398293081

theorem tailTrace_959108 : CollatzResearch.WordTrace tailWord_959108 prefixEnd_959108 145921008465937398293081 := by
  unfold tailWord_959108
  simp only [CollatzResearch.WordTrace]
  refine ⟨17490771304661496725258989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23321028406215328967011985 17490771304661496725258989)
  ·
    refine ⟨6559039239248061271972121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17490771304661496725258989 6559039239248061271972121)
    ·
      refine ⟨4919279429436045953979091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6559039239248061271972121 4919279429436045953979091)
      ·
        refine ⟨7378919144154068930968637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919279429436045953979091 7378919144154068930968637)
        ·
          refine ⟨2767094679057775849113239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7378919144154068930968637 2767094679057775849113239)
          ·
            refine ⟨4150642018586663773669859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767094679057775849113239 4150642018586663773669859)
            ·
              refine ⟨6225963027879995660504789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150642018586663773669859 6225963027879995660504789)
              ·
                refine ⟨145921008465937398293081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6225963027879995660504789 145921008465937398293081)
                ·
                  rfl

theorem cell20_959108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_959108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959108 prefixEnd_959108 := by exact prefixLift 959108
  have htrace : WordTrace (prefixWord ++ tailWord_959108) baseStart_959108 baseEnd_959108 := by
    simpa [prefixWord, tailWord_959108, baseEnd_959108] using wordTrace_append hprefix tailTrace_959108
  have hstable : (prefixWord ++ tailWord_959108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959108).length < 2 ^ (prefixWord ++ tailWord_959108).sum := by decide
  have hdescent : baseEnd_959108 < baseStart_959108 := by decide
  rcases family_descends (prefixWord ++ tailWord_959108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959129 : List Nat := [1, 2, 1, 2, 1, 2, 3, 8]
def baseStart_959129 : Nat := 118140960795 + 959129 * 2 ^ 59
def prefixEnd_959129 : Nat := 4983230072969 + 3 ^ 40 * 959129 * 2
def baseEnd_959129 : Nat := 145924203456676485059719

theorem tailTrace_959129 : CollatzResearch.WordTrace tailWord_959129 prefixEnd_959129 145924203456676485059719 := by
  unfold tailWord_959129
  simp only [CollatzResearch.WordTrace]
  refine ⟨34982308542246914037032441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23321539028164609358021627 34982308542246914037032441)
  ·
    refine ⟨26236731406685185527774331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34982308542246914037032441 26236731406685185527774331)
    ·
      refine ⟨39355097110027778291661497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26236731406685185527774331 39355097110027778291661497)
      ·
        refine ⟨29516322832520833718746123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39355097110027778291661497 29516322832520833718746123)
        ·
          refine ⟨44274484248781250578119185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29516322832520833718746123 44274484248781250578119185)
          ·
            refine ⟨33205863186585937933589389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44274484248781250578119185 33205863186585937933589389)
            ·
              refine ⟨12452198694969726725096021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33205863186585937933589389 12452198694969726725096021)
              ·
                refine ⟨145924203456676485059719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12452198694969726725096021 145924203456676485059719)
                ·
                  rfl

theorem cell20_959129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_959129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959129 prefixEnd_959129 := by exact prefixLift 959129
  have htrace : WordTrace (prefixWord ++ tailWord_959129) baseStart_959129 baseEnd_959129 := by
    simpa [prefixWord, tailWord_959129, baseEnd_959129] using wordTrace_append hprefix tailTrace_959129
  have hstable : (prefixWord ++ tailWord_959129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959129).length < 2 ^ (prefixWord ++ tailWord_959129).sum := by decide
  have hdescent : baseEnd_959129 < baseStart_959129 := by decide
  rcases family_descends (prefixWord ++ tailWord_959129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959149 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 3]
def baseStart_959149 : Nat := 118140960795 + 959149 * 2 ^ 59
def prefixEnd_959149 : Nat := 4983230072969 + 3 ^ 40 * 959149 * 2
def baseEnd_959149 : Nat := 437781738914998274512409

theorem tailTrace_959149 : CollatzResearch.WordTrace tailWord_959149 prefixEnd_959149 437781738914998274512409 := by
  unfold tailWord_959149
  simp only [CollatzResearch.WordTrace]
  refine ⟨34983038002174457452760501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23322025334782971635173667 34983038002174457452760501)
  ·
    refine ⟨3279659812703855386196297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34983038002174457452760501 3279659812703855386196297)
    ·
      refine ⟨2459744859527891539647223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3279659812703855386196297 2459744859527891539647223)
      ·
        refine ⟨3689617289291837309470835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459744859527891539647223 3689617289291837309470835)
        ·
          refine ⟨5534425933937755964206253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689617289291837309470835 5534425933937755964206253)
          ·
            refine ⟨2075409725226658486577345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5534425933937755964206253 2075409725226658486577345)
            ·
              refine ⟨1556557293919993864933009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075409725226658486577345 1556557293919993864933009)
              ·
                refine ⟨1167417970439995398699757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556557293919993864933009 1167417970439995398699757)
                ·
                  refine ⟨437781738914998274512409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167417970439995398699757 437781738914998274512409)
                  ·
                    rfl

theorem cell20_959149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_959149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959149 prefixEnd_959149 := by exact prefixLift 959149
  have htrace : WordTrace (prefixWord ++ tailWord_959149) baseStart_959149 baseEnd_959149 := by
    simpa [prefixWord, tailWord_959149, baseEnd_959149] using wordTrace_append hprefix tailTrace_959149
  have hstable : (prefixWord ++ tailWord_959149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959149).length < 2 ^ (prefixWord ++ tailWord_959149).sum := by decide
  have hdescent : baseEnd_959149 < baseStart_959149 := by decide
  rcases family_descends (prefixWord ++ tailWord_959149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959194 : List Nat := [3, 1, 1, 2, 2, 2, 4, 3, 2]
def baseStart_959194 : Nat := 118140960795 + 959194 * 2 ^ 59
def prefixEnd_959194 : Nat := 4983230072969 + 3 ^ 40 * 959194 * 2
def baseEnd_959194 : Nat := 437802278141178118012225

theorem tailTrace_959194 : CollatzResearch.WordTrace tailWord_959194 prefixEnd_959194 437802278141178118012225 := by
  unfold tailWord_959194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8746169821752857534537159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23323119524674286758765757 8746169821752857534537159)
  ·
    refine ⟨13119254732629286301805739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8746169821752857534537159 13119254732629286301805739)
    ·
      refine ⟨19678882098943929452708609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13119254732629286301805739 19678882098943929452708609)
      ·
        refine ⟨14759161574207947089531457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19678882098943929452708609 14759161574207947089531457)
        ·
          refine ⟨11069371180655960317148593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14759161574207947089531457 11069371180655960317148593)
          ·
            refine ⟨8302028385491970237861445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11069371180655960317148593 8302028385491970237861445)
            ·
              refine ⟨1556630322279744419599021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8302028385491970237861445 1556630322279744419599021)
              ·
                refine ⟨583736370854904157349633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1556630322279744419599021 583736370854904157349633)
                ·
                  refine ⟨437802278141178118012225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583736370854904157349633 437802278141178118012225)
                  ·
                    rfl

theorem cell20_959194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_959194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959194 prefixEnd_959194 := by exact prefixLift 959194
  have htrace : WordTrace (prefixWord ++ tailWord_959194) baseStart_959194 baseEnd_959194 := by
    simpa [prefixWord, tailWord_959194, baseEnd_959194] using wordTrace_append hprefix tailTrace_959194
  have hstable : (prefixWord ++ tailWord_959194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959194).length < 2 ^ (prefixWord ++ tailWord_959194).sum := by decide
  have hdescent : baseEnd_959194 < baseStart_959194 := by decide
  rcases family_descends (prefixWord ++ tailWord_959194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959208 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 5]
def baseStart_959208 : Nat := 118140960795 + 959208 * 2 ^ 59
def prefixEnd_959208 : Nat := 4983230072969 + 3 ^ 40 * 959208 * 2
def baseEnd_959208 : Nat := 437808668122656291545501

theorem tailTrace_959208 : CollatzResearch.WordTrace tailWord_959208 prefixEnd_959208 437808668122656291545501 := by
  unfold tailWord_959208
  simp only [CollatzResearch.WordTrace]
  refine ⟨17492594954480355264579139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23323459939307140352772185 17492594954480355264579139)
  ·
    refine ⟨26238892431720532896868709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17492594954480355264579139 26238892431720532896868709)
    ·
      refine ⟨4919792330947599918162883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26238892431720532896868709 4919792330947599918162883)
      ·
        refine ⟨7379688496421399877244325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919792330947599918162883 7379688496421399877244325)
        ·
          refine ⟨1383691593079012476983311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7379688496421399877244325 1383691593079012476983311)
          ·
            refine ⟨2075537389618518715474967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383691593079012476983311 2075537389618518715474967)
            ·
              refine ⟨3113306084427778073212451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075537389618518715474967 3113306084427778073212451)
              ·
                refine ⟨4669959126641667109818677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113306084427778073212451 4669959126641667109818677)
                ·
                  refine ⟨437808668122656291545501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4669959126641667109818677 437808668122656291545501)
                  ·
                    rfl

theorem cell20_959208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_959208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959208 prefixEnd_959208 := by exact prefixLift 959208
  have htrace : WordTrace (prefixWord ++ tailWord_959208) baseStart_959208 baseEnd_959208 := by
    simpa [prefixWord, tailWord_959208, baseEnd_959208] using wordTrace_append hprefix tailTrace_959208
  have hstable : (prefixWord ++ tailWord_959208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959208).length < 2 ^ (prefixWord ++ tailWord_959208).sum := by decide
  have hdescent : baseEnd_959208 < baseStart_959208 := by decide
  rcases family_descends (prefixWord ++ tailWord_959208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959215 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 4]
def baseStart_959215 : Nat := 118140960795 + 959215 * 2 ^ 59
def prefixEnd_959215 : Nat := 4983230072969 + 3 ^ 40 * 959215 * 2
def baseEnd_959215 : Nat := 437811863113395378312139

theorem tailTrace_959215 : CollatzResearch.WordTrace tailWord_959215 prefixEnd_959215 437811863113395378312139 := by
  unfold tailWord_959215
  simp only [CollatzResearch.WordTrace]
  refine ⟨34985445219935350724663099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23323630146623567149775399 34985445219935350724663099)
  ·
    refine ⟨52478167829903026086994649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34985445219935350724663099 52478167829903026086994649)
    ·
      refine ⟨39358625872427269565245987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52478167829903026086994649 39358625872427269565245987)
      ·
        refine ⟨59037938808640904347868981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39358625872427269565245987 59037938808640904347868981)
        ·
          refine ⟨5534806763310084782612717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59037938808640904347868981 5534806763310084782612717)
          ·
            refine ⟨2075552536241281793479769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5534806763310084782612717 2075552536241281793479769)
            ·
              refine ⟨1556664402180961345109827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075552536241281793479769 1556664402180961345109827)
              ·
                refine ⟨2334996603271442017664741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556664402180961345109827 2334996603271442017664741)
                ·
                  refine ⟨437811863113395378312139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334996603271442017664741 437811863113395378312139)
                  ·
                    rfl

theorem cell20_959215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_959215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959215 prefixEnd_959215 := by exact prefixLift 959215
  have htrace : WordTrace (prefixWord ++ tailWord_959215) baseStart_959215 baseEnd_959215 := by
    simpa [prefixWord, tailWord_959215, baseEnd_959215] using wordTrace_append hprefix tailTrace_959215
  have hstable : (prefixWord ++ tailWord_959215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959215).length < 2 ^ (prefixWord ++ tailWord_959215).sum := by decide
  have hdescent : baseEnd_959215 < baseStart_959215 := by decide
  rcases family_descends (prefixWord ++ tailWord_959215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959222 : List Nat := [5, 1, 1, 1, 1, 2, 2, 7]
def baseStart_959222 : Nat := 118140960795 + 959222 * 2 ^ 59
def prefixEnd_959222 : Nat := 4983230072969 + 3 ^ 40 * 959222 * 2
def baseEnd_959222 : Nat := 145938352701378155026259

theorem tailTrace_959222 : CollatzResearch.WordTrace tailWord_959222 prefixEnd_959222 145938352701378155026259 := by
  unfold tailWord_959222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2186606283181874432510495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23323800353939993946778613 2186606283181874432510495)
  ·
    refine ⟨3279909424772811648765743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2186606283181874432510495 3279909424772811648765743)
    ·
      refine ⟨4919864137159217473148615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3279909424772811648765743 4919864137159217473148615)
      ·
        refine ⟨7379796205738826209722923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919864137159217473148615 7379796205738826209722923)
        ·
          refine ⟨11069694308608239314584385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379796205738826209722923 11069694308608239314584385)
          ·
            refine ⟨8302270731456179485938289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11069694308608239314584385 8302270731456179485938289)
            ·
              refine ⟨6226703048592134614453717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8302270731456179485938289 6226703048592134614453717)
              ·
                refine ⟨145938352701378155026259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6226703048592134614453717 145938352701378155026259)
                ·
                  rfl

theorem cell20_959222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_959222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959222 prefixEnd_959222 := by exact prefixLift 959222
  have htrace : WordTrace (prefixWord ++ tailWord_959222) baseStart_959222 baseEnd_959222 := by
    simpa [prefixWord, tailWord_959222, baseEnd_959222] using wordTrace_append hprefix tailTrace_959222
  have hstable : (prefixWord ++ tailWord_959222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959222).length < 2 ^ (prefixWord ++ tailWord_959222).sum := by decide
  have hdescent : baseEnd_959222 < baseStart_959222 := by decide
  rcases family_descends (prefixWord ++ tailWord_959222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959239 : List Nat := [1, 1, 4, 4, 1, 1, 4, 4]
def baseStart_959239 : Nat := 118140960795 + 959239 * 2 ^ 59
def prefixEnd_959239 : Nat := 4983230072969 + 3 ^ 40 * 959239 * 2
def baseEnd_959239 : Nat := 145940939122452653837347

theorem tailTrace_959239 : CollatzResearch.WordTrace tailWord_959239 prefixEnd_959239 145940939122452653837347 := by
  unfold tailWord_959239
  simp only [CollatzResearch.WordTrace]
  refine ⟨34986320571848402823536771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23324213714565601882357847 34986320571848402823536771)
  ·
    refine ⟨52479480857772604235305157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34986320571848402823536771 52479480857772604235305157)
    ·
      refine ⟨9839902660832363294119717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52479480857772604235305157 9839902660832363294119717)
      ·
        refine ⟨1844981748906068117647447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9839902660832363294119717 1844981748906068117647447)
        ·
          refine ⟨2767472623359102176471171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844981748906068117647447 2767472623359102176471171)
          ·
            refine ⟨4151208935038653264706757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767472623359102176471171 4151208935038653264706757)
            ·
              refine ⟨778351675319747487132517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4151208935038653264706757 778351675319747487132517)
              ·
                refine ⟨145940939122452653837347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778351675319747487132517 145940939122452653837347)
                ·
                  rfl

theorem cell20_959239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 4].length) (baseStart_959239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959239 prefixEnd_959239 := by exact prefixLift 959239
  have htrace : WordTrace (prefixWord ++ tailWord_959239) baseStart_959239 baseEnd_959239 := by
    simpa [prefixWord, tailWord_959239, baseEnd_959239] using wordTrace_append hprefix tailTrace_959239
  have hstable : (prefixWord ++ tailWord_959239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959239).length < 2 ^ (prefixWord ++ tailWord_959239).sum := by decide
  have hdescent : baseEnd_959239 < baseStart_959239 := by decide
  rcases family_descends (prefixWord ++ tailWord_959239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959260 : List Nat := [2, 2, 3, 1, 1, 5, 6]
def baseStart_959260 : Nat := 118140960795 + 959260 * 2 ^ 59
def prefixEnd_959260 : Nat := 4983230072969 + 3 ^ 40 * 959260 * 2
def baseEnd_959260 : Nat := 48648044704397246867995

theorem tailTrace_959260 : CollatzResearch.WordTrace tailWord_959260 prefixEnd_959260 48648044704397246867995 := by
  unfold tailWord_959260
  simp only [CollatzResearch.WordTrace]
  refine ⟨17493543252386161705025617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23324724336514882273367489 17493543252386161705025617)
  ·
    refine ⟨13120157439289621278769213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17493543252386161705025617 13120157439289621278769213)
    ·
      refine ⟨4920059039733607979538455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13120157439289621278769213 4920059039733607979538455)
      ·
        refine ⟨7380088559600411969307683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4920059039733607979538455 7380088559600411969307683)
        ·
          refine ⟨11070132839400617953961525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380088559600411969307683 11070132839400617953961525)
          ·
            refine ⟨1037824953693807933183893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11070132839400617953961525 1037824953693807933183893)
            ·
              refine ⟨48648044704397246867995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1037824953693807933183893 48648044704397246867995)
              ·
                rfl

theorem cell20_959260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 6].length) (baseStart_959260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959260 prefixEnd_959260 := by exact prefixLift 959260
  have htrace : WordTrace (prefixWord ++ tailWord_959260) baseStart_959260 baseEnd_959260 := by
    simpa [prefixWord, tailWord_959260, baseEnd_959260] using wordTrace_append hprefix tailTrace_959260
  have hstable : (prefixWord ++ tailWord_959260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959260).length < 2 ^ (prefixWord ++ tailWord_959260).sum := by decide
  have hdescent : baseEnd_959260 < baseStart_959260 := by decide
  rcases family_descends (prefixWord ++ tailWord_959260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959267 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 3]
def baseStart_959267 : Nat := 118140960795 + 959267 * 2 ^ 59
def prefixEnd_959267 : Nat := 4983230072969 + 3 ^ 40 * 959267 * 2
def baseEnd_959267 : Nat := 437835597330314308578593

theorem tailTrace_959267 : CollatzResearch.WordTrace tailWord_959267 prefixEnd_959267 437835597330314308578593 := by
  unfold tailWord_959267
  simp only [CollatzResearch.WordTrace]
  refine ⟨34987341815746963605556055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23324894543831309070370703 34987341815746963605556055)
  ·
    refine ⟨52481012723620445408334083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34987341815746963605556055 52481012723620445408334083)
    ·
      refine ⟨78721519085430668112501125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52481012723620445408334083 78721519085430668112501125)
      ·
        refine ⟨14760284828518250271093961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78721519085430668112501125 14760284828518250271093961)
        ·
          refine ⟨11070213621388687703320471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14760284828518250271093961 11070213621388687703320471)
          ·
            refine ⟨16605320432083031554980707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11070213621388687703320471 16605320432083031554980707)
            ·
              refine ⟨24907980648124547332471061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16605320432083031554980707 24907980648124547332471061)
              ·
                refine ⟨1167561592880838156209581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24907980648124547332471061 1167561592880838156209581)
                ·
                  refine ⟨437835597330314308578593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167561592880838156209581 437835597330314308578593)
                  ·
                    rfl

theorem cell20_959267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 3].length) (baseStart_959267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959267 prefixEnd_959267 := by exact prefixLift 959267
  have htrace : WordTrace (prefixWord ++ tailWord_959267) baseStart_959267 baseEnd_959267 := by
    simpa [prefixWord, tailWord_959267, baseEnd_959267] using wordTrace_append hprefix tailTrace_959267
  have hstable : (prefixWord ++ tailWord_959267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959267).length < 2 ^ (prefixWord ++ tailWord_959267).sum := by decide
  have hdescent : baseEnd_959267 < baseStart_959267 := by decide
  rcases family_descends (prefixWord ++ tailWord_959267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959319 : List Nat := [1, 1, 3, 2, 4, 9]
def baseStart_959319 : Nat := 118140960795 + 959319 * 2 ^ 59
def prefixEnd_959319 : Nat := 4983230072969 + 3 ^ 40 * 959319 * 2
def baseEnd_959319 : Nat := 16217012279527156994261

theorem tailTrace_959319 : CollatzResearch.WordTrace tailWord_959319 prefixEnd_959319 16217012279527156994261 := by
  unfold tailWord_959319
  simp only [CollatzResearch.WordTrace]
  refine ⟨34989238411558576486449011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23326158941039050990966007 34989238411558576486449011)
  ·
    refine ⟨52483857617337864729673517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34989238411558576486449011 52483857617337864729673517)
    ·
      refine ⟨19681446606501699273627569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52483857617337864729673517 19681446606501699273627569)
      ·
        refine ⟨14761084954876274455220677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19681446606501699273627569 14761084954876274455220677)
        ·
          refine ⟨2767703429039301460353877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14761084954876274455220677 2767703429039301460353877)
          ·
            refine ⟨16217012279527156994261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2767703429039301460353877 16217012279527156994261)
            ·
              rfl

theorem cell20_959319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 9].length) (baseStart_959319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959319 prefixEnd_959319 := by exact prefixLift 959319
  have htrace : WordTrace (prefixWord ++ tailWord_959319) baseStart_959319 baseEnd_959319 := by
    simpa [prefixWord, tailWord_959319, baseEnd_959319] using wordTrace_append hprefix tailTrace_959319
  have hstable : (prefixWord ++ tailWord_959319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959319).length < 2 ^ (prefixWord ++ tailWord_959319).sum := by decide
  have hdescent : baseEnd_959319 < baseStart_959319 := by decide
  rcases family_descends (prefixWord ++ tailWord_959319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959322 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_959322 : Nat := 118140960795 + 959322 * 2 ^ 59
def prefixEnd_959322 : Nat := 4983230072969 + 3 ^ 40 * 959322 * 2
def baseEnd_959322 : Nat := 437860700828978561745035

theorem tailTrace_959322 : CollatzResearch.WordTrace tailWord_959322 prefixEnd_959322 437860700828978561745035 := by
  unfold tailWord_959322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8747336957636926999702055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23326231887031805332538813 8747336957636926999702055)
  ·
    refine ⟨13121005436455390499553083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8747336957636926999702055 13121005436455390499553083)
    ·
      refine ⟨19681508154683085749329625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13121005436455390499553083 19681508154683085749329625)
      ·
        refine ⟨14761131116012314311997219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19681508154683085749329625 14761131116012314311997219)
        ·
          refine ⟨22141696674018471467995829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14761131116012314311997219 22141696674018471467995829)
          ·
            refine ⟨2075784063189231700124609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22141696674018471467995829 2075784063189231700124609)
            ·
              refine ⟨1556838047391923775093457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075784063189231700124609 1556838047391923775093457)
              ·
                refine ⟨1167628535543942831320093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556838047391923775093457 1167628535543942831320093)
                ·
                  refine ⟨437860700828978561745035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167628535543942831320093 437860700828978561745035)
                  ·
                    rfl

theorem cell20_959322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_959322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959322 prefixEnd_959322 := by exact prefixLift 959322
  have htrace : WordTrace (prefixWord ++ tailWord_959322) baseStart_959322 baseEnd_959322 := by
    simpa [prefixWord, tailWord_959322, baseEnd_959322] using wordTrace_append hprefix tailTrace_959322
  have hstable : (prefixWord ++ tailWord_959322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959322).length < 2 ^ (prefixWord ++ tailWord_959322).sum := by decide
  have hdescent : baseEnd_959322 < baseStart_959322 := by decide
  rcases family_descends (prefixWord ++ tailWord_959322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959336 : List Nat := [2, 1, 4, 2, 1, 2, 3, 5]
def baseStart_959336 : Nat := 118140960795 + 959336 * 2 ^ 59
def prefixEnd_959336 : Nat := 4983230072969 + 3 ^ 40 * 959336 * 2
def baseEnd_959336 : Nat := 145955696936818911759437

theorem tailTrace_959336 : CollatzResearch.WordTrace tailWord_959336 prefixEnd_959336 145955696936818911759437 := by
  unfold tailWord_959336
  simp only [CollatzResearch.WordTrace]
  refine ⟨17494929226248494194908931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23326572301664658926545241 17494929226248494194908931)
  ·
    refine ⟨26242393839372741292363397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17494929226248494194908931 26242393839372741292363397)
    ·
      refine ⟨4920448844882388992318137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26242393839372741292363397 4920448844882388992318137)
      ·
        refine ⟨3690336633661791744238603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4920448844882388992318137 3690336633661791744238603)
        ·
          refine ⟨5535504950492687616357905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3690336633661791744238603 5535504950492687616357905)
          ·
            refine ⟨4151628712869515712268429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5535504950492687616357905 4151628712869515712268429)
            ·
              refine ⟨1556860767326068392100661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4151628712869515712268429 1556860767326068392100661)
              ·
                refine ⟨145955696936818911759437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1556860767326068392100661 145955696936818911759437)
                ·
                  rfl

theorem cell20_959336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_959336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959336 prefixEnd_959336 := by exact prefixLift 959336
  have htrace : WordTrace (prefixWord ++ tailWord_959336) baseStart_959336 baseEnd_959336 := by
    simpa [prefixWord, tailWord_959336, baseEnd_959336] using wordTrace_append hprefix tailTrace_959336
  have hstable : (prefixWord ++ tailWord_959336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959336).length < 2 ^ (prefixWord ++ tailWord_959336).sum := by decide
  have hdescent : baseEnd_959336 < baseStart_959336 := by decide
  rcases family_descends (prefixWord ++ tailWord_959336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959357 : List Nat := [1, 4, 1, 1, 2, 1, 2, 8]
def baseStart_959357 : Nat := 118140960795 + 959357 * 2 ^ 59
def prefixEnd_959357 : Nat := 4983230072969 + 3 ^ 40 * 959357 * 2
def baseEnd_959357 : Nat := 145958891927557998526075

theorem tailTrace_959357 : CollatzResearch.WordTrace tailWord_959357 prefixEnd_959357 145958891927557998526075 := by
  unfold tailWord_959357
  simp only [CollatzResearch.WordTrace]
  refine ⟨34990624385420908976332325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23327082923613939317554883 34990624385420908976332325)
  ·
    refine ⟨6560742072266420433062311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34990624385420908976332325 6560742072266420433062311)
    ·
      refine ⟨9841113108399630649593467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6560742072266420433062311 9841113108399630649593467)
      ·
        refine ⟨14761669662599445974390201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9841113108399630649593467 14761669662599445974390201)
        ·
          refine ⟨11071252246949584480792651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14761669662599445974390201 11071252246949584480792651)
          ·
            refine ⟨16606878370424376721188977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11071252246949584480792651 16606878370424376721188977)
            ·
              refine ⟨12455158777818282540891733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16606878370424376721188977 12455158777818282540891733)
              ·
                refine ⟨145958891927557998526075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12455158777818282540891733 145958891927557998526075)
                ·
                  rfl

theorem cell20_959357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_959357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959357 prefixEnd_959357 := by exact prefixLift 959357
  have htrace : WordTrace (prefixWord ++ tailWord_959357) baseStart_959357 baseEnd_959357 := by
    simpa [prefixWord, tailWord_959357, baseEnd_959357] using wordTrace_append hprefix tailTrace_959357
  have hstable : (prefixWord ++ tailWord_959357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959357).length < 2 ^ (prefixWord ++ tailWord_959357).sum := by decide
  have hdescent : baseEnd_959357 < baseStart_959357 := by decide
  rcases family_descends (prefixWord ++ tailWord_959357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959381 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 5]
def baseStart_959381 : Nat := 118140960795 + 959381 * 2 ^ 59
def prefixEnd_959381 : Nat := 4983230072969 + 3 ^ 40 * 959381 * 2
def baseEnd_959381 : Nat := 437887630036636578778127

theorem tailTrace_959381 : CollatzResearch.WordTrace tailWord_959381 prefixEnd_959381 437887630036636578778127 := by
  unfold tailWord_959381
  simp only [CollatzResearch.WordTrace]
  refine ⟨34991499737333961075205997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23327666491555974050137331 34991499737333961075205997)
  ·
    refine ⟨13121812401500235403202249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34991499737333961075205997 13121812401500235403202249)
    ·
      refine ⟨9841359301125176552401687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13121812401500235403202249 9841359301125176552401687)
      ·
        refine ⟨14762038951687764828602531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9841359301125176552401687 14762038951687764828602531)
        ·
          refine ⟨22143058427531647242903797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14762038951687764828602531 22143058427531647242903797)
          ·
            refine ⟨2075911727581091929022231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22143058427531647242903797 2075911727581091929022231)
            ·
              refine ⟨3113867591371637893533347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075911727581091929022231 3113867591371637893533347)
              ·
                refine ⟨4670801387057456840300021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113867591371637893533347 4670801387057456840300021)
                ·
                  refine ⟨437887630036636578778127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4670801387057456840300021 437887630036636578778127)
                  ·
                    rfl

theorem cell20_959381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_959381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959381 prefixEnd_959381 := by exact prefixLift 959381
  have htrace : WordTrace (prefixWord ++ tailWord_959381) baseStart_959381 baseEnd_959381 := by
    simpa [prefixWord, tailWord_959381, baseEnd_959381] using wordTrace_append hprefix tailTrace_959381
  have hstable : (prefixWord ++ tailWord_959381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959381).length < 2 ^ (prefixWord ++ tailWord_959381).sum := by decide
  have hdescent : baseEnd_959381 < baseStart_959381 := by decide
  rcases family_descends (prefixWord ++ tailWord_959381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959414 : List Nat := [5, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_959414 : Nat := 118140960795 + 959414 * 2 ^ 59
def prefixEnd_959414 : Nat := 4983230072969 + 3 ^ 40 * 959414 * 2
def baseEnd_959414 : Nat := 437902692135835130677993

theorem tailTrace_959414 : CollatzResearch.WordTrace tailWord_959414 prefixEnd_959414 437902692135835130677993 := by
  unfold tailWord_959414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187043959138400481947331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23328468897476271807438197 2187043959138400481947331)
  ·
    refine ⟨3280565938707600722920997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2187043959138400481947331 3280565938707600722920997)
    ·
      refine ⟨615106113507675135547687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3280565938707600722920997 615106113507675135547687)
      ·
        refine ⟨922659170261512703321531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615106113507675135547687 922659170261512703321531)
        ·
          refine ⟨1383988755392269054982297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922659170261512703321531 1383988755392269054982297)
          ·
            refine ⟨1037991566544201791236723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383988755392269054982297 1037991566544201791236723)
            ·
              refine ⟨1556987349816302686855085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037991566544201791236723 1556987349816302686855085)
              ·
                refine ⟨583870256181113507570657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1556987349816302686855085 583870256181113507570657)
                ·
                  refine ⟨437902692135835130677993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583870256181113507570657 437902692135835130677993)
                  ·
                    rfl

theorem cell20_959414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_959414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959414 prefixEnd_959414 := by exact prefixLift 959414
  have htrace : WordTrace (prefixWord ++ tailWord_959414) baseStart_959414 baseEnd_959414 := by
    simpa [prefixWord, tailWord_959414, baseEnd_959414] using wordTrace_append hprefix tailTrace_959414
  have hstable : (prefixWord ++ tailWord_959414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959414).length < 2 ^ (prefixWord ++ tailWord_959414).sum := by decide
  have hdescent : baseEnd_959414 < baseStart_959414 := by decide
  rcases family_descends (prefixWord ++ tailWord_959414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959450 : List Nat := [3, 1, 1, 2, 4, 2, 2, 5]
def baseStart_959450 : Nat := 118140960795 + 959450 * 2 ^ 59
def prefixEnd_959450 : Nat := 4983230072969 + 3 ^ 40 * 959450 * 2
def baseEnd_959450 : Nat := 145973041172259668492615

theorem tailTrace_959450 : CollatzResearch.WordTrace tailWord_959450 prefixEnd_959450 145973041172259668492615 := by
  unfold tailWord_959450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748504093520996464866951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23329344249389323906311869 8748504093520996464866951)
  ·
    refine ⟨13122756140281494697300427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8748504093520996464866951 13122756140281494697300427)
    ·
      refine ⟨19684134210422242045950641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13122756140281494697300427 19684134210422242045950641)
      ·
        refine ⟨14763100657816681534462981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19684134210422242045950641 14763100657816681534462981)
        ·
          refine ⟨2768081373340627787711809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14763100657816681534462981 2768081373340627787711809)
          ·
            refine ⟨2076061030005470840783857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768081373340627787711809 2076061030005470840783857)
            ·
              refine ⟨1557045772504103130587893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076061030005470840783857 1557045772504103130587893)
              ·
                refine ⟨145973041172259668492615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1557045772504103130587893 145973041172259668492615)
                ·
                  rfl

theorem cell20_959450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_959450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959450 prefixEnd_959450 := by exact prefixLift 959450
  have htrace : WordTrace (prefixWord ++ tailWord_959450) baseStart_959450 baseEnd_959450 := by
    simpa [prefixWord, tailWord_959450, baseEnd_959450] using wordTrace_append hprefix tailTrace_959450
  have hstable : (prefixWord ++ tailWord_959450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959450).length < 2 ^ (prefixWord ++ tailWord_959450).sum := by decide
  have hdescent : baseEnd_959450 < baseStart_959450 := by decide
  rcases family_descends (prefixWord ++ tailWord_959450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959453 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 3]
def baseStart_959453 : Nat := 118140960795 + 959453 * 2 ^ 59
def prefixEnd_959453 : Nat := 4983230072969 + 3 ^ 40 * 959453 * 2
def baseEnd_959453 : Nat := 437920492798524328377833

theorem tailTrace_959453 : CollatzResearch.WordTrace tailWord_959453 prefixEnd_959453 437920492798524328377833 := by
  unfold tailWord_959453
  simp only [CollatzResearch.WordTrace]
  refine ⟨34994125793073117371827013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23329417195382078247884675 34994125793073117371827013)
  ·
    refine ⟨6561398586201209507217565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34994125793073117371827013 6561398586201209507217565)
    ·
      refine ⟨2460524469825453565206587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6561398586201209507217565 2460524469825453565206587)
      ·
        refine ⟨3690786704738180347809881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460524469825453565206587 3690786704738180347809881)
        ·
          refine ⟨2768090028553635260857411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3690786704738180347809881 2768090028553635260857411)
          ·
            refine ⟨4152135042830452891286117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768090028553635260857411 4152135042830452891286117)
            ·
              refine ⟨778525320530709917116147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4152135042830452891286117 778525320530709917116147)
              ·
                refine ⟨1167787980796064875674221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778525320530709917116147 1167787980796064875674221)
                ·
                  refine ⟨437920492798524328377833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167787980796064875674221 437920492798524328377833)
                  ·
                    rfl

theorem cell20_959453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_959453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959453 prefixEnd_959453 := by exact prefixLift 959453
  have htrace : WordTrace (prefixWord ++ tailWord_959453) baseStart_959453 baseEnd_959453 := by
    simpa [prefixWord, tailWord_959453, baseEnd_959453] using wordTrace_append hprefix tailTrace_959453
  have hstable : (prefixWord ++ tailWord_959453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959453).length < 2 ^ (prefixWord ++ tailWord_959453).sum := by decide
  have hdescent : baseEnd_959453 < baseStart_959453 := by decide
  rcases family_descends (prefixWord ++ tailWord_959453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959464 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_959464 : Nat := 118140960795 + 959464 * 2 ^ 59
def prefixEnd_959464 : Nat := 4983230072969 + 3 ^ 40 * 959464 * 2
def baseEnd_959464 : Nat := 437925513498257179011121

theorem tailTrace_959464 : CollatzResearch.WordTrace tailWord_959464 prefixEnd_959464 437925513498257179011121 := by
  unfold tailWord_959464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17497263498016633125238723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23329684664022177500318297 17497263498016633125238723)
  ·
    refine ⟨26245895247024949687858085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17497263498016633125238723 26245895247024949687858085)
    ·
      refine ⟨4921105358817178066473391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26245895247024949687858085 4921105358817178066473391)
      ·
        refine ⟨7381658038225767099710087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4921105358817178066473391 7381658038225767099710087)
        ·
          refine ⟨11072487057338650649565131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7381658038225767099710087 11072487057338650649565131)
          ·
            refine ⟨16608730586007975974347697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11072487057338650649565131 16608730586007975974347697)
            ·
              refine ⟨12456547939505981980760773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16608730586007975974347697 12456547939505981980760773)
              ·
                refine ⟨2335602738657371621392645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12456547939505981980760773 2335602738657371621392645)
                ·
                  refine ⟨437925513498257179011121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335602738657371621392645 437925513498257179011121)
                  ·
                    rfl

theorem cell20_959464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_959464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959464 prefixEnd_959464 := by exact prefixLift 959464
  have htrace : WordTrace (prefixWord ++ tailWord_959464) baseStart_959464 baseEnd_959464 := by
    simpa [prefixWord, tailWord_959464, baseEnd_959464] using wordTrace_append hprefix tailTrace_959464
  have hstable : (prefixWord ++ tailWord_959464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959464).length < 2 ^ (prefixWord ++ tailWord_959464).sum := by decide
  have hdescent : baseEnd_959464 < baseStart_959464 := by decide
  rcases family_descends (prefixWord ++ tailWord_959464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959471 : List Nat := [1, 1, 2, 1, 4, 3, 2, 6]
def baseStart_959471 : Nat := 118140960795 + 959471 * 2 ^ 59
def prefixEnd_959471 : Nat := 4983230072969 + 3 ^ 40 * 959471 * 2
def baseEnd_959471 : Nat := 145976236162998755259253

theorem tailTrace_959471 : CollatzResearch.WordTrace tailWord_959471 prefixEnd_959471 145976236162998755259253 := by
  unfold tailWord_959471
  simp only [CollatzResearch.WordTrace]
  refine ⟨34994782307007906445982267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23329854871338604297321511 34994782307007906445982267)
  ·
    refine ⟨52492173460511859668973401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34994782307007906445982267 52492173460511859668973401)
    ·
      refine ⟨39369130095383894751730051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52492173460511859668973401 39369130095383894751730051)
      ·
        refine ⟨59053695143075842127595077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39369130095383894751730051 59053695143075842127595077)
        ·
          refine ⟨11072567839326720398924077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59053695143075842127595077 11072567839326720398924077)
          ·
            refine ⟨4152212939747520149596529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11072567839326720398924077 4152212939747520149596529)
            ·
              refine ⟨3114159704810640112197397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4152212939747520149596529 3114159704810640112197397)
              ·
                refine ⟨145976236162998755259253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3114159704810640112197397 145976236162998755259253)
                ·
                  rfl

theorem cell20_959471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_959471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959471 prefixEnd_959471 := by exact prefixLift 959471
  have htrace : WordTrace (prefixWord ++ tailWord_959471) baseStart_959471 baseEnd_959471 := by
    simpa [prefixWord, tailWord_959471, baseEnd_959471] using wordTrace_append hprefix tailTrace_959471
  have hstable : (prefixWord ++ tailWord_959471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959471).length < 2 ^ (prefixWord ++ tailWord_959471).sum := by decide
  have hdescent : baseEnd_959471 < baseStart_959471 := by decide
  rcases family_descends (prefixWord ++ tailWord_959471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959481 : List Nat := [1, 2, 1, 3, 1, 3, 2, 5, 2]
def baseStart_959481 : Nat := 118140960795 + 959481 * 2 ^ 59
def prefixEnd_959481 : Nat := 4983230072969 + 3 ^ 40 * 959481 * 2
def baseEnd_959481 : Nat := 437933272761480675444385

theorem tailTrace_959481 : CollatzResearch.WordTrace tailWord_959481 prefixEnd_959481 437933272761480675444385 := by
  unfold tailWord_959481
  simp only [CollatzResearch.WordTrace]
  refine ⟨34995147036971678153846297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23330098024647785435897531 34995147036971678153846297)
  ·
    refine ⟨26246360277728758615384723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34995147036971678153846297 26246360277728758615384723)
    ·
      refine ⟨39369540416593137923077085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26246360277728758615384723 39369540416593137923077085)
      ·
        refine ⟨14763577656222426721153907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39369540416593137923077085 14763577656222426721153907)
        ·
          refine ⟨22145366484333640081730861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14763577656222426721153907 22145366484333640081730861)
          ·
            refine ⟨8304512431625115030649073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22145366484333640081730861 8304512431625115030649073)
            ·
              refine ⟨6228384323718836272986805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8304512431625115030649073 6228384323718836272986805)
              ·
                refine ⟨583911030348640900592513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6228384323718836272986805 583911030348640900592513)
                ·
                  refine ⟨437933272761480675444385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583911030348640900592513 437933272761480675444385)
                  ·
                    rfl

theorem cell20_959481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_959481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959481 prefixEnd_959481 := by exact prefixLift 959481
  have htrace : WordTrace (prefixWord ++ tailWord_959481) baseStart_959481 baseEnd_959481 := by
    simpa [prefixWord, tailWord_959481, baseEnd_959481] using wordTrace_append hprefix tailTrace_959481
  have hstable : (prefixWord ++ tailWord_959481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959481).length < 2 ^ (prefixWord ++ tailWord_959481).sum := by decide
  have hdescent : baseEnd_959481 < baseStart_959481 := by decide
  rcases family_descends (prefixWord ++ tailWord_959481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959490 : List Nat := [3, 4, 1, 3, 2, 1, 2, 2, 2]
def baseStart_959490 : Nat := 118140960795 + 959490 * 2 ^ 59
def prefixEnd_959490 : Nat := 4983230072969 + 3 ^ 40 * 959490 * 2
def baseEnd_959490 : Nat := 437937380606716644144349

theorem tailTrace_959490 : CollatzResearch.WordTrace tailWord_959490 prefixEnd_959490 437937380606716644144349 := by
  unfold tailWord_959490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748868823484768172730981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23330316862626048460615949 8748868823484768172730981)
  ·
    refine ⟨1640412904403394032387059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8748868823484768172730981 1640412904403394032387059)
    ·
      refine ⟨2460619356605091048580589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1640412904403394032387059 2460619356605091048580589)
      ·
        refine ⟨922732258726909143217721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2460619356605091048580589 922732258726909143217721)
        ·
          refine ⟨692049194045181857413291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922732258726909143217721 692049194045181857413291)
          ·
            refine ⟨1038073791067772786119937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692049194045181857413291 1038073791067772786119937)
            ·
              refine ⟨778555343300829589589953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038073791067772786119937 778555343300829589589953)
              ·
                refine ⟨583916507475622192192465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778555343300829589589953 583916507475622192192465)
                ·
                  refine ⟨437937380606716644144349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583916507475622192192465 437937380606716644144349)
                  ·
                    rfl

theorem cell20_959490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_959490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959490 prefixEnd_959490 := by exact prefixLift 959490
  have htrace : WordTrace (prefixWord ++ tailWord_959490) baseStart_959490 baseEnd_959490 := by
    simpa [prefixWord, tailWord_959490, baseEnd_959490] using wordTrace_append hprefix tailTrace_959490
  have hstable : (prefixWord ++ tailWord_959490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959490).length < 2 ^ (prefixWord ++ tailWord_959490).sum := by decide
  have hdescent : baseEnd_959490 < baseStart_959490 := by decide
  rcases family_descends (prefixWord ++ tailWord_959490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959498 : List Nat := [3, 1, 2, 2, 3, 2, 1, 4, 2]
def baseStart_959498 : Nat := 118140960795 + 959498 * 2 ^ 59
def prefixEnd_959498 : Nat := 4983230072969 + 3 ^ 40 * 959498 * 2
def baseEnd_959498 : Nat := 437941032024704171877649

theorem tailTrace_959498 : CollatzResearch.WordTrace tailWord_959498 prefixEnd_959498 437941032024704171877649 := by
  unfold tailWord_959498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748941769477522514303787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23330511385273393371476765 8748941769477522514303787)
  ·
    refine ⟨13123412654216283771455681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8748941769477522514303787 13123412654216283771455681)
    ·
      refine ⟨9842559490662212828591761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13123412654216283771455681 9842559490662212828591761)
      ·
        refine ⟨7381919617996659621443821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9842559490662212828591761 7381919617996659621443821)
        ·
          refine ⟨2768219856748747358041433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7381919617996659621443821 2768219856748747358041433)
          ·
            refine ⟨2076164892561560518531075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768219856748747358041433 2076164892561560518531075)
            ·
              refine ⟨3114247338842340777796613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076164892561560518531075 3114247338842340777796613)
              ·
                refine ⟨583921376032938895836865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3114247338842340777796613 583921376032938895836865)
                ·
                  refine ⟨437941032024704171877649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583921376032938895836865 437941032024704171877649)
                  ·
                    rfl

theorem cell20_959498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_959498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959498 prefixEnd_959498 := by exact prefixLift 959498
  have htrace : WordTrace (prefixWord ++ tailWord_959498) baseStart_959498 baseEnd_959498 := by
    simpa [prefixWord, tailWord_959498, baseEnd_959498] using wordTrace_append hprefix tailTrace_959498
  have hstable : (prefixWord ++ tailWord_959498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959498).length < 2 ^ (prefixWord ++ tailWord_959498).sum := by decide
  have hdescent : baseEnd_959498 < baseStart_959498 := by decide
  rcases family_descends (prefixWord ++ tailWord_959498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959550 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_959550 : Nat := 118140960795 + 959550 * 2 ^ 59
def prefixEnd_959550 : Nat := 4983230072969 + 3 ^ 40 * 959550 * 2
def baseEnd_959550 : Nat := 437964766241623102144103

theorem tailTrace_959550 : CollatzResearch.WordTrace tailWord_959550 prefixEnd_959550 437964766241623102144103 := by
  unfold tailWord_959550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374707959215212867263513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23331775782481135292072069 4374707959215212867263513)
  ·
    refine ⟨3281030969411409650447635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4374707959215212867263513 3281030969411409650447635)
    ·
      refine ⟨4921546454117114475671453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3281030969411409650447635 4921546454117114475671453)
      ·
        refine ⟨1845579920293917928376795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4921546454117114475671453 1845579920293917928376795)
        ·
          refine ⟨2768369880440876892565193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845579920293917928376795 2768369880440876892565193)
          ·
            refine ⟨2076277410330657669423895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768369880440876892565193 2076277410330657669423895)
            ·
              refine ⟨3114416115495986504135843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076277410330657669423895 3114416115495986504135843)
              ·
                refine ⟨4671624173243979756203765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114416115495986504135843 4671624173243979756203765)
                ·
                  refine ⟨437964766241623102144103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4671624173243979756203765 437964766241623102144103)
                  ·
                    rfl

theorem cell20_959550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_959550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959550 prefixEnd_959550 := by exact prefixLift 959550
  have htrace : WordTrace (prefixWord ++ tailWord_959550) baseStart_959550 baseEnd_959550 := by
    simpa [prefixWord, tailWord_959550, baseEnd_959550] using wordTrace_append hprefix tailTrace_959550
  have hstable : (prefixWord ++ tailWord_959550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959550).length < 2 ^ (prefixWord ++ tailWord_959550).sum := by decide
  have hdescent : baseEnd_959550 < baseStart_959550 := by decide
  rcases family_descends (prefixWord ++ tailWord_959550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959557 : List Nat := [1, 3, 1, 1, 1, 3, 4, 4, 2]
def baseStart_959557 : Nat := 118140960795 + 959557 * 2 ^ 59
def prefixEnd_959557 : Nat := 4983230072969 + 3 ^ 40 * 959557 * 2
def baseEnd_959557 : Nat := 437967961232362188910741

theorem tailTrace_959557 : CollatzResearch.WordTrace tailWord_959557 prefixEnd_959557 437967961232362188910741 := by
  unfold tailWord_959557
  simp only [CollatzResearch.WordTrace]
  refine ⟨34997918984696343133612925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23331945989797562089075283 34997918984696343133612925)
  ·
    refine ⟨13124219619261128675104847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34997918984696343133612925 13124219619261128675104847)
    ·
      refine ⟨19686329428891693012657271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13124219619261128675104847 19686329428891693012657271)
      ·
        refine ⟨29529494143337539518985907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19686329428891693012657271 29529494143337539518985907)
        ·
          refine ⟨44294241215006309278478861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29529494143337539518985907 44294241215006309278478861)
          ·
            refine ⟨16610340455627365979429573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44294241215006309278478861 16610340455627365979429573)
            ·
              refine ⟨3114438835430131121143045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16610340455627365979429573 3114438835430131121143045)
              ·
                refine ⟨583957281643149585214321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3114438835430131121143045 583957281643149585214321)
                ·
                  refine ⟨437967961232362188910741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583957281643149585214321 437967961232362188910741)
                  ·
                    rfl

theorem cell20_959557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_959557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959557 prefixEnd_959557 := by exact prefixLift 959557
  have htrace : WordTrace (prefixWord ++ tailWord_959557) baseStart_959557 baseEnd_959557 := by
    simpa [prefixWord, tailWord_959557, baseEnd_959557] using wordTrace_append hprefix tailTrace_959557
  have hstable : (prefixWord ++ tailWord_959557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959557).length < 2 ^ (prefixWord ++ tailWord_959557).sum := by decide
  have hdescent : baseEnd_959557 < baseStart_959557 := by decide
  rcases family_descends (prefixWord ++ tailWord_959557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959581 : List Nat := [1, 4, 4, 1, 2, 1, 1, 6]
def baseStart_959581 : Nat := 118140960795 + 959581 * 2 ^ 59
def prefixEnd_959581 : Nat := 4983230072969 + 3 ^ 40 * 959581 * 2
def baseEnd_959581 : Nat := 145992971828774924036881

theorem tailTrace_959581 : CollatzResearch.WordTrace tailWord_959581 prefixEnd_959581 145992971828774924036881 := by
  unfold tailWord_959581
  simp only [CollatzResearch.WordTrace]
  refine ⟨34998794336609395232486597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23332529557739596821657731 34998794336609395232486597)
  ·
    refine ⟨6562273938114261606091237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34998794336609395232486597 6562273938114261606091237)
    ·
      refine ⟨1230426363396424051142107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6562273938114261606091237 1230426363396424051142107)
      ·
        refine ⟨1845639545094636076713161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230426363396424051142107 1845639545094636076713161)
        ·
          refine ⟨1384229658820977057534871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1845639545094636076713161 1384229658820977057534871)
          ·
            refine ⟨2076344488231465586302307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384229658820977057534871 2076344488231465586302307)
            ·
              refine ⟨3114516732347198379453461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076344488231465586302307 3114516732347198379453461)
              ·
                refine ⟨145992971828774924036881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3114516732347198379453461 145992971828774924036881)
                ·
                  rfl

theorem cell20_959581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 6].length) (baseStart_959581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959581 prefixEnd_959581 := by exact prefixLift 959581
  have htrace : WordTrace (prefixWord ++ tailWord_959581) baseStart_959581 baseEnd_959581 := by
    simpa [prefixWord, tailWord_959581, baseEnd_959581] using wordTrace_append hprefix tailTrace_959581
  have hstable : (prefixWord ++ tailWord_959581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959581).length < 2 ^ (prefixWord ++ tailWord_959581).sum := by decide
  have hdescent : baseEnd_959581 < baseStart_959581 := by decide
  rcases family_descends (prefixWord ++ tailWord_959581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959612 : List Nat := [2, 2, 2, 1, 1, 3, 5, 2, 2]
def baseStart_959612 : Nat := 118140960795 + 959612 * 2 ^ 59
def prefixEnd_959612 : Nat := 4983230072969 + 3 ^ 40 * 959612 * 2
def baseEnd_959612 : Nat := 437993064731026442077183

theorem tailTrace_959612 : CollatzResearch.WordTrace tailWord_959612 prefixEnd_959612 437993064731026442077183 := by
  unfold tailWord_959612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17499962499748543763432545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23333283332998058351243393 17499962499748543763432545)
  ·
    refine ⟨13124971874811407822574409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17499962499748543763432545 13124971874811407822574409)
    ·
      refine ⟨9843728906108555866930807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13124971874811407822574409 9843728906108555866930807)
      ·
        refine ⟨14765593359162833800396211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9843728906108555866930807 14765593359162833800396211)
        ·
          refine ⟨22148390038744250700594317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14765593359162833800396211 22148390038744250700594317)
          ·
            refine ⟨8305646264529094012722869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22148390038744250700594317 8305646264529094012722869)
            ·
              refine ⟨778654337299602563692769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8305646264529094012722869 778654337299602563692769)
              ·
                refine ⟨583990752974701922769577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778654337299602563692769 583990752974701922769577)
                ·
                  refine ⟨437993064731026442077183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583990752974701922769577 437993064731026442077183)
                  ·
                    rfl

theorem cell20_959612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_959612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959612 prefixEnd_959612 := by exact prefixLift 959612
  have htrace : WordTrace (prefixWord ++ tailWord_959612) baseStart_959612 baseEnd_959612 := by
    simpa [prefixWord, tailWord_959612, baseEnd_959612] using wordTrace_append hprefix tailTrace_959612
  have hstable : (prefixWord ++ tailWord_959612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959612).length < 2 ^ (prefixWord ++ tailWord_959612).sum := by decide
  have hdescent : baseEnd_959612 < baseStart_959612 := by decide
  rcases family_descends (prefixWord ++ tailWord_959612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959616 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_959616 : Nat := 118140960795 + 959616 * 2 ^ 59
def prefixEnd_959616 : Nat := 4983230072969 + 3 ^ 40 * 959616 * 2
def baseEnd_959616 : Nat := 437994890440020205943833

theorem tailTrace_959616 : CollatzResearch.WordTrace tailWord_959616 prefixEnd_959616 437994890440020205943833 := by
  unfold tailWord_959616
  simp only [CollatzResearch.WordTrace]
  refine ⟨17500035445741298105005351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23333380594321730806673801 17500035445741298105005351)
  ·
    refine ⟨26250053168611947157508027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17500035445741298105005351 26250053168611947157508027)
    ·
      refine ⟨39375079752917920736262041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26250053168611947157508027 39375079752917920736262041)
      ·
        refine ⟨29531309814688440552196531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39375079752917920736262041 29531309814688440552196531)
        ·
          refine ⟨44296964722032660828294797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29531309814688440552196531 44296964722032660828294797)
          ·
            refine ⟨16611361770762247810610549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44296964722032660828294797 16611361770762247810610549)
            ·
              refine ⟨1557315166008960732244739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16611361770762247810610549 1557315166008960732244739)
              ·
                refine ⟨2335972749013441098367109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557315166008960732244739 2335972749013441098367109)
                ·
                  refine ⟨437994890440020205943833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335972749013441098367109 437994890440020205943833)
                  ·
                    rfl

theorem cell20_959616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_959616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959616 prefixEnd_959616 := by exact prefixLift 959616
  have htrace : WordTrace (prefixWord ++ tailWord_959616) baseStart_959616 baseEnd_959616 := by
    simpa [prefixWord, tailWord_959616, baseEnd_959616] using wordTrace_append hprefix tailTrace_959616
  have hstable : (prefixWord ++ tailWord_959616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959616).length < 2 ^ (prefixWord ++ tailWord_959616).sum := by decide
  have hdescent : baseEnd_959616 < baseStart_959616 := by decide
  rcases family_descends (prefixWord ++ tailWord_959616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959661 : List Nat := [1, 5, 2, 1, 11]
def baseStart_959661 : Nat := 118140960795 + 959661 * 2 ^ 59
def prefixEnd_959661 : Nat := 4983230072969 + 3 ^ 40 * 959661 * 2
def baseEnd_959661 : Nat := 5407597897113580857329

theorem tailTrace_959661 : CollatzResearch.WordTrace tailWord_959661 prefixEnd_959661 5407597897113580857329 := by
  unfold tailWord_959661
  simp only [CollatzResearch.WordTrace]
  refine ⟨35001712176319568895398837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23334474784213045930265891 35001712176319568895398837)
  ·
    refine ⟨3281410516529959583943641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35001712176319568895398837 3281410516529959583943641)
    ·
      refine ⟨2461057887397469687957731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3281410516529959583943641 2461057887397469687957731)
      ·
        refine ⟨3691586831096204531936597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461057887397469687957731 3691586831096204531936597)
        ·
          refine ⟨5407597897113580857329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3691586831096204531936597 5407597897113580857329)
          ·
            rfl

theorem cell20_959661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 11].length) (baseStart_959661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959661 prefixEnd_959661 := by exact prefixLift 959661
  have htrace : WordTrace (prefixWord ++ tailWord_959661) baseStart_959661 baseEnd_959661 := by
    simpa [prefixWord, tailWord_959661, baseEnd_959661] using wordTrace_append hprefix tailTrace_959661
  have hstable : (prefixWord ++ tailWord_959661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959661).length < 2 ^ (prefixWord ++ tailWord_959661).sum := by decide
  have hdescent : baseEnd_959661 < baseStart_959661 := by decide
  rcases family_descends (prefixWord ++ tailWord_959661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959671 : List Nat := [1, 1, 3, 1, 4, 1, 3, 4, 2]
def baseStart_959671 : Nat := 118140960795 + 959671 * 2 ^ 59
def prefixEnd_959671 : Nat := 4983230072969 + 3 ^ 40 * 959671 * 2
def baseEnd_959671 : Nat := 438019993938684459110275

theorem tailTrace_959671 : CollatzResearch.WordTrace tailWord_959671 prefixEnd_959671 438019993938684459110275 := by
  unfold tailWord_959671
  simp only [CollatzResearch.WordTrace]
  refine ⟨35002076906283340603262867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23334717937522227068841911 35002076906283340603262867)
  ·
    refine ⟨52503115359425010904894301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35002076906283340603262867 52503115359425010904894301)
    ·
      refine ⟨19688668259784379089335363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52503115359425010904894301 19688668259784379089335363)
      ·
        refine ⟨29533002389676568634003045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19688668259784379089335363 29533002389676568634003045)
        ·
          refine ⟨5537437948064356618875571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29533002389676568634003045 5537437948064356618875571)
          ·
            refine ⟨8306156922096534928313357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5537437948064356618875571 8306156922096534928313357)
            ·
              refine ⟨3114808845786200598117509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8306156922096534928313357 3114808845786200598117509)
              ·
                refine ⟨584026658584912612147033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3114808845786200598117509 584026658584912612147033)
                ·
                  refine ⟨438019993938684459110275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584026658584912612147033 438019993938684459110275)
                  ·
                    rfl

theorem cell20_959671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 2].length) (baseStart_959671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959671 prefixEnd_959671 := by exact prefixLift 959671
  have htrace : WordTrace (prefixWord ++ tailWord_959671) baseStart_959671 baseEnd_959671 := by
    simpa [prefixWord, tailWord_959671, baseEnd_959671] using wordTrace_append hprefix tailTrace_959671
  have hstable : (prefixWord ++ tailWord_959671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959671).length < 2 ^ (prefixWord ++ tailWord_959671).sum := by decide
  have hdescent : baseEnd_959671 < baseStart_959671 := by decide
  rcases family_descends (prefixWord ++ tailWord_959671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959678 : List Nat := [4, 2, 1, 1, 3, 1, 3, 5]
def baseStart_959678 : Nat := 118140960795 + 959678 * 2 ^ 59
def prefixEnd_959678 : Nat := 4983230072969 + 3 ^ 40 * 959678 * 2
def baseEnd_959678 : Nat := 146007729643141181958971

theorem tailTrace_959678 : CollatzResearch.WordTrace tailWord_959678 prefixEnd_959678 146007729643141181958971 := by
  unfold tailWord_959678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375291527157247599845961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23334888144838653865845125 4375291527157247599845961)
  ·
    refine ⟨3281468645367935699884471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4375291527157247599845961 3281468645367935699884471)
    ·
      refine ⟨4922202968051903549826707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3281468645367935699884471 4922202968051903549826707)
      ·
        refine ⟨7383304452077855324740061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4922202968051903549826707 7383304452077855324740061)
        ·
          refine ⟨2768739169529195746777523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7383304452077855324740061 2768739169529195746777523)
          ·
            refine ⟨4153108754293793620166285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768739169529195746777523 4153108754293793620166285)
            ·
              refine ⟨1557415782860172607562357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4153108754293793620166285 1557415782860172607562357)
              ·
                refine ⟨146007729643141181958971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1557415782860172607562357 146007729643141181958971)
                ·
                  rfl

theorem cell20_959678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_959678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959678 prefixEnd_959678 := by exact prefixLift 959678
  have htrace : WordTrace (prefixWord ++ tailWord_959678) baseStart_959678 baseEnd_959678 := by
    simpa [prefixWord, tailWord_959678, baseEnd_959678] using wordTrace_append hprefix tailTrace_959678
  have hstable : (prefixWord ++ tailWord_959678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959678).length < 2 ^ (prefixWord ++ tailWord_959678).sum := by decide
  have hdescent : baseEnd_959678 < baseStart_959678 := by decide
  rcases family_descends (prefixWord ++ tailWord_959678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959706 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_959706 : Nat := 118140960795 + 959706 * 2 ^ 59
def prefixEnd_959706 : Nat := 4983230072969 + 3 ^ 40 * 959706 * 2
def baseEnd_959706 : Nat := 438035968892379892943465

theorem tailTrace_959706 : CollatzResearch.WordTrace tailWord_959706 prefixEnd_959706 438035968892379892943465 := by
  unfold tailWord_959706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750838365289135395196743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23335568974104361053857981 8750838365289135395196743)
  ·
    refine ⟨13126257547933703092795115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8750838365289135395196743 13126257547933703092795115)
    ·
      refine ⟨19689386321900554639192673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13126257547933703092795115 19689386321900554639192673)
      ·
        refine ⟨14767039741425415979394505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19689386321900554639192673 14767039741425415979394505)
        ·
          refine ⟨11075279806069061984545879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14767039741425415979394505 11075279806069061984545879)
          ·
            refine ⟨16612919709103592976818819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11075279806069061984545879 16612919709103592976818819)
            ·
              refine ⟨24919379563655389465228229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16612919709103592976818819 24919379563655389465228229)
              ·
                refine ⟨4672383668185385524730293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24919379563655389465228229 4672383668185385524730293)
                ·
                  refine ⟨438035968892379892943465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4672383668185385524730293 438035968892379892943465)
                  ·
                    rfl

theorem cell20_959706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_959706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959706 prefixEnd_959706 := by exact prefixLift 959706
  have htrace : WordTrace (prefixWord ++ tailWord_959706) baseStart_959706 baseEnd_959706 := by
    simpa [prefixWord, tailWord_959706, baseEnd_959706] using wordTrace_append hprefix tailTrace_959706
  have hstable : (prefixWord ++ tailWord_959706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959706).length < 2 ^ (prefixWord ++ tailWord_959706).sum := by decide
  have hdescent : baseEnd_959706 < baseStart_959706 := by decide
  rcases family_descends (prefixWord ++ tailWord_959706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959719 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 3]
def baseStart_959719 : Nat := 118140960795 + 959719 * 2 ^ 59
def prefixEnd_959719 : Nat := 4983230072969 + 3 ^ 40 * 959719 * 2
def baseEnd_959719 : Nat := 438041902446609625510079

theorem tailTrace_959719 : CollatzResearch.WordTrace tailWord_959719 prefixEnd_959719 438041902446609625510079 := by
  unfold tailWord_959719
  simp only [CollatzResearch.WordTrace]
  refine ⟨35003827610109444801010211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23335885073406296534006807 35003827610109444801010211)
  ·
    refine ⟨52505741415164167201515317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35003827610109444801010211 52505741415164167201515317)
    ·
      refine ⟨4922413257671640675142061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52505741415164167201515317 4922413257671640675142061)
      ·
        refine ⟨1845904971626865253178273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4922413257671640675142061 1845904971626865253178273)
        ·
          refine ⟨1384428728720148939883705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1845904971626865253178273 1384428728720148939883705)
          ·
            refine ⟨1038321546540111704912779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1384428728720148939883705 1038321546540111704912779)
            ·
              refine ⟨1557482319810167557369169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038321546540111704912779 1557482319810167557369169)
              ·
                refine ⟨1168111739857625668026877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557482319810167557369169 1168111739857625668026877)
                ·
                  refine ⟨438041902446609625510079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168111739857625668026877 438041902446609625510079)
                  ·
                    rfl

theorem cell20_959719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 3].length) (baseStart_959719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959719 prefixEnd_959719 := by exact prefixLift 959719
  have htrace : WordTrace (prefixWord ++ tailWord_959719) baseStart_959719 baseEnd_959719 := by
    simpa [prefixWord, tailWord_959719, baseEnd_959719] using wordTrace_append hprefix tailTrace_959719
  have hstable : (prefixWord ++ tailWord_959719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959719).length < 2 ^ (prefixWord ++ tailWord_959719).sum := by decide
  have hdescent : baseEnd_959719 < baseStart_959719 := by decide
  rcases family_descends (prefixWord ++ tailWord_959719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959723 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 3]
def baseStart_959723 : Nat := 118140960795 + 959723 * 2 ^ 59
def prefixEnd_959723 : Nat := 4983230072969 + 3 ^ 40 * 959723 * 2
def baseEnd_959723 : Nat := 438043728155603389376729

theorem tailTrace_959723 : CollatzResearch.WordTrace tailWord_959723 prefixEnd_959723 438043728155603389376729 := by
  unfold tailWord_959723
  simp only [CollatzResearch.WordTrace]
  refine ⟨35003973502094953484155823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23335982334729968989437215 35003973502094953484155823)
  ·
    refine ⟨52505960253142430226233735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35003973502094953484155823 52505960253142430226233735)
    ·
      refine ⟨78758940379713645339350603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52505960253142430226233735 78758940379713645339350603)
      ·
        refine ⟨118138410569570468009025905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78758940379713645339350603 118138410569570468009025905)
        ·
          refine ⟨88603807927177851006769429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118138410569570468009025905 88603807927177851006769429)
          ·
            refine ⟨4153303496586461765942317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88603807927177851006769429 4153303496586461765942317)
            ·
              refine ⟨1557488811219923162228369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4153303496586461765942317 1557488811219923162228369)
              ·
                refine ⟨1168116608414942371671277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557488811219923162228369 1168116608414942371671277)
                ·
                  refine ⟨438043728155603389376729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168116608414942371671277 438043728155603389376729)
                  ·
                    rfl

theorem cell20_959723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 3].length) (baseStart_959723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959723 prefixEnd_959723 := by exact prefixLift 959723
  have htrace : WordTrace (prefixWord ++ tailWord_959723) baseStart_959723 baseEnd_959723 := by
    simpa [prefixWord, tailWord_959723, baseEnd_959723] using wordTrace_append hprefix tailTrace_959723
  have hstable : (prefixWord ++ tailWord_959723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959723).length < 2 ^ (prefixWord ++ tailWord_959723).sum := by decide
  have hdescent : baseEnd_959723 < baseStart_959723 := by decide
  rcases family_descends (prefixWord ++ tailWord_959723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959806 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_959806 : Nat := 118140960795 + 959806 * 2 ^ 59
def prefixEnd_959806 : Nat := 4983230072969 + 3 ^ 40 * 959806 * 2
def baseEnd_959806 : Nat := 438081611617223989609723

theorem tailTrace_959806 : CollatzResearch.WordTrace tailWord_959806 prefixEnd_959806 438081611617223989609723 := by
  unfold tailWord_959806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375875095099282332428409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23338000507196172439618181 4375875095099282332428409)
  ·
    refine ⟨3281906321324461749321307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4375875095099282332428409 3281906321324461749321307)
    ·
      refine ⟨4922859481986692623981961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3281906321324461749321307 4922859481986692623981961)
      ·
        refine ⟨3692144611490019467986471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4922859481986692623981961 3692144611490019467986471)
        ·
          refine ⟨5538216917235029201979707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692144611490019467986471 5538216917235029201979707)
          ·
            refine ⟨8307325375852543802969561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5538216917235029201979707 8307325375852543802969561)
            ·
              refine ⟨6230494031889407852227171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8307325375852543802969561 6230494031889407852227171)
              ·
                refine ⟨9345741047834111778340757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230494031889407852227171 9345741047834111778340757)
                ·
                  refine ⟨438081611617223989609723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9345741047834111778340757 438081611617223989609723)
                  ·
                    rfl

theorem cell20_959806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_959806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959806 prefixEnd_959806 := by exact prefixLift 959806
  have htrace : WordTrace (prefixWord ++ tailWord_959806) baseStart_959806 baseEnd_959806 := by
    simpa [prefixWord, tailWord_959806, baseEnd_959806] using wordTrace_append hprefix tailTrace_959806
  have hstable : (prefixWord ++ tailWord_959806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959806).length < 2 ^ (prefixWord ++ tailWord_959806).sum := by decide
  have hdescent : baseEnd_959806 < baseStart_959806 := by decide
  rcases family_descends (prefixWord ++ tailWord_959806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959840 : List Nat := [2, 1, 1, 3, 4, 1, 4, 2, 2]
def baseStart_959840 : Nat := 118140960795 + 959840 * 2 ^ 59
def prefixEnd_959840 : Nat := 4983230072969 + 3 ^ 40 * 959840 * 2
def baseEnd_959840 : Nat := 438097130143670982476251

theorem tailTrace_959840 : CollatzResearch.WordTrace tailWord_959840 prefixEnd_959840 438097130143670982476251 := by
  unfold tailWord_959840
  simp only [CollatzResearch.WordTrace]
  refine ⟨17504120421335541233082487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23338827228447388310776649 17504120421335541233082487)
  ·
    refine ⟨26256180632003311849623731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17504120421335541233082487 26256180632003311849623731)
    ·
      refine ⟨39384270948004967774435597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26256180632003311849623731 39384270948004967774435597)
      ·
        refine ⟨14769101605501862915413349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39384270948004967774435597 14769101605501862915413349)
        ·
          refine ⟨2769206551031599296640003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14769101605501862915413349 2769206551031599296640003)
          ·
            refine ⟨4153809826547398944960005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769206551031599296640003 4153809826547398944960005)
            ·
              refine ⟨778839342477637302180001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4153809826547398944960005 778839342477637302180001)
              ·
                refine ⟨584129506858227976635001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778839342477637302180001 584129506858227976635001)
                ·
                  refine ⟨438097130143670982476251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584129506858227976635001 438097130143670982476251)
                  ·
                    rfl

theorem cell20_959840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_959840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959840 prefixEnd_959840 := by exact prefixLift 959840
  have htrace : WordTrace (prefixWord ++ tailWord_959840) baseStart_959840 baseEnd_959840 := by
    simpa [prefixWord, tailWord_959840, baseEnd_959840] using wordTrace_append hprefix tailTrace_959840
  have hstable : (prefixWord ++ tailWord_959840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959840).length < 2 ^ (prefixWord ++ tailWord_959840).sum := by decide
  have hdescent : baseEnd_959840 < baseStart_959840 := by decide
  rcases family_descends (prefixWord ++ tailWord_959840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959847 : List Nat := [1, 1, 5, 1, 5, 1, 1, 5]
def baseStart_959847 : Nat := 118140960795 + 959847 * 2 ^ 59
def prefixEnd_959847 : Nat := 4983230072969 + 3 ^ 40 * 959847 * 2
def baseEnd_959847 : Nat := 146033441711470023080963

theorem tailTrace_959847 : CollatzResearch.WordTrace tailWord_959847 prefixEnd_959847 146033441711470023080963 := by
  unfold tailWord_959847
  simp only [CollatzResearch.WordTrace]
  refine ⟨35008496153645722661669795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23338997435763815107779863 35008496153645722661669795)
  ·
    refine ⟨52512744230468583992504693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35008496153645722661669795 52512744230468583992504693)
    ·
      refine ⟨4923069771606429749297315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52512744230468583992504693 4923069771606429749297315)
      ·
        refine ⟨7384604657409644623945973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4923069771606429749297315 7384604657409644623945973)
        ·
          refine ⟨692306686632154183494935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7384604657409644623945973 692306686632154183494935)
          ·
            refine ⟨1038460029948231275242403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692306686632154183494935 1038460029948231275242403)
            ·
              refine ⟨1557690044922346912863605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038460029948231275242403 1557690044922346912863605)
              ·
                refine ⟨146033441711470023080963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1557690044922346912863605 146033441711470023080963)
                ·
                  rfl

theorem cell20_959847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 5].length) (baseStart_959847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959847 prefixEnd_959847 := by exact prefixLift 959847
  have htrace : WordTrace (prefixWord ++ tailWord_959847) baseStart_959847 baseEnd_959847 := by
    simpa [prefixWord, tailWord_959847, baseEnd_959847] using wordTrace_append hprefix tailTrace_959847
  have hstable : (prefixWord ++ tailWord_959847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959847).length < 2 ^ (prefixWord ++ tailWord_959847).sum := by decide
  have hdescent : baseEnd_959847 < baseStart_959847 := by decide
  rcases family_descends (prefixWord ++ tailWord_959847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959861 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 4]
def baseStart_959861 : Nat := 118140960795 + 959861 * 2 ^ 59
def prefixEnd_959861 : Nat := 4983230072969 + 3 ^ 40 * 959861 * 2
def baseEnd_959861 : Nat := 438106715115888242776165

theorem tailTrace_959861 : CollatzResearch.WordTrace tailWord_959861 prefixEnd_959861 438106715115888242776165 := by
  unfold tailWord_959861
  simp only [CollatzResearch.WordTrace]
  refine ⟨35009006775595003052679437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23339337850396668701786291 35009006775595003052679437)
  ·
    refine ⟨13128377540848126144754789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35009006775595003052679437 13128377540848126144754789)
    ·
      refine ⟨2461570788909023652141523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13128377540848126144754789 2461570788909023652141523)
      ·
        refine ⟨3692356183363535478212285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461570788909023652141523 3692356183363535478212285)
        ·
          refine ⟨1384633568761325804329607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3692356183363535478212285 1384633568761325804329607)
          ·
            refine ⟨2076950353141988706494411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384633568761325804329607 2076950353141988706494411)
            ·
              refine ⟨3115425529712983059741617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076950353141988706494411 3115425529712983059741617)
              ·
                refine ⟨2336569147284737294806213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3115425529712983059741617 2336569147284737294806213)
                ·
                  refine ⟨438106715115888242776165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336569147284737294806213 438106715115888242776165)
                  ·
                    rfl

theorem cell20_959861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_959861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959861 prefixEnd_959861 := by exact prefixLift 959861
  have htrace : WordTrace (prefixWord ++ tailWord_959861) baseStart_959861 baseEnd_959861 := by
    simpa [prefixWord, tailWord_959861, baseEnd_959861] using wordTrace_append hprefix tailTrace_959861
  have hstable : (prefixWord ++ tailWord_959861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959861).length < 2 ^ (prefixWord ++ tailWord_959861).sum := by decide
  have hdescent : baseEnd_959861 < baseStart_959861 := by decide
  rcases family_descends (prefixWord ++ tailWord_959861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959865 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_959865 : Nat := 118140960795 + 959865 * 2 ^ 59
def prefixEnd_959865 : Nat := 4983230072969 + 3 ^ 40 * 959865 * 2
def baseEnd_959865 : Nat := 438108540824882006642815

theorem tailTrace_959865 : CollatzResearch.WordTrace tailWord_959865 prefixEnd_959865 438108540824882006642815 := by
  unfold tailWord_959865
  simp only [CollatzResearch.WordTrace]
  refine ⟨35009152667580511735825049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23339435111720341157216699 35009152667580511735825049)
  ·
    refine ⟨26256864500685383801868787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35009152667580511735825049 26256864500685383801868787)
    ·
      refine ⟨39385296751028075702803181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26256864500685383801868787 39385296751028075702803181)
      ·
        refine ⟨14769486281635528388551193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39385296751028075702803181 14769486281635528388551193)
        ·
          refine ⟨11077114711226646291413395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14769486281635528388551193 11077114711226646291413395)
          ·
            refine ⟨16615672066839969437120093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11077114711226646291413395 16615672066839969437120093)
            ·
              refine ⟨6230877025064988538920035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16615672066839969437120093 6230877025064988538920035)
              ·
                refine ⟨9346315537597482808380053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230877025064988538920035 9346315537597482808380053)
                ·
                  refine ⟨438108540824882006642815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9346315537597482808380053 438108540824882006642815)
                  ·
                    rfl

theorem cell20_959865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_959865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959865 prefixEnd_959865 := by exact prefixLift 959865
  have htrace : WordTrace (prefixWord ++ tailWord_959865) baseStart_959865 baseEnd_959865 := by
    simpa [prefixWord, tailWord_959865, baseEnd_959865] using wordTrace_append hprefix tailTrace_959865
  have hstable : (prefixWord ++ tailWord_959865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959865).length < 2 ^ (prefixWord ++ tailWord_959865).sum := by decide
  have hdescent : baseEnd_959865 < baseStart_959865 := by decide
  rcases family_descends (prefixWord ++ tailWord_959865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959872 : List Nat := [2, 1, 1, 2, 1, 2, 1, 10]
def baseStart_959872 : Nat := 118140960795 + 959872 * 2 ^ 59
def prefixEnd_959872 : Nat := 4983230072969 + 3 ^ 40 * 959872 * 2
def baseEnd_959872 : Nat := 146037245271873697803151

theorem tailTrace_959872 : CollatzResearch.WordTrace tailWord_959872 prefixEnd_959872 146037245271873697803151 := by
  unfold tailWord_959872
  simp only [CollatzResearch.WordTrace]
  refine ⟨17504703989277575965664935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23339605319036767954219913 17504703989277575965664935)
  ·
    refine ⟨26257055983916363948497403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17504703989277575965664935 26257055983916363948497403)
    ·
      refine ⟨39385583975874545922746105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26257055983916363948497403 39385583975874545922746105)
      ·
        refine ⟨29539187981905909442059579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39385583975874545922746105 29539187981905909442059579)
        ·
          refine ⟨44308781972858864163089369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29539187981905909442059579 44308781972858864163089369)
          ·
            refine ⟨33231586479644148122317027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44308781972858864163089369 33231586479644148122317027)
            ·
              refine ⟨49847379719466222183475541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33231586479644148122317027 49847379719466222183475541)
              ·
                refine ⟨146037245271873697803151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49847379719466222183475541 146037245271873697803151)
                ·
                  rfl

theorem cell20_959872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_959872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959872 prefixEnd_959872 := by exact prefixLift 959872
  have htrace : WordTrace (prefixWord ++ tailWord_959872) baseStart_959872 baseEnd_959872 := by
    simpa [prefixWord, tailWord_959872, baseEnd_959872] using wordTrace_append hprefix tailTrace_959872
  have hstable : (prefixWord ++ tailWord_959872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959872).length < 2 ^ (prefixWord ++ tailWord_959872).sum := by decide
  have hdescent : baseEnd_959872 < baseStart_959872 := by decide
  rcases family_descends (prefixWord ++ tailWord_959872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959892 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 3]
def baseStart_959892 : Nat := 118140960795 + 959892 * 2 ^ 59
def prefixEnd_959892 : Nat := 4983230072969 + 3 ^ 40 * 959892 * 2
def baseEnd_959892 : Nat := 438120864360589912742705

theorem tailTrace_959892 : CollatzResearch.WordTrace tailWord_959892 prefixEnd_959892 438120864360589912742705 := by
  unfold tailWord_959892
  simp only [CollatzResearch.WordTrace]
  refine ⟨17505068719241347673528965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23340091625655130231371953 17505068719241347673528965)
  ·
    refine ⟨3282200384857752688786681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17505068719241347673528965 3282200384857752688786681)
    ·
      refine ⟨2461650288643314516590011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3282200384857752688786681 2461650288643314516590011)
      ·
        refine ⟨3692475432964971774885017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461650288643314516590011 3692475432964971774885017)
        ·
          refine ⟨2769356574723728831163763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3692475432964971774885017 2769356574723728831163763)
          ·
            refine ⟨4154034862085593246745645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769356574723728831163763 4154034862085593246745645)
            ·
              refine ⟨1557763073282097467529617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4154034862085593246745645 1557763073282097467529617)
              ·
                refine ⟨1168322304961573100647213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557763073282097467529617 1168322304961573100647213)
                ·
                  refine ⟨438120864360589912742705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168322304961573100647213 438120864360589912742705)
                  ·
                    rfl

theorem cell20_959892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_959892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959892 prefixEnd_959892 := by exact prefixLift 959892
  have htrace : WordTrace (prefixWord ++ tailWord_959892) baseStart_959892 baseEnd_959892 := by
    simpa [prefixWord, tailWord_959892, baseEnd_959892] using wordTrace_append hprefix tailTrace_959892
  have hstable : (prefixWord ++ tailWord_959892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959892).length < 2 ^ (prefixWord ++ tailWord_959892).sum := by decide
  have hdescent : baseEnd_959892 < baseStart_959892 := by decide
  rcases family_descends (prefixWord ++ tailWord_959892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959965 : List Nat := [1, 4, 3, 1, 1, 2, 1, 7]
def baseStart_959965 : Nat := 118140960795 + 959965 * 2 ^ 59
def prefixEnd_959965 : Nat := 4983230072969 + 3 ^ 40 * 959965 * 2
def baseEnd_959965 : Nat := 146051394516575367769691

theorem tailTrace_959965 : CollatzResearch.WordTrace tailWord_959965 prefixEnd_959965 146051394516575367769691 := by
  unfold tailWord_959965
  simp only [CollatzResearch.WordTrace]
  refine ⟨35012799967218228814465349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23341866644812152542976899 35012799967218228814465349)
  ·
    refine ⟨6564899993853417902712253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35012799967218228814465349 6564899993853417902712253)
    ·
      refine ⟨2461837497695031713517095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6564899993853417902712253 2461837497695031713517095)
      ·
        refine ⟨3692756246542547570275643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461837497695031713517095 3692756246542547570275643)
        ·
          refine ⟨5539134369813821355413465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692756246542547570275643 5539134369813821355413465)
          ·
            refine ⟨4154350777360366016560099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5539134369813821355413465 4154350777360366016560099)
            ·
              refine ⟨6231526166040549024840149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154350777360366016560099 6231526166040549024840149)
              ·
                refine ⟨146051394516575367769691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6231526166040549024840149 146051394516575367769691)
                ·
                  rfl

theorem cell20_959965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_959965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_959965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_959965 prefixEnd_959965 := by exact prefixLift 959965
  have htrace : WordTrace (prefixWord ++ tailWord_959965) baseStart_959965 baseEnd_959965 := by
    simpa [prefixWord, tailWord_959965, baseEnd_959965] using wordTrace_append hprefix tailTrace_959965
  have hstable : (prefixWord ++ tailWord_959965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959965).length < 2 ^ (prefixWord ++ tailWord_959965).sum := by decide
  have hdescent : baseEnd_959965 < baseStart_959965 := by decide
  rcases family_descends (prefixWord ++ tailWord_959965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960017 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_960017 : Nat := 118140960795 + 960017 * 2 ^ 59
def prefixEnd_960017 : Nat := 4983230072969 + 3 ^ 40 * 960017 * 2
def baseEnd_960017 : Nat := 438177917766645033575527

theorem tailTrace_960017 : CollatzResearch.WordTrace tailWord_960017 prefixEnd_960017 438177917766645033575527 := by
  unfold tailWord_960017
  simp only [CollatzResearch.WordTrace]
  refine ⟨35014696563029841695358305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23343131042019894463572203 35014696563029841695358305)
  ·
    refine ⟨26261022422272381271518729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35014696563029841695358305 26261022422272381271518729)
    ·
      refine ⟨19695766816704285953639047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26261022422272381271518729 19695766816704285953639047)
      ·
        refine ⟨29543650225056428930458571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19695766816704285953639047 29543650225056428930458571)
        ·
          refine ⟨44315475337584643395687857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29543650225056428930458571 44315475337584643395687857)
          ·
            refine ⟨33236606503188482546765893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44315475337584643395687857 33236606503188482546765893)
            ·
              refine ⟨6231863719347840477518605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33236606503188482546765893 6231863719347840477518605)
              ·
                refine ⟨2336948894755440179069477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6231863719347840477518605 2336948894755440179069477)
                ·
                  refine ⟨438177917766645033575527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336948894755440179069477 438177917766645033575527)
                  ·
                    rfl

theorem cell20_960017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_960017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960017 prefixEnd_960017 := by exact prefixLift 960017
  have htrace : WordTrace (prefixWord ++ tailWord_960017) baseStart_960017 baseEnd_960017 := by
    simpa [prefixWord, tailWord_960017, baseEnd_960017] using wordTrace_append hprefix tailTrace_960017
  have hstable : (prefixWord ++ tailWord_960017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960017).length < 2 ^ (prefixWord ++ tailWord_960017).sum := by decide
  have hdescent : baseEnd_960017 < baseStart_960017 := by decide
  rcases family_descends (prefixWord ++ tailWord_960017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960051 : List Nat := [1, 1, 1, 2, 4, 4, 2, 3, 2]
def baseStart_960051 : Nat := 118140960795 + 960051 * 2 ^ 59
def prefixEnd_960051 : Nat := 4983230072969 + 3 ^ 40 * 960051 * 2
def baseEnd_960051 : Nat := 438193436293092026442055

theorem tailTrace_960051 : CollatzResearch.WordTrace tailWord_960051 prefixEnd_960051 438193436293092026442055 := by
  unfold tailWord_960051
  simp only [CollatzResearch.WordTrace]
  refine ⟨35015936644906665502096007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23343957763271110334730671 35015936644906665502096007)
  ·
    refine ⟨52523904967359998253144011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35015936644906665502096007 52523904967359998253144011)
    ·
      refine ⟨78785857451039997379716017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52523904967359998253144011 78785857451039997379716017)
      ·
        refine ⟨59089393088279998034787013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78785857451039997379716017 59089393088279998034787013)
        ·
          refine ⟨11079261204052499631522565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59089393088279998034787013 11079261204052499631522565)
          ·
            refine ⟨2077361475759843680910481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11079261204052499631522565 2077361475759843680910481)
            ·
              refine ⟨1558021106819882760682861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2077361475759843680910481 1558021106819882760682861)
              ·
                refine ⟨584257915057456035256073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1558021106819882760682861 584257915057456035256073)
                ·
                  refine ⟨438193436293092026442055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584257915057456035256073 438193436293092026442055)
                  ·
                    rfl

theorem cell20_960051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 2].length) (baseStart_960051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960051 prefixEnd_960051 := by exact prefixLift 960051
  have htrace : WordTrace (prefixWord ++ tailWord_960051) baseStart_960051 baseEnd_960051 := by
    simpa [prefixWord, tailWord_960051, baseEnd_960051] using wordTrace_append hprefix tailTrace_960051
  have hstable : (prefixWord ++ tailWord_960051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960051).length < 2 ^ (prefixWord ++ tailWord_960051).sum := by decide
  have hdescent : baseEnd_960051 < baseStart_960051 := by decide
  rcases family_descends (prefixWord ++ tailWord_960051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960061 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 3]
def baseStart_960061 : Nat := 118140960795 + 960061 * 2 ^ 59
def prefixEnd_960061 : Nat := 4983230072969 + 3 ^ 40 * 960061 * 2
def baseEnd_960061 : Nat := 438198000565576436108681

theorem tailTrace_960061 : CollatzResearch.WordTrace tailWord_960061 prefixEnd_960061 438198000565576436108681 := by
  unfold tailWord_960061
  simp only [CollatzResearch.WordTrace]
  refine ⟨35016301374870437209960037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23344200916580291473306691 35016301374870437209960037)
  ·
    refine ⟨6565556507788206976867507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35016301374870437209960037 6565556507788206976867507)
    ·
      refine ⟨9848334761682310465301261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6565556507788206976867507 9848334761682310465301261)
      ·
        refine ⟨3693125535630866424487973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9848334761682310465301261 3693125535630866424487973)
        ·
          refine ⟨692461037930787454591495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3693125535630866424487973 692461037930787454591495)
          ·
            refine ⟨1038691556896181181887243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692461037930787454591495 1038691556896181181887243)
            ·
              refine ⟨1558037335344271772830865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038691556896181181887243 1558037335344271772830865)
              ·
                refine ⟨1168528001508203829623149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558037335344271772830865 1168528001508203829623149)
                ·
                  refine ⟨438198000565576436108681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168528001508203829623149 438198000565576436108681)
                  ·
                    rfl

theorem cell20_960061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_960061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960061 prefixEnd_960061 := by exact prefixLift 960061
  have htrace : WordTrace (prefixWord ++ tailWord_960061) baseStart_960061 baseEnd_960061 := by
    simpa [prefixWord, tailWord_960061, baseEnd_960061] using wordTrace_append hprefix tailTrace_960061
  have hstable : (prefixWord ++ tailWord_960061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960061).length < 2 ^ (prefixWord ++ tailWord_960061).sum := by decide
  have hdescent : baseEnd_960061 < baseStart_960061 := by decide
  rcases family_descends (prefixWord ++ tailWord_960061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960082 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_960082 : Nat := 118140960795 + 960082 * 2 ^ 59
def prefixEnd_960082 : Nat := 4983230072969 + 3 ^ 40 * 960082 * 2
def baseEnd_960082 : Nat := 438207585537793696408595

theorem tailTrace_960082 : CollatzResearch.WordTrace tailWord_960082 prefixEnd_960082 438207585537793696408595 := by
  unfold tailWord_960082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8754266826948589449118625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23344711538529571864316333 8754266826948589449118625)
  ·
    refine ⟨6565700120211442086838969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8754266826948589449118625 6565700120211442086838969)
    ·
      refine ⟨4924275090158581565129227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6565700120211442086838969 4924275090158581565129227)
      ·
        refine ⟨7386412635237872347693841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4924275090158581565129227 7386412635237872347693841)
        ·
          refine ⟨5539809476428404260770381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7386412635237872347693841 5539809476428404260770381)
          ·
            refine ⟨2077428553660651597788893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5539809476428404260770381 2077428553660651597788893)
            ·
              refine ⟨779035707622744349170835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2077428553660651597788893 779035707622744349170835)
              ·
                refine ⟨1168553561434116523756253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779035707622744349170835 1168553561434116523756253)
                ·
                  refine ⟨438207585537793696408595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168553561434116523756253 438207585537793696408595)
                  ·
                    rfl

theorem cell20_960082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_960082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960082 prefixEnd_960082 := by exact prefixLift 960082
  have htrace : WordTrace (prefixWord ++ tailWord_960082) baseStart_960082 baseEnd_960082 := by
    simpa [prefixWord, tailWord_960082, baseEnd_960082] using wordTrace_append hprefix tailTrace_960082
  have hstable : (prefixWord ++ tailWord_960082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960082).length < 2 ^ (prefixWord ++ tailWord_960082).sum := by decide
  have hdescent : baseEnd_960082 < baseStart_960082 := by decide
  rcases family_descends (prefixWord ++ tailWord_960082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960106 : List Nat := [3, 1, 3, 2, 1, 4, 1, 3, 2]
def baseStart_960106 : Nat := 118140960795 + 960106 * 2 ^ 59
def prefixEnd_960106 : Nat := 4983230072969 + 3 ^ 40 * 960106 * 2
def baseEnd_960106 : Nat := 438218539791756279608497

theorem tailTrace_960106 : CollatzResearch.WordTrace tailWord_960106 prefixEnd_960106 438218539791756279608497 := by
  unfold tailWord_960106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8754485664926852473837043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23345295106471606596898781 8754485664926852473837043)
  ·
    refine ⟨13131728497390278710755565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8754485664926852473837043 13131728497390278710755565)
    ·
      refine ⟨4924398186521354516533337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13131728497390278710755565 4924398186521354516533337)
      ·
        refine ⟨3693298639891015887400003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4924398186521354516533337 3693298639891015887400003)
        ·
          refine ⟨5539947959836523831100005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3693298639891015887400003 5539947959836523831100005)
          ·
            refine ⟨1038740242469348218331251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5539947959836523831100005 1038740242469348218331251)
            ·
              refine ⟨1558110363704022327496877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038740242469348218331251 1558110363704022327496877)
              ·
                refine ⟨584291386389008372811329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1558110363704022327496877 584291386389008372811329)
                ·
                  refine ⟨438218539791756279608497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584291386389008372811329 438218539791756279608497)
                  ·
                    rfl

theorem cell20_960106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_960106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960106 prefixEnd_960106 := by exact prefixLift 960106
  have htrace : WordTrace (prefixWord ++ tailWord_960106) baseStart_960106 baseEnd_960106 := by
    simpa [prefixWord, tailWord_960106, baseEnd_960106] using wordTrace_append hprefix tailTrace_960106
  have hstable : (prefixWord ++ tailWord_960106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960106).length < 2 ^ (prefixWord ++ tailWord_960106).sum := by decide
  have hdescent : baseEnd_960106 < baseStart_960106 := by decide
  rcases family_descends (prefixWord ++ tailWord_960106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960117 : List Nat := [1, 3, 4, 2, 1, 1, 8]
def baseStart_960117 : Nat := 118140960795 + 960117 * 2 ^ 59
def prefixEnd_960117 : Nat := 4983230072969 + 3 ^ 40 * 960117 * 2
def baseEnd_960117 : Nat := 48691506721276570026865

theorem tailTrace_960117 : CollatzResearch.WordTrace tailWord_960117 prefixEnd_960117 48691506721276570026865 := by
  unfold tailWord_960117
  simp only [CollatzResearch.WordTrace]
  refine ⟨35018343862667558773998605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23345562575111705849332403 35018343862667558773998605)
  ·
    refine ⟨13131878948500334540249477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35018343862667558773998605 13131878948500334540249477)
    ·
      refine ⟨2462227302843812726296777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13131878948500334540249477 2462227302843812726296777)
      ·
        refine ⟨1846670477132859544722583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2462227302843812726296777 1846670477132859544722583)
        ·
          refine ⟨2770005715699289317083875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846670477132859544722583 2770005715699289317083875)
          ·
            refine ⟨4155008573548933975625813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770005715699289317083875 4155008573548933975625813)
            ·
              refine ⟨48691506721276570026865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4155008573548933975625813 48691506721276570026865)
              ·
                rfl

theorem cell20_960117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 8].length) (baseStart_960117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960117 prefixEnd_960117 := by exact prefixLift 960117
  have htrace : WordTrace (prefixWord ++ tailWord_960117) baseStart_960117 baseEnd_960117 := by
    simpa [prefixWord, tailWord_960117, baseEnd_960117] using wordTrace_append hprefix tailTrace_960117
  have hstable : (prefixWord ++ tailWord_960117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960117).length < 2 ^ (prefixWord ++ tailWord_960117).sum := by decide
  have hdescent : baseEnd_960117 < baseStart_960117 := by decide
  rcases family_descends (prefixWord ++ tailWord_960117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960124 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 3]
def baseStart_960124 : Nat := 118140960795 + 960124 * 2 ^ 59
def prefixEnd_960124 : Nat := 4983230072969 + 3 ^ 40 * 960124 * 2
def baseEnd_960124 : Nat := 438226755482228217008423

theorem tailTrace_960124 : CollatzResearch.WordTrace tailWord_960124 prefixEnd_960124 438226755482228217008423 := by
  unfold tailWord_960124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17509299586821099484751713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23345732782428132646335617 17509299586821099484751713)
  ·
    refine ⟨13131974690115824613563785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17509299586821099484751713 13131974690115824613563785)
    ·
      refine ⟨9848981017586868460172839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13131974690115824613563785 9848981017586868460172839)
      ·
        refine ⟨14773471526380302690259259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9848981017586868460172839 14773471526380302690259259)
        ·
          refine ⟨22160207289570454035388889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14773471526380302690259259 22160207289570454035388889)
          ·
            refine ⟨16620155467177840526541667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22160207289570454035388889 16620155467177840526541667)
            ·
              refine ⟨24930233200766760789812501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16620155467177840526541667 24930233200766760789812501)
              ·
                refine ⟨1168604681285941912022461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24930233200766760789812501 1168604681285941912022461)
                ·
                  refine ⟨438226755482228217008423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168604681285941912022461 438226755482228217008423)
                  ·
                    rfl

theorem cell20_960124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_960124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960124 prefixEnd_960124 := by exact prefixLift 960124
  have htrace : WordTrace (prefixWord ++ tailWord_960124) baseStart_960124 baseEnd_960124 := by
    simpa [prefixWord, tailWord_960124, baseEnd_960124] using wordTrace_append hprefix tailTrace_960124
  have hstable : (prefixWord ++ tailWord_960124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960124).length < 2 ^ (prefixWord ++ tailWord_960124).sum := by decide
  have hdescent : baseEnd_960124 < baseStart_960124 := by decide
  rcases family_descends (prefixWord ++ tailWord_960124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960145 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_960145 : Nat := 118140960795 + 960145 * 2 ^ 59
def prefixEnd_960145 : Nat := 4983230072969 + 3 ^ 40 * 960145 * 2
def baseEnd_960145 : Nat := 438236340454445477308337

theorem tailTrace_960145 : CollatzResearch.WordTrace tailWord_960145 prefixEnd_960145 438236340454445477308337 := by
  unfold tailWord_960145
  simp only [CollatzResearch.WordTrace]
  refine ⟨35019365106566119556017889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23346243404377413037345259 35019365106566119556017889)
  ·
    refine ⟨26264523829924589667013417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35019365106566119556017889 26264523829924589667013417)
    ·
      refine ⟨19698392872443442250260063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26264523829924589667013417 19698392872443442250260063)
      ·
        refine ⟨29547589308665163375390095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19698392872443442250260063 29547589308665163375390095)
        ·
          refine ⟨44321383962997745063085143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29547589308665163375390095 44321383962997745063085143)
          ·
            refine ⟨66482075944496617594627715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44321383962997745063085143 66482075944496617594627715)
            ·
              refine ⟨99723113916744926391941573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66482075944496617594627715 99723113916744926391941573)
              ·
                refine ⟨18698083859389673698489045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99723113916744926391941573 18698083859389673698489045)
                ·
                  refine ⟨438236340454445477308337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18698083859389673698489045 438236340454445477308337)
                  ·
                    rfl

theorem cell20_960145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_960145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960145 prefixEnd_960145 := by exact prefixLift 960145
  have htrace : WordTrace (prefixWord ++ tailWord_960145) baseStart_960145 baseEnd_960145 := by
    simpa [prefixWord, tailWord_960145, baseEnd_960145] using wordTrace_append hprefix tailTrace_960145
  have hstable : (prefixWord ++ tailWord_960145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960145).length < 2 ^ (prefixWord ++ tailWord_960145).sum := by decide
  have hdescent : baseEnd_960145 < baseStart_960145 := by decide
  rcases family_descends (prefixWord ++ tailWord_960145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960200 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 3]
def baseStart_960200 : Nat := 118140960795 + 960200 * 2 ^ 59
def prefixEnd_960200 : Nat := 4983230072969 + 3 ^ 40 * 960200 * 2
def baseEnd_960200 : Nat := 438261443953109730474779

theorem tailTrace_960200 : CollatzResearch.WordTrace tailWord_960200 prefixEnd_960200 438261443953109730474779 := by
  unfold tailWord_960200
  simp only [CollatzResearch.WordTrace]
  refine ⟨17510685560683431974635027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23347580747577909299513369 17510685560683431974635027)
  ·
    refine ⟨26266028341025147961952541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17510685560683431974635027 26266028341025147961952541)
    ·
      refine ⟨9849760627884430485732203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26266028341025147961952541 9849760627884430485732203)
      ·
        refine ⟨14774640941826645728598305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9849760627884430485732203 14774640941826645728598305)
        ·
          refine ⟨11080980706369984296448729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14774640941826645728598305 11080980706369984296448729)
          ·
            refine ⟨8310735529777488222336547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11080980706369984296448729 8310735529777488222336547)
            ·
              refine ⟨12466103294666232333504821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8310735529777488222336547 12466103294666232333504821)
              ·
                refine ⟨1168697183874959281266077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12466103294666232333504821 1168697183874959281266077)
                ·
                  refine ⟨438261443953109730474779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168697183874959281266077 438261443953109730474779)
                  ·
                    rfl

theorem cell20_960200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_960200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960200 prefixEnd_960200 := by exact prefixLift 960200
  have htrace : WordTrace (prefixWord ++ tailWord_960200) baseStart_960200 baseEnd_960200 := by
    simpa [prefixWord, tailWord_960200, baseEnd_960200] using wordTrace_append hprefix tailTrace_960200
  have hstable : (prefixWord ++ tailWord_960200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960200).length < 2 ^ (prefixWord ++ tailWord_960200).sum := by decide
  have hdescent : baseEnd_960200 < baseStart_960200 := by decide
  rcases family_descends (prefixWord ++ tailWord_960200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960210 : List Nat := [3, 2, 2, 2, 2, 2, 3, 4]
def baseStart_960210 : Nat := 118140960795 + 960210 * 2 ^ 59
def prefixEnd_960210 : Nat := 4983230072969 + 3 ^ 40 * 960210 * 2
def baseEnd_960210 : Nat := 146088669408531380047135

theorem tailTrace_960210 : CollatzResearch.WordTrace tailWord_960210 prefixEnd_960210 146088669408531380047135 := by
  unfold tailWord_960210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8755433962832658914283521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23347823900887090438089389 8755433962832658914283521)
  ·
    refine ⟨6566575472124494185712641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8755433962832658914283521 6566575472124494185712641)
    ·
      refine ⟨4924931604093370639284481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6566575472124494185712641 4924931604093370639284481)
      ·
        refine ⟨3693698703070027979463361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4924931604093370639284481 3693698703070027979463361)
        ·
          refine ⟨2770274027302520984597521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3693698703070027979463361 2770274027302520984597521)
          ·
            refine ⟨2077705520476890738448141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2770274027302520984597521 2077705520476890738448141)
            ·
              refine ⟨779139570178834026918053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2077705520476890738448141 779139570178834026918053)
              ·
                refine ⟨146088669408531380047135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 779139570178834026918053 146088669408531380047135)
                ·
                  rfl

theorem cell20_960210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_960210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960210 prefixEnd_960210 := by exact prefixLift 960210
  have htrace : WordTrace (prefixWord ++ tailWord_960210) baseStart_960210 baseEnd_960210 := by
    simpa [prefixWord, tailWord_960210, baseEnd_960210] using wordTrace_append hprefix tailTrace_960210
  have hstable : (prefixWord ++ tailWord_960210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960210).length < 2 ^ (prefixWord ++ tailWord_960210).sum := by decide
  have hdescent : baseEnd_960210 < baseStart_960210 := by decide
  rcases family_descends (prefixWord ++ tailWord_960210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960224 : List Nat := [2, 1, 1, 3, 1, 2, 3, 5, 2]
def baseStart_960224 : Nat := 118140960795 + 960224 * 2 ^ 59
def prefixEnd_960224 : Nat := 4983230072969 + 3 ^ 40 * 960224 * 2
def baseEnd_960224 : Nat := 438272398207072313674681

theorem tailTrace_960224 : CollatzResearch.WordTrace tailWord_960224 prefixEnd_960224 438272398207072313674681 := by
  unfold tailWord_960224
  simp only [CollatzResearch.WordTrace]
  refine ⟨17511123236639958024071863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23348164315519944032095817 17511123236639958024071863)
  ·
    refine ⟨26266684854959937036107795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17511123236639958024071863 26266684854959937036107795)
    ·
      refine ⟨39400027282439905554161693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26266684854959937036107795 39400027282439905554161693)
      ·
        refine ⟨14775010230914964582810635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39400027282439905554161693 14775010230914964582810635)
        ·
          refine ⟨22162515346372446874215953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14775010230914964582810635 22162515346372446874215953)
          ·
            refine ⟨16621886509779335155661965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22162515346372446874215953 16621886509779335155661965)
            ·
              refine ⟨6233207441167250683373237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16621886509779335155661965 6233207441167250683373237)
              ·
                refine ⟨584363197609429751566241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6233207441167250683373237 584363197609429751566241)
                ·
                  refine ⟨438272398207072313674681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584363197609429751566241 438272398207072313674681)
                  ·
                    rfl

theorem cell20_960224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_960224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960224 prefixEnd_960224 := by exact prefixLift 960224
  have htrace : WordTrace (prefixWord ++ tailWord_960224) baseStart_960224 baseEnd_960224 := by
    simpa [prefixWord, tailWord_960224, baseEnd_960224] using wordTrace_append hprefix tailTrace_960224
  have hstable : (prefixWord ++ tailWord_960224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960224).length < 2 ^ (prefixWord ++ tailWord_960224).sum := by decide
  have hdescent : baseEnd_960224 < baseStart_960224 := by decide
  rcases family_descends (prefixWord ++ tailWord_960224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960238 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_960238 : Nat := 118140960795 + 960238 * 2 ^ 59
def prefixEnd_960238 : Nat := 4983230072969 + 3 ^ 40 * 960238 * 2
def baseEnd_960238 : Nat := 438278788188550487207957

theorem tailTrace_960238 : CollatzResearch.WordTrace tailWord_960238 prefixEnd_960238 438278788188550487207957 := by
  unfold tailWord_960238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377844636903649554894171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23348504730152797626102245 4377844636903649554894171)
  ·
    refine ⟨6566766955355474332341257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4377844636903649554894171 6566766955355474332341257)
    ·
      refine ⟨4925075216516605749255943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6566766955355474332341257 4925075216516605749255943)
      ·
        refine ⟨7387612824774908623883915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4925075216516605749255943 7387612824774908623883915)
        ·
          refine ⟨11081419237162362935825873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7387612824774908623883915 11081419237162362935825873)
          ·
            refine ⟨8311064427871772201869405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11081419237162362935825873 8311064427871772201869405)
            ·
              refine ⟨3116649160451914575701027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8311064427871772201869405 3116649160451914575701027)
              ·
                refine ⟨4674973740677871863551541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116649160451914575701027 4674973740677871863551541)
                ·
                  refine ⟨438278788188550487207957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4674973740677871863551541 438278788188550487207957)
                  ·
                    rfl

theorem cell20_960238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_960238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960238 prefixEnd_960238 := by exact prefixLift 960238
  have htrace : WordTrace (prefixWord ++ tailWord_960238) baseStart_960238 baseEnd_960238 := by
    simpa [prefixWord, tailWord_960238, baseEnd_960238] using wordTrace_append hprefix tailTrace_960238
  have hstable : (prefixWord ++ tailWord_960238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960238).length < 2 ^ (prefixWord ++ tailWord_960238).sum := by decide
  have hdescent : baseEnd_960238 < baseStart_960238 := by decide
  rcases family_descends (prefixWord ++ tailWord_960238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960252 : List Nat := [2, 2, 2, 1, 3, 1, 2, 7]
def baseStart_960252 : Nat := 118140960795 + 960252 * 2 ^ 59
def prefixEnd_960252 : Nat := 4983230072969 + 3 ^ 40 * 960252 * 2
def baseEnd_960252 : Nat := 146095059390009553580411

theorem tailTrace_960252 : CollatzResearch.WordTrace tailWord_960252 prefixEnd_960252 146095059390009553580411 := by
  unfold tailWord_960252
  simp only [CollatzResearch.WordTrace]
  refine ⟨17511633858589238415081505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23348845144785651220108673 17511633858589238415081505)
  ·
    refine ⟨13133725393941928811311129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17511633858589238415081505 13133725393941928811311129)
    ·
      refine ⟨9850294045456446608483347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13133725393941928811311129 9850294045456446608483347)
      ·
        refine ⟨14775441068184669912725021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9850294045456446608483347 14775441068184669912725021)
        ·
          refine ⟨5540790400569251217271883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14775441068184669912725021 5540790400569251217271883)
          ·
            refine ⟨8311185600853876825907825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5540790400569251217271883 8311185600853876825907825)
            ·
              refine ⟨6233389200640407619430869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8311185600853876825907825 6233389200640407619430869)
              ·
                refine ⟨146095059390009553580411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6233389200640407619430869 146095059390009553580411)
                ·
                  rfl

theorem cell20_960252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_960252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960252 prefixEnd_960252 := by exact prefixLift 960252
  have htrace : WordTrace (prefixWord ++ tailWord_960252) baseStart_960252 baseEnd_960252 := by
    simpa [prefixWord, tailWord_960252, baseEnd_960252] using wordTrace_append hprefix tailTrace_960252
  have hstable : (prefixWord ++ tailWord_960252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960252).length < 2 ^ (prefixWord ++ tailWord_960252).sum := by decide
  have hdescent : baseEnd_960252 < baseStart_960252 := by decide
  rcases family_descends (prefixWord ++ tailWord_960252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960279 : List Nat := [1, 1, 3, 4, 2, 1, 3, 3, 2]
def baseStart_960279 : Nat := 118140960795 + 960279 * 2 ^ 59
def prefixEnd_960279 : Nat := 4983230072969 + 3 ^ 40 * 960279 * 2
def baseEnd_960279 : Nat := 438297501705736566841123

theorem tailTrace_960279 : CollatzResearch.WordTrace tailWord_960279 prefixEnd_960279 438297501705736566841123 := by
  unfold tailWord_960279
  simp only [CollatzResearch.WordTrace]
  refine ⟨35024252488080660441395891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23349501658720440294263927 35024252488080660441395891)
  ·
    refine ⟨52536378732120990662093837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35024252488080660441395891 52536378732120990662093837)
    ·
      refine ⟨19701142024545371498285189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52536378732120990662093837 19701142024545371498285189)
      ·
        refine ⟨3693964129602257155928473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19701142024545371498285189 3693964129602257155928473)
        ·
          refine ⟨2770473097201692866946355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3693964129602257155928473 2770473097201692866946355)
          ·
            refine ⟨4155709645802539300419533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770473097201692866946355 4155709645802539300419533)
            ·
              refine ⟨1558391117175952237657325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4155709645802539300419533 1558391117175952237657325)
              ·
                refine ⟨584396668940982089121497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1558391117175952237657325 584396668940982089121497)
                ·
                  refine ⟨438297501705736566841123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584396668940982089121497 438297501705736566841123)
                  ·
                    rfl

theorem cell20_960279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 2].length) (baseStart_960279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960279 prefixEnd_960279 := by exact prefixLift 960279
  have htrace : WordTrace (prefixWord ++ tailWord_960279) baseStart_960279 baseEnd_960279 := by
    simpa [prefixWord, tailWord_960279, baseEnd_960279] using wordTrace_append hprefix tailTrace_960279
  have hstable : (prefixWord ++ tailWord_960279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960279).length < 2 ^ (prefixWord ++ tailWord_960279).sum := by decide
  have hdescent : baseEnd_960279 < baseStart_960279 := by decide
  rcases family_descends (prefixWord ++ tailWord_960279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960296 : List Nat := [2, 1, 5, 1, 1, 3, 3, 2, 2]
def baseStart_960296 : Nat := 118140960795 + 960296 * 2 ^ 59
def prefixEnd_960296 : Nat := 4983230072969 + 3 ^ 40 * 960296 * 2
def baseEnd_960296 : Nat := 438305260968960063274387

theorem tailTrace_960296 : CollatzResearch.WordTrace tailWord_960296 prefixEnd_960296 438305260968960063274387 := by
  unfold tailWord_960296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17512436264509536172382371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23349915019346048229843161 17512436264509536172382371)
  ·
    refine ⟨26268654396764304258573557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17512436264509536172382371 26268654396764304258573557)
    ·
      refine ⟨2462686349696653524241271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26268654396764304258573557 2462686349696653524241271)
      ·
        refine ⟨3694029524544980286361907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462686349696653524241271 3694029524544980286361907)
        ·
          refine ⟨5541044286817470429542861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3694029524544980286361907 5541044286817470429542861)
          ·
            refine ⟨2077891607556551411078573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5541044286817470429542861 2077891607556551411078573)
            ·
              refine ⟨779209352833706779154465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2077891607556551411078573 779209352833706779154465)
              ·
                refine ⟨584407014625280084365849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779209352833706779154465 584407014625280084365849)
                ·
                  refine ⟨438305260968960063274387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584407014625280084365849 438305260968960063274387)
                  ·
                    rfl

theorem cell20_960296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_960296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960296 prefixEnd_960296 := by exact prefixLift 960296
  have htrace : WordTrace (prefixWord ++ tailWord_960296) baseStart_960296 baseEnd_960296 := by
    simpa [prefixWord, tailWord_960296, baseEnd_960296] using wordTrace_append hprefix tailTrace_960296
  have hstable : (prefixWord ++ tailWord_960296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960296).length < 2 ^ (prefixWord ++ tailWord_960296).sum := by decide
  have hdescent : baseEnd_960296 < baseStart_960296 := by decide
  rcases family_descends (prefixWord ++ tailWord_960296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960300 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 4]
def baseStart_960300 : Nat := 118140960795 + 960300 * 2 ^ 59
def prefixEnd_960300 : Nat := 4983230072969 + 3 ^ 40 * 960300 * 2
def baseEnd_960300 : Nat := 438307086677953827141037

theorem tailTrace_960300 : CollatzResearch.WordTrace tailWord_960300 prefixEnd_960300 438307086677953827141037 := by
  unfold tailWord_960300
  simp only [CollatzResearch.WordTrace]
  refine ⟨17512509210502290513955177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23350012280669720685273569 17512509210502290513955177)
  ·
    refine ⟨13134381907876717885466383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17512509210502290513955177 13134381907876717885466383)
    ·
      refine ⟨19701572861815076828199575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13134381907876717885466383 19701572861815076828199575)
      ·
        refine ⟨29552359292722615242299363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19701572861815076828199575 29552359292722615242299363)
        ·
          refine ⟨44328538939083922863449045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29552359292722615242299363 44328538939083922863449045)
          ·
            refine ⟨1038950131384779442112087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44328538939083922863449045 1038950131384779442112087)
            ·
              refine ⟨1558425197077169163168131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038950131384779442112087 1558425197077169163168131)
              ·
                refine ⟨2337637795615753744752197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1558425197077169163168131 2337637795615753744752197)
                ·
                  refine ⟨438307086677953827141037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2337637795615753744752197 438307086677953827141037)
                  ·
                    rfl

theorem cell20_960300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_960300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960300 prefixEnd_960300 := by exact prefixLift 960300
  have htrace : WordTrace (prefixWord ++ tailWord_960300) baseStart_960300 baseEnd_960300 := by
    simpa [prefixWord, tailWord_960300, baseEnd_960300] using wordTrace_append hprefix tailTrace_960300
  have hstable : (prefixWord ++ tailWord_960300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960300).length < 2 ^ (prefixWord ++ tailWord_960300).sum := by decide
  have hdescent : baseEnd_960300 < baseStart_960300 := by decide
  rcases family_descends (prefixWord ++ tailWord_960300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960307 : List Nat := [1, 1, 1, 2, 7, 1, 2, 5]
def baseStart_960307 : Nat := 118140960795 + 960307 * 2 ^ 59
def prefixEnd_960307 : Nat := 4983230072969 + 3 ^ 40 * 960307 * 2
def baseEnd_960307 : Nat := 146103427222897637969225

theorem tailTrace_960307 : CollatzResearch.WordTrace tailWord_960307 prefixEnd_960307 146103427222897637969225 := by
  unfold tailWord_960307
  simp only [CollatzResearch.WordTrace]
  refine ⟨35025273731979221223415175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23350182487986147482276783 35025273731979221223415175)
  ·
    refine ⟨52537910597968831835122763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35025273731979221223415175 52537910597968831835122763)
    ·
      refine ⟨78806865896953247752684145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52537910597968831835122763 78806865896953247752684145)
      ·
        refine ⟨59105149422714935814513109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78806865896953247752684145 59105149422714935814513109)
        ·
          refine ⟨1385276939594881308152651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 59105149422714935814513109 1385276939594881308152651)
          ·
            refine ⟨2077915409392321962228977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385276939594881308152651 2077915409392321962228977)
            ·
              refine ⟨1558436557044241471671733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2077915409392321962228977 1558436557044241471671733)
              ·
                refine ⟨146103427222897637969225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1558436557044241471671733 146103427222897637969225)
                ·
                  rfl

theorem cell20_960307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 5].length) (baseStart_960307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960307 prefixEnd_960307 := by exact prefixLift 960307
  have htrace : WordTrace (prefixWord ++ tailWord_960307) baseStart_960307 baseEnd_960307 := by
    simpa [prefixWord, tailWord_960307, baseEnd_960307] using wordTrace_append hprefix tailTrace_960307
  have hstable : (prefixWord ++ tailWord_960307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960307).length < 2 ^ (prefixWord ++ tailWord_960307).sum := by decide
  have hdescent : baseEnd_960307 < baseStart_960307 := by decide
  rcases family_descends (prefixWord ++ tailWord_960307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960310 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_960310 : Nat := 118140960795 + 960310 * 2 ^ 59
def prefixEnd_960310 : Nat := 4983230072969 + 3 ^ 40 * 960310 * 2
def baseEnd_960310 : Nat := 438311650950438236807663

theorem tailTrace_960310 : CollatzResearch.WordTrace tailWord_960310 prefixEnd_960310 438311650950438236807663 := by
  unfold tailWord_960310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2189086446935522045985899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23350255433978901823849589 2189086446935522045985899)
  ·
    refine ⟨3283629670403283068978849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2189086446935522045985899 3283629670403283068978849)
    ·
      refine ⟨2462722252802462301734137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3283629670403283068978849 2462722252802462301734137)
      ·
        refine ⟨1847041689601846726300603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2462722252802462301734137 1847041689601846726300603)
        ·
          refine ⟨2770562534402770089450905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1847041689601846726300603 2770562534402770089450905)
          ·
            refine ⟨2077921900802077567088179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2770562534402770089450905 2077921900802077567088179)
            ·
              refine ⟨3116882851203116350632269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077921900802077567088179 3116882851203116350632269)
              ·
                refine ⟨1168831069201168631487101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3116882851203116350632269 1168831069201168631487101)
                ·
                  refine ⟨438311650950438236807663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168831069201168631487101 438311650950438236807663)
                  ·
                    rfl

theorem cell20_960310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_960310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960310 prefixEnd_960310 := by exact prefixLift 960310
  have htrace : WordTrace (prefixWord ++ tailWord_960310) baseStart_960310 baseEnd_960310 := by
    simpa [prefixWord, tailWord_960310, baseEnd_960310] using wordTrace_append hprefix tailTrace_960310
  have hstable : (prefixWord ++ tailWord_960310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960310).length < 2 ^ (prefixWord ++ tailWord_960310).sum := by decide
  have hdescent : baseEnd_960310 < baseStart_960310 := by decide
  rcases family_descends (prefixWord ++ tailWord_960310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960328 : List Nat := [2, 1, 3, 1, 1, 4, 2, 6]
def baseStart_960328 : Nat := 118140960795 + 960328 * 2 ^ 59
def prefixEnd_960328 : Nat := 4983230072969 + 3 ^ 40 * 960328 * 2
def baseEnd_960328 : Nat := 146106622213636724735863

theorem tailTrace_960328 : CollatzResearch.WordTrace tailWord_960328 prefixEnd_960328 146106622213636724735863 := by
  unfold tailWord_960328
  simp only [CollatzResearch.WordTrace]
  refine ⟨17513019832451570904964819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23350693109935427873286425 17513019832451570904964819)
  ·
    refine ⟨26269529748677356357447229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17513019832451570904964819 26269529748677356357447229)
    ·
      refine ⟨9851073655754008634042711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26269529748677356357447229 9851073655754008634042711)
      ·
        refine ⟨14776610483631012951064067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9851073655754008634042711 14776610483631012951064067)
        ·
          refine ⟨22164915725446519426596101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14776610483631012951064067 22164915725446519426596101)
          ·
            refine ⟨4155921698521222392486769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22164915725446519426596101 4155921698521222392486769)
            ·
              refine ⟨3116941273890916794365077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4155921698521222392486769 3116941273890916794365077)
              ·
                refine ⟨146106622213636724735863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3116941273890916794365077 146106622213636724735863)
                ·
                  rfl

theorem cell20_960328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_960328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960328 prefixEnd_960328 := by exact prefixLift 960328
  have htrace : WordTrace (prefixWord ++ tailWord_960328) baseStart_960328 baseEnd_960328 := by
    simpa [prefixWord, tailWord_960328, baseEnd_960328] using wordTrace_append hprefix tailTrace_960328
  have hstable : (prefixWord ++ tailWord_960328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960328).length < 2 ^ (prefixWord ++ tailWord_960328).sum := by decide
  have hdescent : baseEnd_960328 < baseStart_960328 := by decide
  rcases family_descends (prefixWord ++ tailWord_960328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960348 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 3]
def baseStart_960348 : Nat := 118140960795 + 960348 * 2 ^ 59
def prefixEnd_960348 : Nat := 4983230072969 + 3 ^ 40 * 960348 * 2
def baseEnd_960348 : Nat := 438328995185878993540841

theorem tailTrace_960348 : CollatzResearch.WordTrace tailWord_960348 prefixEnd_960348 438328995185878993540841 := by
  unfold tailWord_960348
  simp only [CollatzResearch.WordTrace]
  refine ⟨17513384562415342612828849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23351179416553790150438465 17513384562415342612828849)
  ·
    refine ⟨13135038421811506959621637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17513384562415342612828849 13135038421811506959621637)
    ·
      refine ⟨2462819704089657554929057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13135038421811506959621637 2462819704089657554929057)
      ·
        refine ⟨1847114778067243166196793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2462819704089657554929057 1847114778067243166196793)
        ·
          refine ⟨1385336083550432374647595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1847114778067243166196793 1385336083550432374647595)
          ·
            refine ⟨2078004125325648561971393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385336083550432374647595 2078004125325648561971393)
            ·
              refine ⟨1558503093994236421478545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2078004125325648561971393 1558503093994236421478545)
              ·
                refine ⟨1168877320495677316108909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558503093994236421478545 1168877320495677316108909)
                ·
                  refine ⟨438328995185878993540841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168877320495677316108909 438328995185878993540841)
                  ·
                    rfl

theorem cell20_960348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_960348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960348 prefixEnd_960348 := by exact prefixLift 960348
  have htrace : WordTrace (prefixWord ++ tailWord_960348) baseStart_960348 baseEnd_960348 := by
    simpa [prefixWord, tailWord_960348, baseEnd_960348] using wordTrace_append hprefix tailTrace_960348
  have hstable : (prefixWord ++ tailWord_960348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960348).length < 2 ^ (prefixWord ++ tailWord_960348).sum := by decide
  have hdescent : baseEnd_960348 < baseStart_960348 := by decide
  rcases family_descends (prefixWord ++ tailWord_960348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960352 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 3]
def baseStart_960352 : Nat := 118140960795 + 960352 * 2 ^ 59
def prefixEnd_960352 : Nat := 4983230072969 + 3 ^ 40 * 960352 * 2
def baseEnd_960352 : Nat := 438330820894872757407491

theorem tailTrace_960352 : CollatzResearch.WordTrace tailWord_960352 prefixEnd_960352 438330820894872757407491 := by
  unfold tailWord_960352
  simp only [CollatzResearch.WordTrace]
  refine ⟨17513457508408096954401655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23351276677877462605868873 17513457508408096954401655)
  ·
    refine ⟨26270186262612145431602483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17513457508408096954401655 26270186262612145431602483)
    ·
      refine ⟨39405279393918218147403725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26270186262612145431602483 39405279393918218147403725)
      ·
        refine ⟨14776979772719331805276397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39405279393918218147403725 14776979772719331805276397)
        ·
          refine ⟨5541367414769749426978649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14776979772719331805276397 5541367414769749426978649)
          ·
            refine ⟨4156025561077312070233987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5541367414769749426978649 4156025561077312070233987)
            ·
              refine ⟨6234038341615968105350981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4156025561077312070233987 6234038341615968105350981)
              ·
                refine ⟨1168882189052994019753309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6234038341615968105350981 1168882189052994019753309)
                ·
                  refine ⟨438330820894872757407491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168882189052994019753309 438330820894872757407491)
                  ·
                    rfl

theorem cell20_960352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_960352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960352 prefixEnd_960352 := by exact prefixLift 960352
  have htrace : WordTrace (prefixWord ++ tailWord_960352) baseStart_960352 baseEnd_960352 := by
    simpa [prefixWord, tailWord_960352, baseEnd_960352] using wordTrace_append hprefix tailTrace_960352
  have hstable : (prefixWord ++ tailWord_960352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960352).length < 2 ^ (prefixWord ++ tailWord_960352).sum := by decide
  have hdescent : baseEnd_960352 < baseStart_960352 := by decide
  rcases family_descends (prefixWord ++ tailWord_960352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960355 : List Nat := [1, 1, 1, 5, 4, 1, 1, 4, 2]
def baseStart_960355 : Nat := 118140960795 + 960355 * 2 ^ 59
def prefixEnd_960355 : Nat := 4983230072969 + 3 ^ 40 * 960355 * 2
def baseEnd_960355 : Nat := 438332190176618080307479

theorem tailTrace_960355 : CollatzResearch.WordTrace tailWord_960355 prefixEnd_960355 438332190176618080307479 := by
  unfold tailWord_960355
  simp only [CollatzResearch.WordTrace]
  refine ⟨35027024435805325421162519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23351349623870216947441679 35027024435805325421162519)
  ·
    refine ⟨52540536653707988131743779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35027024435805325421162519 52540536653707988131743779)
    ·
      refine ⟨78810804980561982197615669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52540536653707988131743779 78810804980561982197615669)
      ·
        refine ⟨7388512966927685831026469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78810804980561982197615669 7388512966927685831026469)
        ·
          refine ⟨1385346181298941093317463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7388512966927685831026469 1385346181298941093317463)
          ·
            refine ⟨2078019271948411639976195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385346181298941093317463 2078019271948411639976195)
            ·
              refine ⟨3117028907922617459964293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078019271948411639976195 3117028907922617459964293)
              ·
                refine ⟨584442920235490773743305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3117028907922617459964293 584442920235490773743305)
                ·
                  refine ⟨438332190176618080307479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584442920235490773743305 438332190176618080307479)
                  ·
                    rfl

theorem cell20_960355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 2].length) (baseStart_960355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960355 prefixEnd_960355 := by exact prefixLift 960355
  have htrace : WordTrace (prefixWord ++ tailWord_960355) baseStart_960355 baseEnd_960355 := by
    simpa [prefixWord, tailWord_960355, baseEnd_960355] using wordTrace_append hprefix tailTrace_960355
  have hstable : (prefixWord ++ tailWord_960355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960355).length < 2 ^ (prefixWord ++ tailWord_960355).sum := by decide
  have hdescent : baseEnd_960355 < baseStart_960355 := by decide
  rcases family_descends (prefixWord ++ tailWord_960355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960359 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_960359 : Nat := 118140960795 + 960359 * 2 ^ 59
def prefixEnd_960359 : Nat := 4983230072969 + 3 ^ 40 * 960359 * 2
def baseEnd_960359 : Nat := 438334015885611844174129

theorem tailTrace_960359 : CollatzResearch.WordTrace tailWord_960359 prefixEnd_960359 438334015885611844174129 := by
  unfold tailWord_960359
  simp only [CollatzResearch.WordTrace]
  refine ⟨35027170327790834104308131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23351446885193889402872087 35027170327790834104308131)
  ·
    refine ⟨52540755491686251156462197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35027170327790834104308131 52540755491686251156462197)
    ·
      refine ⟨4925695827345586045918331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52540755491686251156462197 4925695827345586045918331)
      ·
        refine ⟨7388543741018379068877497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4925695827345586045918331 7388543741018379068877497)
        ·
          refine ⟨5541407805763784301658123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7388543741018379068877497 5541407805763784301658123)
          ·
            refine ⟨8312111708645676452487185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541407805763784301658123 8312111708645676452487185)
            ·
              refine ⟨6234083781484257339365389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8312111708645676452487185 6234083781484257339365389)
              ·
                refine ⟨2337781418056596502262021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6234083781484257339365389 2337781418056596502262021)
                ·
                  refine ⟨438334015885611844174129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2337781418056596502262021 438334015885611844174129)
                  ·
                    rfl

theorem cell20_960359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_960359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960359 prefixEnd_960359 := by exact prefixLift 960359
  have htrace : WordTrace (prefixWord ++ tailWord_960359) baseStart_960359 baseEnd_960359 := by
    simpa [prefixWord, tailWord_960359, baseEnd_960359] using wordTrace_append hprefix tailTrace_960359
  have hstable : (prefixWord ++ tailWord_960359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960359).length < 2 ^ (prefixWord ++ tailWord_960359).sum := by decide
  have hdescent : baseEnd_960359 < baseStart_960359 := by decide
  rcases family_descends (prefixWord ++ tailWord_960359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960407 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 3]
def baseStart_960407 : Nat := 118140960795 + 960407 * 2 ^ 59
def prefixEnd_960407 : Nat := 4983230072969 + 3 ^ 40 * 960407 * 2
def baseEnd_960407 : Nat := 438355924393537010573933

theorem tailTrace_960407 : CollatzResearch.WordTrace tailWord_960407 prefixEnd_960407 438355924393537010573933 := by
  unfold tailWord_960407
  simp only [CollatzResearch.WordTrace]
  refine ⟨35028921031616938302055475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23352614021077958868036983 35028921031616938302055475)
  ·
    refine ⟨52543381547425407453083213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35028921031616938302055475 52543381547425407453083213)
    ·
      refine ⟨19703768080284527794906205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52543381547425407453083213 19703768080284527794906205)
      ·
        refine ⟨7388913030106697923089827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19703768080284527794906205 7388913030106697923089827)
        ·
          refine ⟨11083369545160046884634741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7388913030106697923089827 11083369545160046884634741)
          ·
            refine ⟨1039065894858754395434507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11083369545160046884634741 1039065894858754395434507)
            ·
              refine ⟨1558598842288131593151761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039065894858754395434507 1558598842288131593151761)
              ·
                refine ⟨1168949131716098694863821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558598842288131593151761 1168949131716098694863821)
                ·
                  refine ⟨438355924393537010573933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168949131716098694863821 438355924393537010573933)
                  ·
                    rfl

theorem cell20_960407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 3].length) (baseStart_960407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960407 prefixEnd_960407 := by exact prefixLift 960407
  have htrace : WordTrace (prefixWord ++ tailWord_960407) baseStart_960407 baseEnd_960407 := by
    simpa [prefixWord, tailWord_960407, baseEnd_960407] using wordTrace_append hprefix tailTrace_960407
  have hstable : (prefixWord ++ tailWord_960407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960407).length < 2 ^ (prefixWord ++ tailWord_960407).sum := by decide
  have hdescent : baseEnd_960407 < baseStart_960407 := by decide
  rcases family_descends (prefixWord ++ tailWord_960407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960483 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 3]
def baseStart_960483 : Nat := 118140960795 + 960483 * 2 ^ 59
def prefixEnd_960483 : Nat := 4983230072969 + 3 ^ 40 * 960483 * 2
def baseEnd_960483 : Nat := 438390612864418524040289

theorem tailTrace_960483 : CollatzResearch.WordTrace tailWord_960483 prefixEnd_960483 438390612864418524040289 := by
  unfold tailWord_960483
  simp only [CollatzResearch.WordTrace]
  refine ⟨35031692979341603281822103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23354461986227735521214735 35031692979341603281822103)
  ·
    refine ⟨52547539469012404922733155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35031692979341603281822103 52547539469012404922733155)
    ·
      refine ⟨78821309203518607384099733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52547539469012404922733155 78821309203518607384099733)
      ·
        refine ⟨3694748868914934721129675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78821309203518607384099733 3694748868914934721129675)
        ·
          refine ⟨5542123303372402081694513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3694748868914934721129675 5542123303372402081694513)
          ·
            refine ⟨4156592477529301561270885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5542123303372402081694513 4156592477529301561270885)
            ·
              refine ⟨779361089536744042738291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4156592477529301561270885 779361089536744042738291)
              ·
                refine ⟨1169041634305116064107437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779361089536744042738291 1169041634305116064107437)
                ·
                  refine ⟨438390612864418524040289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169041634305116064107437 438390612864418524040289)
                  ·
                    rfl

theorem cell20_960483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 3].length) (baseStart_960483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960483 prefixEnd_960483 := by exact prefixLift 960483
  have htrace : WordTrace (prefixWord ++ tailWord_960483) baseStart_960483 baseEnd_960483 := by
    simpa [prefixWord, tailWord_960483, baseEnd_960483] using wordTrace_append hprefix tailTrace_960483
  have hstable : (prefixWord ++ tailWord_960483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960483).length < 2 ^ (prefixWord ++ tailWord_960483).sum := by decide
  have hdescent : baseEnd_960483 < baseStart_960483 := by decide
  rcases family_descends (prefixWord ++ tailWord_960483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960539 : List Nat := [1, 1, 1, 1, 1, 1, 3, 11]
def baseStart_960539 : Nat := 118140960795 + 960539 * 2 ^ 59
def prefixEnd_960539 : Nat := 4983230072969 + 3 ^ 40 * 960539 * 2
def baseEnd_960539 : Nat := 146138724263443739391131

theorem tailTrace_960539 : CollatzResearch.WordTrace tailWord_960539 prefixEnd_960539 146138724263443739391131 := by
  unfold tailWord_960539
  simp only [CollatzResearch.WordTrace]
  refine ⟨35033735467138724845860671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23355823644759149897240447 35033735467138724845860671)
  ·
    refine ⟨52550603200708087268791007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35033735467138724845860671 52550603200708087268791007)
    ·
      refine ⟨78825904801062130903186511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52550603200708087268791007 78825904801062130903186511)
      ·
        refine ⟨118238857201593196354779767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78825904801062130903186511 118238857201593196354779767)
        ·
          refine ⟨177358285802389794532169651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118238857201593196354779767 177358285802389794532169651)
          ·
            refine ⟨266037428703584691798254477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177358285802389794532169651 266037428703584691798254477)
            ·
              refine ⟨99764035763844259424345429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266037428703584691798254477 99764035763844259424345429)
              ·
                refine ⟨146138724263443739391131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 99764035763844259424345429 146138724263443739391131)
                ·
                  rfl

theorem cell20_960539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_960539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960539 prefixEnd_960539 := by exact prefixLift 960539
  have htrace : WordTrace (prefixWord ++ tailWord_960539) baseStart_960539 baseEnd_960539 := by
    simpa [prefixWord, tailWord_960539, baseEnd_960539] using wordTrace_append hprefix tailTrace_960539
  have hstable : (prefixWord ++ tailWord_960539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960539).length < 2 ^ (prefixWord ++ tailWord_960539).sum := by decide
  have hdescent : baseEnd_960539 < baseStart_960539 := by decide
  rcases family_descends (prefixWord ++ tailWord_960539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960549 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 4]
def baseStart_960549 : Nat := 118140960795 + 960549 * 2 ^ 59
def prefixEnd_960549 : Nat := 4983230072969 + 3 ^ 40 * 960549 * 2
def baseEnd_960549 : Nat := 438420737062815627840019

theorem tailTrace_960549 : CollatzResearch.WordTrace tailWord_960549 prefixEnd_960549 438420737062815627840019 := by
  unfold tailWord_960549
  simp only [CollatzResearch.WordTrace]
  refine ⟨35034100197102496553724701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23356066798068331035816467 35034100197102496553724701)
  ·
    refine ⟨13137787573913436207646763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35034100197102496553724701 13137787573913436207646763)
    ·
      refine ⟨19706681360870154311470145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13137787573913436207646763 19706681360870154311470145)
      ·
        refine ⟨14780011020652615733602609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19706681360870154311470145 14780011020652615733602609)
        ·
          refine ⟨11085008265489461800201957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14780011020652615733602609 11085008265489461800201957)
          ·
            refine ⟨2078439049779274087537867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11085008265489461800201957 2078439049779274087537867)
            ·
              refine ⟨3117658574668911131306801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078439049779274087537867 3117658574668911131306801)
              ·
                refine ⟨2338243931001683348480101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3117658574668911131306801 2338243931001683348480101)
                ·
                  refine ⟨438420737062815627840019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338243931001683348480101 438420737062815627840019)
                  ·
                    rfl

theorem cell20_960549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_960549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960549 prefixEnd_960549 := by exact prefixLift 960549
  have htrace : WordTrace (prefixWord ++ tailWord_960549) baseStart_960549 baseEnd_960549 := by
    simpa [prefixWord, tailWord_960549, baseEnd_960549] using wordTrace_append hprefix tailTrace_960549
  have hstable : (prefixWord ++ tailWord_960549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960549).length < 2 ^ (prefixWord ++ tailWord_960549).sum := by decide
  have hdescent : baseEnd_960549 < baseStart_960549 := by decide
  rcases family_descends (prefixWord ++ tailWord_960549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960570 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_960570 : Nat := 118140960795 + 960570 * 2 ^ 59
def prefixEnd_960570 : Nat := 4983230072969 + 3 ^ 40 * 960570 * 2
def baseEnd_960570 : Nat := 438430322035032888139933

theorem tailTrace_960570 : CollatzResearch.WordTrace tailWord_960570 prefixEnd_960570 438430322035032888139933 := by
  unfold tailWord_960570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8758716532506604285059791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23356577420017611426826109 8758716532506604285059791)
  ·
    refine ⟨13138074798759906427589687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8758716532506604285059791 13138074798759906427589687)
    ·
      refine ⟨19707112198139859641384531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13138074798759906427589687 19707112198139859641384531)
      ·
        refine ⟨29560668297209789462076797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19707112198139859641384531 29560668297209789462076797)
        ·
          refine ⟨11085250611453671048278799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29560668297209789462076797 11085250611453671048278799)
          ·
            refine ⟨16627875917180506572418199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11085250611453671048278799 16627875917180506572418199)
            ·
              refine ⟨24941813875770759858627299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16627875917180506572418199 24941813875770759858627299)
              ·
                refine ⟨37412720813656139787940949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24941813875770759858627299 37412720813656139787940949)
                ·
                  refine ⟨438430322035032888139933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37412720813656139787940949 438430322035032888139933)
                  ·
                    rfl

theorem cell20_960570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_960570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960570 prefixEnd_960570 := by exact prefixLift 960570
  have htrace : WordTrace (prefixWord ++ tailWord_960570) baseStart_960570 baseEnd_960570 := by
    simpa [prefixWord, tailWord_960570, baseEnd_960570] using wordTrace_append hprefix tailTrace_960570
  have hstable : (prefixWord ++ tailWord_960570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960570).length < 2 ^ (prefixWord ++ tailWord_960570).sum := by decide
  have hdescent : baseEnd_960570 < baseStart_960570 := by decide
  rcases family_descends (prefixWord ++ tailWord_960570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960597 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 3]
def baseStart_960597 : Nat := 118140960795 + 960597 * 2 ^ 59
def prefixEnd_960597 : Nat := 4983230072969 + 3 ^ 40 * 960597 * 2
def baseEnd_960597 : Nat := 438442645570740794239823

theorem tailTrace_960597 : CollatzResearch.WordTrace tailWord_960597 prefixEnd_960597 438442645570740794239823 := by
  unfold tailWord_960597
  simp only [CollatzResearch.WordTrace]
  refine ⟨35035850900928600751472045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23357233933952400500981363 35035850900928600751472045)
  ·
    refine ⟨13138444087848225281802017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35035850900928600751472045 13138444087848225281802017)
    ·
      refine ⟨9853833065886168961351513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13138444087848225281802017 9853833065886168961351513)
      ·
        refine ⟨7390374799414626721013635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9853833065886168961351513 7390374799414626721013635)
        ·
          refine ⟨11085562199121940081520453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390374799414626721013635 11085562199121940081520453)
          ·
            refine ⟨2078542912335363765285085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11085562199121940081520453 2078542912335363765285085)
            ·
              refine ⟨779453592125761411981907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2078542912335363765285085 779453592125761411981907)
              ·
                refine ⟨1169180388188642117972861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779453592125761411981907 1169180388188642117972861)
                ·
                  refine ⟨438442645570740794239823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169180388188642117972861 438442645570740794239823)
                  ·
                    rfl

theorem cell20_960597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_960597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960597 prefixEnd_960597 := by exact prefixLift 960597
  have htrace : WordTrace (prefixWord ++ tailWord_960597) baseStart_960597 baseEnd_960597 := by
    simpa [prefixWord, tailWord_960597, baseEnd_960597] using wordTrace_append hprefix tailTrace_960597
  have hstable : (prefixWord ++ tailWord_960597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960597).length < 2 ^ (prefixWord ++ tailWord_960597).sum := by decide
  have hdescent : baseEnd_960597 < baseStart_960597 := by decide
  rcases family_descends (prefixWord ++ tailWord_960597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960693 : List Nat := [1, 3, 3, 4, 1, 2, 2, 2, 2]
def baseStart_960693 : Nat := 118140960795 + 960693 * 2 ^ 59
def prefixEnd_960693 : Nat := 4983230072969 + 3 ^ 40 * 960693 * 2
def baseEnd_960693 : Nat := 438486462586591127039431

theorem tailTrace_960693 : CollatzResearch.WordTrace tailWord_960693 prefixEnd_960693 438486462586591127039431 := by
  unfold tailWord_960693
  simp only [CollatzResearch.WordTrace]
  refine ⟨35039352308580809146966733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23359568205720539431311155 35039352308580809146966733)
  ·
    refine ⟨13139757115717803430112525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35039352308580809146966733 13139757115717803430112525)
    ·
      refine ⟨4927408918394176286292197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13139757115717803430112525 4927408918394176286292197)
      ·
        refine ⟨923889172198908053679787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4927408918394176286292197 923889172198908053679787)
        ·
          refine ⟨1385833758298362080519681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923889172198908053679787 1385833758298362080519681)
          ·
            refine ⟨1039375318723771560389761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1385833758298362080519681 1039375318723771560389761)
            ·
              refine ⟨779531489042828670292321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1039375318723771560389761 779531489042828670292321)
              ·
                refine ⟨584648616782121502719241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779531489042828670292321 584648616782121502719241)
                ·
                  refine ⟨438486462586591127039431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584648616782121502719241 438486462586591127039431)
                  ·
                    rfl

theorem cell20_960693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_960693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960693 prefixEnd_960693 := by exact prefixLift 960693
  have htrace : WordTrace (prefixWord ++ tailWord_960693) baseStart_960693 baseEnd_960693 := by
    simpa [prefixWord, tailWord_960693, baseEnd_960693] using wordTrace_append hprefix tailTrace_960693
  have hstable : (prefixWord ++ tailWord_960693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960693).length < 2 ^ (prefixWord ++ tailWord_960693).sum := by decide
  have hdescent : baseEnd_960693 < baseStart_960693 := by decide
  rcases family_descends (prefixWord ++ tailWord_960693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960715 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 3]
def baseStart_960715 : Nat := 118140960795 + 960715 * 2 ^ 59
def prefixEnd_960715 : Nat := 4983230072969 + 3 ^ 40 * 960715 * 2
def baseEnd_960715 : Nat := 438496503986056828306007

theorem tailTrace_960715 : CollatzResearch.WordTrace tailWord_960715 prefixEnd_960715 438496503986056828306007 := by
  unfold tailWord_960715
  simp only [CollatzResearch.WordTrace]
  refine ⟨35040154714501106904267599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23360103143000737936178399 35040154714501106904267599)
  ·
    refine ⟨52560232071751660356401399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35040154714501106904267599 52560232071751660356401399)
    ·
      refine ⟨78840348107627490534602099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52560232071751660356401399 78840348107627490534602099)
      ·
        refine ⟨118260522161441235801903149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78840348107627490534602099 118260522161441235801903149)
        ·
          refine ⟨44347695810540463425713681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118260522161441235801903149 44347695810540463425713681)
          ·
            refine ⟨33260771857905347569285261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44347695810540463425713681 33260771857905347569285261)
            ·
              refine ⟨12472789446714505338481973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33260771857905347569285261 12472789446714505338481973)
              ·
                refine ⟨1169324010629484875482685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12472789446714505338481973 1169324010629484875482685)
                ·
                  refine ⟨438496503986056828306007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169324010629484875482685 438496503986056828306007)
                  ·
                    rfl

theorem cell20_960715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 3].length) (baseStart_960715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960715 prefixEnd_960715 := by exact prefixLift 960715
  have htrace : WordTrace (prefixWord ++ tailWord_960715) baseStart_960715 baseEnd_960715 := by
    simpa [prefixWord, tailWord_960715, baseEnd_960715] using wordTrace_append hprefix tailTrace_960715
  have hstable : (prefixWord ++ tailWord_960715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960715).length < 2 ^ (prefixWord ++ tailWord_960715).sum := by decide
  have hdescent : baseEnd_960715 < baseStart_960715 := by decide
  rcases family_descends (prefixWord ++ tailWord_960715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960729 : List Nat := [1, 2, 1, 2, 3, 1, 2, 8]
def baseStart_960729 : Nat := 118140960795 + 960729 * 2 ^ 59
def prefixEnd_960729 : Nat := 4983230072969 + 3 ^ 40 * 960729 * 2
def baseEnd_960729 : Nat := 146167631322511667279761

theorem tailTrace_960729 : CollatzResearch.WordTrace tailWord_960729 prefixEnd_960729 146167631322511667279761 := by
  unfold tailWord_960729
  simp only [CollatzResearch.WordTrace]
  refine ⟨35040665336450387295277241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23360443557633591530184827 35040665336450387295277241)
  ·
    refine ⟨26280499002337790471457931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35040665336450387295277241 26280499002337790471457931)
    ·
      refine ⟨39420748503506685707186897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26280499002337790471457931 39420748503506685707186897)
      ·
        refine ⟨29565561377630014280390173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39420748503506685707186897 29565561377630014280390173)
        ·
          refine ⟨11087085516611255355146315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29565561377630014280390173 11087085516611255355146315)
          ·
            refine ⟨16630628274916883032719473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11087085516611255355146315 16630628274916883032719473)
            ·
              refine ⟨12472971206187662274539605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16630628274916883032719473 12472971206187662274539605)
              ·
                refine ⟨146167631322511667279761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12472971206187662274539605 146167631322511667279761)
                ·
                  rfl

theorem cell20_960729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_960729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960729 prefixEnd_960729 := by exact prefixLift 960729
  have htrace : WordTrace (prefixWord ++ tailWord_960729) baseStart_960729 baseEnd_960729 := by
    simpa [prefixWord, tailWord_960729, baseEnd_960729] using wordTrace_append hprefix tailTrace_960729
  have hstable : (prefixWord ++ tailWord_960729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960729).length < 2 ^ (prefixWord ++ tailWord_960729).sum := by decide
  have hdescent : baseEnd_960729 < baseStart_960729 := by decide
  rcases family_descends (prefixWord ++ tailWord_960729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960767 : List Nat := [1, 1, 2, 2, 1, 4, 2, 7]
def baseStart_960767 : Nat := 118140960795 + 960767 * 2 ^ 59
def prefixEnd_960767 : Nat := 4983230072969 + 3 ^ 40 * 960767 * 2
def baseEnd_960767 : Nat := 146173412734325252857487

theorem tailTrace_960767 : CollatzResearch.WordTrace tailWord_960767 prefixEnd_960767 146173412734325252857487 := by
  unfold tailWord_960767
  simp only [CollatzResearch.WordTrace]
  refine ⟨35042051310312719785160555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23361367540208479856773703 35042051310312719785160555)
  ·
    refine ⟨52563076965469079677740833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35042051310312719785160555 52563076965469079677740833)
    ·
      refine ⟨39422307724101809758305625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52563076965469079677740833 39422307724101809758305625)
      ·
        refine ⟨29566730793076357318729219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39422307724101809758305625 29566730793076357318729219)
        ·
          refine ⟨44350096189614535978093829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29566730793076357318729219 44350096189614535978093829)
          ·
            refine ⟨8315643035552725495892593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44350096189614535978093829 8315643035552725495892593)
            ·
              refine ⟨6236732276664544121919445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8315643035552725495892593 6236732276664544121919445)
              ·
                refine ⟨146173412734325252857487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6236732276664544121919445 146173412734325252857487)
                ·
                  rfl

theorem cell20_960767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_960767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960767 prefixEnd_960767 := by exact prefixLift 960767
  have htrace : WordTrace (prefixWord ++ tailWord_960767) baseStart_960767 baseEnd_960767 := by
    simpa [prefixWord, tailWord_960767, baseEnd_960767] using wordTrace_append hprefix tailTrace_960767
  have hstable : (prefixWord ++ tailWord_960767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960767).length < 2 ^ (prefixWord ++ tailWord_960767).sum := by decide
  have hdescent : baseEnd_960767 < baseStart_960767 := by decide
  rcases family_descends (prefixWord ++ tailWord_960767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960791 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_960791 : Nat := 118140960795 + 960791 * 2 ^ 59
def prefixEnd_960791 : Nat := 4983230072969 + 3 ^ 40 * 960791 * 2
def baseEnd_960791 : Nat := 438531192456938341772363

theorem tailTrace_960791 : CollatzResearch.WordTrace tailWord_960791 prefixEnd_960791 438531192456938341772363 := by
  unfold tailWord_960791
  simp only [CollatzResearch.WordTrace]
  refine ⟨35042926662225771884034227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23361951108150514589356151 35042926662225771884034227)
  ·
    refine ⟨52564389993338657826051341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35042926662225771884034227 52564389993338657826051341)
    ·
      refine ⟨19711646247501996684769253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52564389993338657826051341 19711646247501996684769253)
      ·
        refine ⟨3695933671406624378394235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19711646247501996684769253 3695933671406624378394235)
        ·
          refine ⟨5543900507109936567591353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695933671406624378394235 5543900507109936567591353)
          ·
            refine ⟨4157925380332452425693515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5543900507109936567591353 4157925380332452425693515)
            ·
              refine ⟨6236888070498678638540273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157925380332452425693515 6236888070498678638540273)
              ·
                refine ⟨4677666052874008978905205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6236888070498678638540273 4677666052874008978905205)
                ·
                  refine ⟨438531192456938341772363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4677666052874008978905205 438531192456938341772363)
                  ·
                    rfl

theorem cell20_960791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_960791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960791 prefixEnd_960791 := by exact prefixLift 960791
  have htrace : WordTrace (prefixWord ++ tailWord_960791) baseStart_960791 baseEnd_960791 := by
    simpa [prefixWord, tailWord_960791, baseEnd_960791] using wordTrace_append hprefix tailTrace_960791
  have hstable : (prefixWord ++ tailWord_960791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960791).length < 2 ^ (prefixWord ++ tailWord_960791).sum := by decide
  have hdescent : baseEnd_960791 < baseStart_960791 := by decide
  rcases family_descends (prefixWord ++ tailWord_960791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960807 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 4]
def baseStart_960807 : Nat := 118140960795 + 960807 * 2 ^ 59
def prefixEnd_960807 : Nat := 4983230072969 + 3 ^ 40 * 960807 * 2
def baseEnd_960807 : Nat := 438538495292913397238965

theorem tailTrace_960807 : CollatzResearch.WordTrace tailWord_960807 prefixEnd_960807 438538495292913397238965 := by
  unfold tailWord_960807
  simp only [CollatzResearch.WordTrace]
  refine ⟨35043510230167806616616675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23362340153445204411077783 35043510230167806616616675)
  ·
    refine ⟨52565265345251709924925013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35043510230167806616616675 52565265345251709924925013)
    ·
      refine ⟨615999203264668475682715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 52565265345251709924925013 615999203264668475682715)
      ·
        refine ⟨923998804897002713524073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615999203264668475682715 923998804897002713524073)
        ·
          refine ⟨692999103672752035143055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923998804897002713524073 692999103672752035143055)
          ·
            refine ⟨1039498655509128052714583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692999103672752035143055 1039498655509128052714583)
            ·
              refine ⟨1559247983263692079071875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039498655509128052714583 1559247983263692079071875)
              ·
                refine ⟨2338871974895538118607813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559247983263692079071875 2338871974895538118607813)
                ·
                  refine ⟨438538495292913397238965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338871974895538118607813 438538495292913397238965)
                  ·
                    rfl

theorem cell20_960807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 4].length) (baseStart_960807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960807 prefixEnd_960807 := by exact prefixLift 960807
  have htrace : WordTrace (prefixWord ++ tailWord_960807) baseStart_960807 baseEnd_960807 := by
    simpa [prefixWord, tailWord_960807, baseEnd_960807] using wordTrace_append hprefix tailTrace_960807
  have hstable : (prefixWord ++ tailWord_960807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960807).length < 2 ^ (prefixWord ++ tailWord_960807).sum := by decide
  have hdescent : baseEnd_960807 < baseStart_960807 := by decide
  rcases family_descends (prefixWord ++ tailWord_960807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960815 : List Nat := [1, 1, 2, 1, 2, 1, 4, 6, 2]
def baseStart_960815 : Nat := 118140960795 + 960815 * 2 ^ 59
def prefixEnd_960815 : Nat := 4983230072969 + 3 ^ 40 * 960815 * 2
def baseEnd_960815 : Nat := 438542146710900924972265

theorem tailTrace_960815 : CollatzResearch.WordTrace tailWord_960815 prefixEnd_960815 438542146710900924972265 := by
  unfold tailWord_960815
  simp only [CollatzResearch.WordTrace]
  refine ⟨35043802014138823982907899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23362534676092549321938599 35043802014138823982907899)
  ·
    refine ⟨52565703021208235974361849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35043802014138823982907899 52565703021208235974361849)
    ·
      refine ⟨39424277265906176980771387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52565703021208235974361849 39424277265906176980771387)
      ·
        refine ⟨59136415898859265471157081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39424277265906176980771387 59136415898859265471157081)
        ·
          refine ⟨44352311924144449103367811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59136415898859265471157081 44352311924144449103367811)
          ·
            refine ⟨66528467886216673655051717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44352311924144449103367811 66528467886216673655051717)
            ·
              refine ⟨12474087728665626310322197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66528467886216673655051717 12474087728665626310322197)
              ·
                refine ⟨584722862281201233296353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12474087728665626310322197 584722862281201233296353)
                ·
                  refine ⟨438542146710900924972265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584722862281201233296353 438542146710900924972265)
                  ·
                    rfl

theorem cell20_960815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 2].length) (baseStart_960815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960815 prefixEnd_960815 := by exact prefixLift 960815
  have htrace : WordTrace (prefixWord ++ tailWord_960815) baseStart_960815 baseEnd_960815 := by
    simpa [prefixWord, tailWord_960815, baseEnd_960815] using wordTrace_append hprefix tailTrace_960815
  have hstable : (prefixWord ++ tailWord_960815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960815).length < 2 ^ (prefixWord ++ tailWord_960815).sum := by decide
  have hdescent : baseEnd_960815 < baseStart_960815 := by decide
  rcases family_descends (prefixWord ++ tailWord_960815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960825 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 3]
def baseStart_960825 : Nat := 118140960795 + 960825 * 2 ^ 59
def prefixEnd_960825 : Nat := 4983230072969 + 3 ^ 40 * 960825 * 2
def baseEnd_960825 : Nat := 438546710983385334638891

theorem tailTrace_960825 : CollatzResearch.WordTrace tailWord_960825 prefixEnd_960825 438546710983385334638891 := by
  unfold tailWord_960825
  simp only [CollatzResearch.WordTrace]
  refine ⟨35044166744102595690771929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23362777829401730460514619 35044166744102595690771929)
  ·
    refine ⟨26283125058076946768078947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35044166744102595690771929 26283125058076946768078947)
    ·
      refine ⟨39424687587115420152118421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26283125058076946768078947 39424687587115420152118421)
      ·
        refine ⟨1848032230646035319630551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39424687587115420152118421 1848032230646035319630551)
        ·
          refine ⟨2772048345969052979445827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848032230646035319630551 2772048345969052979445827)
          ·
            refine ⟨4158072518953579469168741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772048345969052979445827 4158072518953579469168741)
            ·
              refine ⟨779638597303796150469139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4158072518953579469168741 779638597303796150469139)
              ·
                refine ⟨1169457895955694225703709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779638597303796150469139 1169457895955694225703709)
                ·
                  refine ⟨438546710983385334638891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169457895955694225703709 438546710983385334638891)
                  ·
                    rfl

theorem cell20_960825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_960825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960825 prefixEnd_960825 := by exact prefixLift 960825
  have htrace : WordTrace (prefixWord ++ tailWord_960825) baseStart_960825 baseEnd_960825 := by
    simpa [prefixWord, tailWord_960825, baseEnd_960825] using wordTrace_append hprefix tailTrace_960825
  have hstable : (prefixWord ++ tailWord_960825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960825).length < 2 ^ (prefixWord ++ tailWord_960825).sum := by decide
  have hdescent : baseEnd_960825 < baseStart_960825 := by decide
  rcases family_descends (prefixWord ++ tailWord_960825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960860 : List Nat := [2, 2, 4, 3, 9]
def baseStart_960860 : Nat := 118140960795 + 960860 * 2 ^ 59
def prefixEnd_960860 : Nat := 4983230072969 + 3 ^ 40 * 960860 * 2
def baseEnd_960860 : Nat := 5414354147371367512001

theorem tailTrace_960860 : CollatzResearch.WordTrace tailWord_960860 prefixEnd_960860 5414354147371367512001 := by
  unfold tailWord_960860
  simp only [CollatzResearch.WordTrace]
  refine ⟨17522721649487898334148017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23363628865983864445530689 17522721649487898334148017)
  ·
    refine ⟨13142041237115923750611013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17522721649487898334148017 13142041237115923750611013)
    ·
      refine ⟨2464132731959235703239565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13142041237115923750611013 2464132731959235703239565)
      ·
        refine ⟨924049774484713388714837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2464132731959235703239565 924049774484713388714837)
        ·
          refine ⟨5414354147371367512001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 924049774484713388714837 5414354147371367512001)
          ·
            rfl

theorem cell20_960860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 9].length) (baseStart_960860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960860 prefixEnd_960860 := by exact prefixLift 960860
  have htrace : WordTrace (prefixWord ++ tailWord_960860) baseStart_960860 baseEnd_960860 := by
    simpa [prefixWord, tailWord_960860, baseEnd_960860] using wordTrace_append hprefix tailTrace_960860
  have hstable : (prefixWord ++ tailWord_960860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960860).length < 2 ^ (prefixWord ++ tailWord_960860).sum := by decide
  have hdescent : baseEnd_960860 < baseStart_960860 := by decide
  rcases family_descends (prefixWord ++ tailWord_960860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960862 : List Nat := [4, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_960862 : Nat := 118140960795 + 960862 * 2 ^ 59
def prefixEnd_960862 : Nat := 4983230072969 + 3 ^ 40 * 960862 * 2
def baseEnd_960862 : Nat := 438563598791577650405407

theorem tailTrace_960862 : CollatzResearch.WordTrace tailWord_960862 prefixEnd_960862 438563598791577650405407 := by
  unfold tailWord_960862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380689530621068876233605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23363677496645700673245893 4380689530621068876233605)
  ·
    refine ⟨821379286991450414293801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4380689530621068876233605 821379286991450414293801)
    ·
      refine ⟨616034465243587810720351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 821379286991450414293801 616034465243587810720351)
      ·
        refine ⟨924051697865381716080527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616034465243587810720351 924051697865381716080527)
        ·
          refine ⟨1386077546798072574120791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924051697865381716080527 1386077546798072574120791)
          ·
            refine ⟨2079116320197108861181187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386077546798072574120791 2079116320197108861181187)
            ·
              refine ⟨3118674480295663291771781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079116320197108861181187 3118674480295663291771781)
              ·
                refine ⟨584751465055436867207209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3118674480295663291771781 584751465055436867207209)
                ·
                  refine ⟨438563598791577650405407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584751465055436867207209 438563598791577650405407)
                  ·
                    rfl

theorem cell20_960862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_960862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960862 prefixEnd_960862 := by exact prefixLift 960862
  have htrace : WordTrace (prefixWord ++ tailWord_960862) baseStart_960862 baseEnd_960862 := by
    simpa [prefixWord, tailWord_960862, baseEnd_960862] using wordTrace_append hprefix tailTrace_960862
  have hstable : (prefixWord ++ tailWord_960862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960862).length < 2 ^ (prefixWord ++ tailWord_960862).sum := by decide
  have hdescent : baseEnd_960862 < baseStart_960862 := by decide
  rcases family_descends (prefixWord ++ tailWord_960862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960866 : List Nat := [3, 3, 2, 1, 1, 4, 2, 2, 2]
def baseStart_960866 : Nat := 118140960795 + 960866 * 2 ^ 59
def prefixEnd_960866 : Nat := 4983230072969 + 3 ^ 40 * 960866 * 2
def baseEnd_960866 : Nat := 438565424500571414272057

theorem tailTrace_960866 : CollatzResearch.WordTrace tailWord_960866 prefixEnd_960866 438565424500571414272057 := by
  unfold tailWord_960866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8761415534238514923253613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23363774757969373128676301 8761415534238514923253613)
  ·
    refine ⟨3285530825339443096220105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8761415534238514923253613 3285530825339443096220105)
    ·
      refine ⟨2464148119004582322165079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3285530825339443096220105 2464148119004582322165079)
      ·
        refine ⟨3696222178506873483247619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2464148119004582322165079 3696222178506873483247619)
        ·
          refine ⟨5544333267760310224871429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696222178506873483247619 5544333267760310224871429)
          ·
            refine ⟨1039562487705058167163393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5544333267760310224871429 1039562487705058167163393)
            ·
              refine ⟨779671865778793625372545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1039562487705058167163393 779671865778793625372545)
              ·
                refine ⟨584753899334095219029409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779671865778793625372545 584753899334095219029409)
                ·
                  refine ⟨438565424500571414272057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584753899334095219029409 438565424500571414272057)
                  ·
                    rfl

theorem cell20_960866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_960866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960866 prefixEnd_960866 := by exact prefixLift 960866
  have htrace : WordTrace (prefixWord ++ tailWord_960866) baseStart_960866 baseEnd_960866 := by
    simpa [prefixWord, tailWord_960866, baseEnd_960866] using wordTrace_append hprefix tailTrace_960866
  have hstable : (prefixWord ++ tailWord_960866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960866).length < 2 ^ (prefixWord ++ tailWord_960866).sum := by decide
  have hdescent : baseEnd_960866 < baseStart_960866 := by decide
  rcases family_descends (prefixWord ++ tailWord_960866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960908 : List Nat := [2, 2, 1, 2, 1, 5, 2, 3, 2]
def baseStart_960908 : Nat := 118140960795 + 960908 * 2 ^ 59
def prefixEnd_960908 : Nat := 4983230072969 + 3 ^ 40 * 960908 * 2
def baseEnd_960908 : Nat := 438584594445005934871885

theorem tailTrace_960908 : CollatzResearch.WordTrace tailWord_960908 prefixEnd_960908 438584594445005934871885 := by
  unfold tailWord_960908
  simp only [CollatzResearch.WordTrace]
  refine ⟨17523597001400950433021689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23364796001867933910695585 17523597001400950433021689)
  ·
    refine ⟨13142697751050712824766267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17523597001400950433021689 13142697751050712824766267)
    ·
      refine ⟨19714046626576069237149401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13142697751050712824766267 19714046626576069237149401)
      ·
        refine ⟨14785534969932051927862051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19714046626576069237149401 14785534969932051927862051)
        ·
          refine ⟨22178302454898077891793077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14785534969932051927862051 22178302454898077891793077)
          ·
            refine ⟨2079215855146694802355601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22178302454898077891793077 2079215855146694802355601)
            ·
              refine ⟨1559411891360021101766701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079215855146694802355601 1559411891360021101766701)
              ·
                refine ⟨584779459260007913162513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1559411891360021101766701 584779459260007913162513)
                ·
                  refine ⟨438584594445005934871885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584779459260007913162513 438584594445005934871885)
                  ·
                    rfl

theorem cell20_960908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_960908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960908 prefixEnd_960908 := by exact prefixLift 960908
  have htrace : WordTrace (prefixWord ++ tailWord_960908) baseStart_960908 baseEnd_960908 := by
    simpa [prefixWord, tailWord_960908, baseEnd_960908] using wordTrace_append hprefix tailTrace_960908
  have hstable : (prefixWord ++ tailWord_960908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960908).length < 2 ^ (prefixWord ++ tailWord_960908).sum := by decide
  have hdescent : baseEnd_960908 < baseStart_960908 := by decide
  rcases family_descends (prefixWord ++ tailWord_960908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960922 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_960922 : Nat := 118140960795 + 960922 * 2 ^ 59
def prefixEnd_960922 : Nat := 4983230072969 + 3 ^ 40 * 960922 * 2
def baseEnd_960922 : Nat := 438590984426484108405161

theorem tailTrace_960922 : CollatzResearch.WordTrace tailWord_960922 prefixEnd_960922 438590984426484108405161 := by
  unfold tailWord_960922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8761926156187795314263255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23365136416500787504702013 8761926156187795314263255)
  ·
    refine ⟨13142889234281692971394883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8761926156187795314263255 13142889234281692971394883)
    ·
      refine ⟨19714333851422539457092325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13142889234281692971394883 19714333851422539457092325)
      ·
        refine ⟨3696437597141726148204811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19714333851422539457092325 3696437597141726148204811)
        ·
          refine ⟨5544656395712589222307217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696437597141726148204811 5544656395712589222307217)
          ·
            refine ⟨4158492296784441916730413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5544656395712589222307217 4158492296784441916730413)
            ·
              refine ⟨1559434611294165718773905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4158492296784441916730413 1559434611294165718773905)
              ·
                refine ⟨1169575958470624289080429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559434611294165718773905 1169575958470624289080429)
                ·
                  refine ⟨438590984426484108405161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169575958470624289080429 438590984426484108405161)
                  ·
                    rfl

theorem cell20_960922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_960922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960922 prefixEnd_960922 := by exact prefixLift 960922
  have htrace : WordTrace (prefixWord ++ tailWord_960922) baseStart_960922 baseEnd_960922 := by
    simpa [prefixWord, tailWord_960922, baseEnd_960922] using wordTrace_append hprefix tailTrace_960922
  have hstable : (prefixWord ++ tailWord_960922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960922).length < 2 ^ (prefixWord ++ tailWord_960922).sum := by decide
  have hdescent : baseEnd_960922 < baseStart_960922 := by decide
  rcases family_descends (prefixWord ++ tailWord_960922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960953 : List Nat := [1, 2, 1, 4, 3, 3, 2, 4]
def baseStart_960953 : Nat := 118140960795 + 960953 * 2 ^ 59
def prefixEnd_960953 : Nat := 4983230072969 + 3 ^ 40 * 960953 * 2
def baseEnd_960953 : Nat := 146201711223728592790567

theorem tailTrace_960953 : CollatzResearch.WordTrace tailWord_960953 prefixEnd_960953 146201711223728592790567 := by
  unfold tailWord_960953
  simp only [CollatzResearch.WordTrace]
  refine ⟨35048835287638873551431513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23365890191759249034287675 35048835287638873551431513)
  ·
    refine ⟨26286626465729155163573635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35048835287638873551431513 26286626465729155163573635)
    ·
      refine ⟨39429939698593732745360453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26286626465729155163573635 39429939698593732745360453)
      ·
        refine ⟨7393113693486324889755085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39429939698593732745360453 7393113693486324889755085)
        ·
          refine ⟨2772417635057371833658157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7393113693486324889755085 2772417635057371833658157)
          ·
            refine ⟨1039656613146514437621809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2772417635057371833658157 1039656613146514437621809)
            ·
              refine ⟨779742459859885828216357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1039656613146514437621809 779742459859885828216357)
              ·
                refine ⟨146201711223728592790567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 779742459859885828216357 146201711223728592790567)
                ·
                  rfl

theorem cell20_960953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 4].length) (baseStart_960953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960953 prefixEnd_960953 := by exact prefixLift 960953
  have htrace : WordTrace (prefixWord ++ tailWord_960953) baseStart_960953 baseEnd_960953 := by
    simpa [prefixWord, tailWord_960953, baseEnd_960953] using wordTrace_append hprefix tailTrace_960953
  have hstable : (prefixWord ++ tailWord_960953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960953).length < 2 ^ (prefixWord ++ tailWord_960953).sum := by decide
  have hdescent : baseEnd_960953 < baseStart_960953 := by decide
  rcases family_descends (prefixWord ++ tailWord_960953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960981 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_960981 : Nat := 118140960795 + 960981 * 2 ^ 59
def prefixEnd_960981 : Nat := 4983230072969 + 3 ^ 40 * 960981 * 2
def baseEnd_960981 : Nat := 438617913634142125438253

theorem tailTrace_960981 : CollatzResearch.WordTrace tailWord_960981 prefixEnd_960981 438617913634142125438253 := by
  unfold tailWord_960981
  simp only [CollatzResearch.WordTrace]
  refine ⟨35049856531537434333450797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23366571021024956222300531 35049856531537434333450797)
  ·
    refine ⟨13143696199326537875044049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35049856531537434333450797 13143696199326537875044049)
    ·
      refine ⟨9857772149494903406283037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13143696199326537875044049 9857772149494903406283037)
      ·
        refine ⟨3696664556060588777356139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9857772149494903406283037 3696664556060588777356139)
        ·
          refine ⟨5544996834090883166034209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696664556060588777356139 5544996834090883166034209)
          ·
            refine ⟨4158747625568162374525657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5544996834090883166034209 4158747625568162374525657)
            ·
              refine ⟨3119060719176121780894243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4158747625568162374525657 3119060719176121780894243)
              ·
                refine ⟨4678591078764182671341365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119060719176121780894243 4678591078764182671341365)
                ·
                  refine ⟨438617913634142125438253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4678591078764182671341365 438617913634142125438253)
                  ·
                    rfl

theorem cell20_960981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_960981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960981 prefixEnd_960981 := by exact prefixLift 960981
  have htrace : WordTrace (prefixWord ++ tailWord_960981) baseStart_960981 baseEnd_960981 := by
    simpa [prefixWord, tailWord_960981, baseEnd_960981] using wordTrace_append hprefix tailTrace_960981
  have hstable : (prefixWord ++ tailWord_960981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960981).length < 2 ^ (prefixWord ++ tailWord_960981).sum := by decide
  have hdescent : baseEnd_960981 < baseStart_960981 := by decide
  rcases family_descends (prefixWord ++ tailWord_960981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960994 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_960994 : Nat := 118140960795 + 960994 * 2 ^ 59
def prefixEnd_960994 : Nat := 4983230072969 + 3 ^ 40 * 960994 * 2
def baseEnd_960994 : Nat := 438623847188371858004867

theorem tailTrace_960994 : CollatzResearch.WordTrace tailWord_960994 prefixEnd_960994 438623847188371858004867 := by
  unfold tailWord_960994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8762582670122584388418509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23366887120326891702449357 8762582670122584388418509)
  ·
    refine ⟨3285968501295969145656941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8762582670122584388418509 3285968501295969145656941)
    ·
      refine ⟨1232238187985988429621353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3285968501295969145656941 1232238187985988429621353)
      ·
        refine ⟨924178640989491322216015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1232238187985988429621353 924178640989491322216015)
        ·
          refine ⟨1386267961484236983324023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924178640989491322216015 1386267961484236983324023)
          ·
            refine ⟨2079401942226355474986035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386267961484236983324023 2079401942226355474986035)
            ·
              refine ⟨3119102913339533212479053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079401942226355474986035 3119102913339533212479053)
              ·
                refine ⟨1169663592502324954679645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3119102913339533212479053 1169663592502324954679645)
                ·
                  refine ⟨438623847188371858004867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169663592502324954679645 438623847188371858004867)
                  ·
                    rfl

theorem cell20_960994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_960994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_960994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_960994 prefixEnd_960994 := by exact prefixLift 960994
  have htrace : WordTrace (prefixWord ++ tailWord_960994) baseStart_960994 baseEnd_960994 := by
    simpa [prefixWord, tailWord_960994, baseEnd_960994] using wordTrace_append hprefix tailTrace_960994
  have hstable : (prefixWord ++ tailWord_960994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960994).length < 2 ^ (prefixWord ++ tailWord_960994).sum := by decide
  have hdescent : baseEnd_960994 < baseStart_960994 := by decide
  rcases family_descends (prefixWord ++ tailWord_960994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961036 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 3]
def baseStart_961036 : Nat := 118140960795 + 961036 * 2 ^ 59
def prefixEnd_961036 : Nat := 4983230072969 + 3 ^ 40 * 961036 * 2
def baseEnd_961036 : Nat := 438643017132806378604695

theorem tailTrace_961036 : CollatzResearch.WordTrace tailWord_961036 prefixEnd_961036 438643017132806378604695 := by
  unfold tailWord_961036
  simp only [CollatzResearch.WordTrace]
  refine ⟨17525931273169089363351481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23367908364225452484468641 17525931273169089363351481)
  ·
    refine ⟨13144448454876817022513611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17525931273169089363351481 13144448454876817022513611)
    ·
      refine ⟨19716672682315225533770417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13144448454876817022513611 19716672682315225533770417)
      ·
        refine ⟨14787504511736419150327813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19716672682315225533770417 14787504511736419150327813)
        ·
          refine ⟨2772657095950578590686465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14787504511736419150327813 2772657095950578590686465)
          ·
            refine ⟨2079492821962933943014849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772657095950578590686465 2079492821962933943014849)
            ·
              refine ⟨1559619616472200457261137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079492821962933943014849 1559619616472200457261137)
              ·
                refine ⟨1169714712354150342945853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559619616472200457261137 1169714712354150342945853)
                ·
                  refine ⟨438643017132806378604695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169714712354150342945853 438643017132806378604695)
                  ·
                    rfl

theorem cell20_961036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_961036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961036 prefixEnd_961036 := by exact prefixLift 961036
  have htrace : WordTrace (prefixWord ++ tailWord_961036) baseStart_961036 baseEnd_961036 := by
    simpa [prefixWord, tailWord_961036, baseEnd_961036] using wordTrace_append hprefix tailTrace_961036
  have hstable : (prefixWord ++ tailWord_961036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961036).length < 2 ^ (prefixWord ++ tailWord_961036).sum := by decide
  have hdescent : baseEnd_961036 < baseStart_961036 := by decide
  rcases family_descends (prefixWord ++ tailWord_961036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961043 : List Nat := [1, 1, 1, 2, 1, 5, 3, 4, 2]
def baseStart_961043 : Nat := 118140960795 + 961043 * 2 ^ 59
def prefixEnd_961043 : Nat := 4983230072969 + 3 ^ 40 * 961043 * 2
def baseEnd_961043 : Nat := 438646212123545465371333

theorem tailTrace_961043 : CollatzResearch.WordTrace tailWord_961043 prefixEnd_961043 438646212123545465371333 := by
  unfold tailWord_961043
  simp only [CollatzResearch.WordTrace]
  refine ⟨35052117857312818922207783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23368078571541879281471855 35052117857312818922207783)
  ·
    refine ⟨52578176785969228383311675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35052117857312818922207783 52578176785969228383311675)
    ·
      refine ⟨78867265178953842574967513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52578176785969228383311675 78867265178953842574967513)
      ·
        refine ⟨59150448884215381931225635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78867265178953842574967513 59150448884215381931225635)
        ·
          refine ⟨88725673326323072896838453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59150448884215381931225635 88725673326323072896838453)
          ·
            refine ⟨8318031874342788084078605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88725673326323072896838453 8318031874342788084078605)
            ·
              refine ⟨3119261952878545531529477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8318031874342788084078605 3119261952878545531529477)
              ·
                refine ⟨584861616164727287161777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3119261952878545531529477 584861616164727287161777)
                ·
                  refine ⟨438646212123545465371333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584861616164727287161777 438646212123545465371333)
                  ·
                    rfl

theorem cell20_961043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 2].length) (baseStart_961043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961043 prefixEnd_961043 := by exact prefixLift 961043
  have htrace : WordTrace (prefixWord ++ tailWord_961043) baseStart_961043 baseEnd_961043 := by
    simpa [prefixWord, tailWord_961043, baseEnd_961043] using wordTrace_append hprefix tailTrace_961043
  have hstable : (prefixWord ++ tailWord_961043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961043).length < 2 ^ (prefixWord ++ tailWord_961043).sum := by decide
  have hdescent : baseEnd_961043 < baseStart_961043 := by decide
  rcases family_descends (prefixWord ++ tailWord_961043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961057 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 3]
def baseStart_961057 : Nat := 118140960795 + 961057 * 2 ^ 59
def prefixEnd_961057 : Nat := 4983230072969 + 3 ^ 40 * 961057 * 2
def baseEnd_961057 : Nat := 438652602105023638904609

theorem tailTrace_961057 : CollatzResearch.WordTrace tailWord_961057 prefixEnd_961057 438652602105023638904609 := by
  unfold tailWord_961057
  simp only [CollatzResearch.WordTrace]
  refine ⟨35052628479262099313217425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23368418986174732875478283 35052628479262099313217425)
  ·
    refine ⟨26289471359446574484913069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35052628479262099313217425 26289471359446574484913069)
    ·
      refine ⟨9858551759792465431842401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26289471359446574484913069 9858551759792465431842401)
      ·
        refine ⟨7393913819844349073881801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9858551759792465431842401 7393913819844349073881801)
        ·
          refine ⟨5545435364883261805411351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7393913819844349073881801 5545435364883261805411351)
          ·
            refine ⟨8318153047324892708117027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545435364883261805411351 8318153047324892708117027)
            ·
              refine ⟨12477229570987339062175541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318153047324892708117027 12477229570987339062175541)
              ·
                refine ⟨1169740272280063037078957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12477229570987339062175541 1169740272280063037078957)
                ·
                  refine ⟨438652602105023638904609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169740272280063037078957 438652602105023638904609)
                  ·
                    rfl

theorem cell20_961057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_961057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961057 prefixEnd_961057 := by exact prefixLift 961057
  have htrace : WordTrace (prefixWord ++ tailWord_961057) baseStart_961057 baseEnd_961057 := by
    simpa [prefixWord, tailWord_961057, baseEnd_961057] using wordTrace_append hprefix tailTrace_961057
  have hstable : (prefixWord ++ tailWord_961057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961057).length < 2 ^ (prefixWord ++ tailWord_961057).sum := by decide
  have hdescent : baseEnd_961057 < baseStart_961057 := by decide
  rcases family_descends (prefixWord ++ tailWord_961057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961060 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 4]
def baseStart_961060 : Nat := 118140960795 + 961060 * 2 ^ 59
def prefixEnd_961060 : Nat := 4983230072969 + 3 ^ 40 * 961060 * 2
def baseEnd_961060 : Nat := 438653971386768961804597

theorem tailTrace_961060 : CollatzResearch.WordTrace tailWord_961060 prefixEnd_961060 438653971386768961804597 := by
  unfold tailWord_961060
  simp only [CollatzResearch.WordTrace]
  refine ⟨17526368949125615412788317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23368491932167487217051089 17526368949125615412788317)
  ·
    refine ⟨6572388355922105779795619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17526368949125615412788317 6572388355922105779795619)
    ·
      refine ⟨9858582533883158669693429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6572388355922105779795619 9858582533883158669693429)
      ·
        refine ⟨924242112551546125283759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9858582533883158669693429 924242112551546125283759)
        ·
          refine ⟨1386363168827319187925639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924242112551546125283759 1386363168827319187925639)
          ·
            refine ⟨2079544753240978781888459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386363168827319187925639 2079544753240978781888459)
            ·
              refine ⟨3119317129861468172832689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079544753240978781888459 3119317129861468172832689)
              ·
                refine ⟨2339487847396101129624517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119317129861468172832689 2339487847396101129624517)
                ·
                  refine ⟨438653971386768961804597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2339487847396101129624517 438653971386768961804597)
                  ·
                    rfl

theorem cell20_961060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_961060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961060 prefixEnd_961060 := by exact prefixLift 961060
  have htrace : WordTrace (prefixWord ++ tailWord_961060) baseStart_961060 baseEnd_961060 := by
    simpa [prefixWord, tailWord_961060, baseEnd_961060] using wordTrace_append hprefix tailTrace_961060
  have hstable : (prefixWord ++ tailWord_961060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961060).length < 2 ^ (prefixWord ++ tailWord_961060).sum := by decide
  have hdescent : baseEnd_961060 < baseStart_961060 := by decide
  rcases family_descends (prefixWord ++ tailWord_961060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961095 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 5]
def baseStart_961095 : Nat := 118140960795 + 961095 * 2 ^ 59
def prefixEnd_961095 : Nat := 4983230072969 + 3 ^ 40 * 961095 * 2
def baseEnd_961095 : Nat := 438669946340464395637787

theorem tailTrace_961095 : CollatzResearch.WordTrace tailWord_961095 prefixEnd_961095 438669946340464395637787 := by
  unfold tailWord_961095
  simp only [CollatzResearch.WordTrace]
  refine ⟨35054014453124431803100739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23369342968749621202067159 35054014453124431803100739)
  ·
    refine ⟨52581021679686647704651109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35054014453124431803100739 52581021679686647704651109)
    ·
      refine ⟨9858941564941246444622083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52581021679686647704651109 9858941564941246444622083)
      ·
        refine ⟨14788412347411869666933125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9858941564941246444622083 14788412347411869666933125)
        ·
          refine ⟨2772827315139725562549961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14788412347411869666933125 2772827315139725562549961)
          ·
            refine ⟨2079620486354794171912471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772827315139725562549961 2079620486354794171912471)
            ·
              refine ⟨3119430729532191257868707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079620486354794171912471 3119430729532191257868707)
              ·
                refine ⟨4679146094298286886803061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119430729532191257868707 4679146094298286886803061)
                ·
                  refine ⟨438669946340464395637787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4679146094298286886803061 438669946340464395637787)
                  ·
                    rfl

theorem cell20_961095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_961095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961095 prefixEnd_961095 := by exact prefixLift 961095
  have htrace : WordTrace (prefixWord ++ tailWord_961095) baseStart_961095 baseEnd_961095 := by
    simpa [prefixWord, tailWord_961095, baseEnd_961095] using wordTrace_append hprefix tailTrace_961095
  have hstable : (prefixWord ++ tailWord_961095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961095).length < 2 ^ (prefixWord ++ tailWord_961095).sum := by decide
  have hdescent : baseEnd_961095 < baseStart_961095 := by decide
  rcases family_descends (prefixWord ++ tailWord_961095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961102 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_961102 : Nat := 118140960795 + 961102 * 2 ^ 59
def prefixEnd_961102 : Nat := 4983230072969 + 3 ^ 40 * 961102 * 2
def baseEnd_961102 : Nat := 438673141331203482404425

theorem tailTrace_961102 : CollatzResearch.WordTrace tailWord_961102 prefixEnd_961102 438673141331203482404425 := by
  unfold tailWord_961102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4381783720512383999825695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23369513176066047999070373 4381783720512383999825695)
  ·
    refine ⟨6572675580768575999738543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4381783720512383999825695 6572675580768575999738543)
    ·
      refine ⟨9859013371152863999607815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6572675580768575999738543 9859013371152863999607815)
      ·
        refine ⟨14788520056729295999411723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859013371152863999607815 14788520056729295999411723)
        ·
          refine ⟨22182780085093943999117585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14788520056729295999411723 22182780085093943999117585)
          ·
            refine ⟨16637085063820457999338189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22182780085093943999117585 16637085063820457999338189)
            ·
              refine ⟨6238906898932671749751821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16637085063820457999338189 6238906898932671749751821)
              ·
                refine ⟨2339590087099751906156933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6238906898932671749751821 2339590087099751906156933)
                ·
                  refine ⟨438673141331203482404425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2339590087099751906156933 438673141331203482404425)
                  ·
                    rfl

theorem cell20_961102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_961102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961102 prefixEnd_961102 := by exact prefixLift 961102
  have htrace : WordTrace (prefixWord ++ tailWord_961102) baseStart_961102 baseEnd_961102 := by
    simpa [prefixWord, tailWord_961102, baseEnd_961102] using wordTrace_append hprefix tailTrace_961102
  have hstable : (prefixWord ++ tailWord_961102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961102).length < 2 ^ (prefixWord ++ tailWord_961102).sum := by decide
  have hdescent : baseEnd_961102 < baseStart_961102 := by decide
  rcases family_descends (prefixWord ++ tailWord_961102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961118 : List Nat := [4, 4, 1, 2, 1, 2, 2, 4]
def baseStart_961118 : Nat := 118140960795 + 961118 * 2 ^ 59
def prefixEnd_961118 : Nat := 4983230072969 + 3 ^ 40 * 961118 * 2
def baseEnd_961118 : Nat := 146226814722392845957009

theorem tailTrace_961118 : CollatzResearch.WordTrace tailWord_961118 prefixEnd_961118 146226814722392845957009 := by
  unfold tailWord_961118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4381856666505138341398501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23369902221360737820792005 4381856666505138341398501)
  ·
    refine ⟨821598124969713439012219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4381856666505138341398501 821598124969713439012219)
    ·
      refine ⟨1232397187454570158518329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821598124969713439012219 1232397187454570158518329)
      ·
        refine ⟨924297890590927618888747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1232397187454570158518329 924297890590927618888747)
        ·
          refine ⟨1386446835886391428333121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924297890590927618888747 1386446835886391428333121)
          ·
            refine ⟨1039835126914793571249841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386446835886391428333121 1039835126914793571249841)
            ·
              refine ⟨779876345186095178437381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1039835126914793571249841 779876345186095178437381)
              ·
                refine ⟨146226814722392845957009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 779876345186095178437381 146226814722392845957009)
                ·
                  rfl

theorem cell20_961118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_961118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961118 prefixEnd_961118 := by exact prefixLift 961118
  have htrace : WordTrace (prefixWord ++ tailWord_961118) baseStart_961118 baseEnd_961118 := by
    simpa [prefixWord, tailWord_961118, baseEnd_961118] using wordTrace_append hprefix tailTrace_961118
  have hstable : (prefixWord ++ tailWord_961118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961118).length < 2 ^ (prefixWord ++ tailWord_961118).sum := by decide
  have hdescent : baseEnd_961118 < baseStart_961118 := by decide
  rcases family_descends (prefixWord ++ tailWord_961118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961133 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_961133 : Nat := 118140960795 + 961133 * 2 ^ 59
def prefixEnd_961133 : Nat := 4983230072969 + 3 ^ 40 * 961133 * 2
def baseEnd_961133 : Nat := 438687290575905152370965

theorem tailTrace_961133 : CollatzResearch.WordTrace tailWord_961133 prefixEnd_961133 438687290575905152370965 := by
  unfold tailWord_961133
  simp only [CollatzResearch.WordTrace]
  refine ⟨35055400426986764292984053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23370266951324509528656035 35055400426986764292984053)
  ·
    refine ⟨3286443790030009152467255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35055400426986764292984053 3286443790030009152467255)
    ·
      refine ⟨4929665685045013728700883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286443790030009152467255 4929665685045013728700883)
      ·
        refine ⟨7394498527567520593051325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4929665685045013728700883 7394498527567520593051325)
        ·
          refine ⟨2772936947837820222394247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7394498527567520593051325 2772936947837820222394247)
          ·
            refine ⟨4159405421756730333591371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772936947837820222394247 4159405421756730333591371)
            ·
              refine ⟨6239108132635095500387057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159405421756730333591371 6239108132635095500387057)
              ·
                refine ⟨4679331099476321625290293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239108132635095500387057 4679331099476321625290293)
                ·
                  refine ⟨438687290575905152370965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4679331099476321625290293 438687290575905152370965)
                  ·
                    rfl

theorem cell20_961133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_961133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961133 prefixEnd_961133 := by exact prefixLift 961133
  have htrace : WordTrace (prefixWord ++ tailWord_961133) baseStart_961133 baseEnd_961133 := by
    simpa [prefixWord, tailWord_961133, baseEnd_961133] using wordTrace_append hprefix tailTrace_961133
  have hstable : (prefixWord ++ tailWord_961133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961133).length < 2 ^ (prefixWord ++ tailWord_961133).sum := by decide
  have hdescent : baseEnd_961133 < baseStart_961133 := by decide
  rcases family_descends (prefixWord ++ tailWord_961133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961157 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 4]
def baseStart_961157 : Nat := 118140960795 + 961157 * 2 ^ 59
def prefixEnd_961157 : Nat := 4983230072969 + 3 ^ 40 * 961157 * 2
def baseEnd_961157 : Nat := 438698244829867735570867

theorem tailTrace_961157 : CollatzResearch.WordTrace tailWord_961157 prefixEnd_961157 438698244829867735570867 := by
  unfold tailWord_961157
  simp only [CollatzResearch.WordTrace]
  refine ⟨35056275778899816391857725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23370850519266544261238483 35056275778899816391857725)
  ·
    refine ⟨13146103417087431146946647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35056275778899816391857725 13146103417087431146946647)
    ·
      refine ⟨19719155125631146720419971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13146103417087431146946647 19719155125631146720419971)
      ·
        refine ⟨29578732688446720080629957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19719155125631146720419971 29578732688446720080629957)
        ·
          refine ⟨5546012379083760015118117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29578732688446720080629957 5546012379083760015118117)
          ·
            refine ⟨1039877321078205002834647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5546012379083760015118117 1039877321078205002834647)
            ·
              refine ⟨1559815981617307504251971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039877321078205002834647 1559815981617307504251971)
              ·
                refine ⟨2339723972425961256377957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559815981617307504251971 2339723972425961256377957)
                ·
                  refine ⟨438698244829867735570867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2339723972425961256377957 438698244829867735570867)
                  ·
                    rfl

theorem cell20_961157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_961157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961157 prefixEnd_961157 := by exact prefixLift 961157
  have htrace : WordTrace (prefixWord ++ tailWord_961157) baseStart_961157 baseEnd_961157 := by
    simpa [prefixWord, tailWord_961157, baseEnd_961157] using wordTrace_append hprefix tailTrace_961157
  have hstable : (prefixWord ++ tailWord_961157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961157).length < 2 ^ (prefixWord ++ tailWord_961157).sum := by decide
  have hdescent : baseEnd_961157 < baseStart_961157 := by decide
  rcases family_descends (prefixWord ++ tailWord_961157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961240 : List Nat := [2, 1, 2, 2, 3, 3, 3, 4]
def baseStart_961240 : Nat := 118140960795 + 961240 * 2 ^ 59
def prefixEnd_961240 : Nat := 4983230072969 + 3 ^ 40 * 961240 * 2
def baseEnd_961240 : Nat := 146245376097162778601287

theorem tailTrace_961240 : CollatzResearch.WordTrace tailWord_961240 prefixEnd_961240 146245376097162778601287 := by
  unfold tailWord_961240
  simp only [CollatzResearch.WordTrace]
  refine ⟨17529651518799560783564587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23372868691732747711419449 17529651518799560783564587)
  ·
    refine ⟨26294477278199341175346881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17529651518799560783564587 26294477278199341175346881)
    ·
      refine ⟨19720857958649505881510161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26294477278199341175346881 19720857958649505881510161)
      ·
        refine ⟨14790643468987129411132621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19720857958649505881510161 14790643468987129411132621)
        ·
          refine ⟨5546491300870173529174733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14790643468987129411132621 5546491300870173529174733)
          ·
            refine ⟨2079934237826315073440525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5546491300870173529174733 2079934237826315073440525)
            ·
              refine ⟨779975339184868152540197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2079934237826315073440525 779975339184868152540197)
              ·
                refine ⟨146245376097162778601287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 779975339184868152540197 146245376097162778601287)
                ·
                  rfl

theorem cell20_961240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_961240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961240 prefixEnd_961240 := by exact prefixLift 961240
  have htrace : WordTrace (prefixWord ++ tailWord_961240) baseStart_961240 baseEnd_961240 := by
    simpa [prefixWord, tailWord_961240, baseEnd_961240] using wordTrace_append hprefix tailTrace_961240
  have hstable : (prefixWord ++ tailWord_961240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961240).length < 2 ^ (prefixWord ++ tailWord_961240).sum := by decide
  have hdescent : baseEnd_961240 < baseStart_961240 := by decide
  rcases family_descends (prefixWord ++ tailWord_961240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961261 : List Nat := [1, 5, 1, 2, 1, 1, 9]
def baseStart_961261 : Nat := 118140960795 + 961261 * 2 ^ 59
def prefixEnd_961261 : Nat := 4983230072969 + 3 ^ 40 * 961261 * 2
def baseEnd_961261 : Nat := 48749523695967288455975

theorem tailTrace_961261 : CollatzResearch.WordTrace tailWord_961261 prefixEnd_961261 48749523695967288455975 := by
  unfold tailWord_961261
  simp only [CollatzResearch.WordTrace]
  refine ⟨35060068970523042153643637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23373379313682028102429091 35060068970523042153643637)
  ·
    refine ⟨3286881465986535201904091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35060068970523042153643637 3286881465986535201904091)
    ·
      refine ⟨4930322198979802802856137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286881465986535201904091 4930322198979802802856137)
      ·
        refine ⟨3697741649234852102142103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4930322198979802802856137 3697741649234852102142103)
        ·
          refine ⟨5546612473852278153213155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3697741649234852102142103 5546612473852278153213155)
          ·
            refine ⟨8319918710778417229819733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5546612473852278153213155 8319918710778417229819733)
            ·
              refine ⟨48749523695967288455975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8319918710778417229819733 48749523695967288455975)
              ·
                rfl

theorem cell20_961261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 9].length) (baseStart_961261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961261 prefixEnd_961261 := by exact prefixLift 961261
  have htrace : WordTrace (prefixWord ++ tailWord_961261) baseStart_961261 baseEnd_961261 := by
    simpa [prefixWord, tailWord_961261, baseEnd_961261] using wordTrace_append hprefix tailTrace_961261
  have hstable : (prefixWord ++ tailWord_961261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961261).length < 2 ^ (prefixWord ++ tailWord_961261).sum := by decide
  have hdescent : baseEnd_961261 < baseStart_961261 := by decide
  rcases family_descends (prefixWord ++ tailWord_961261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961306 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_961306 : Nat := 118140960795 + 961306 * 2 ^ 59
def prefixEnd_961306 : Nat := 4983230072969 + 3 ^ 40 * 961306 * 2
def baseEnd_961306 : Nat := 438766252489885439603591

theorem tailTrace_961306 : CollatzResearch.WordTrace tailWord_961306 prefixEnd_961306 438766252489885439603591 := by
  unfold tailWord_961306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765427563840003709757943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23374473503573343226021181 8765427563840003709757943)
  ·
    refine ⟨13148141345760005564636915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8765427563840003709757943 13148141345760005564636915)
    ·
      refine ⟨19722212018640008346955373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13148141345760005564636915 19722212018640008346955373)
      ·
        refine ⟨7395829506990003130108265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19722212018640008346955373 7395829506990003130108265)
        ·
          refine ⟨5546872130242502347581199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7395829506990003130108265 5546872130242502347581199)
          ·
            refine ⟨8320308195363753521371799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5546872130242502347581199 8320308195363753521371799)
            ·
              refine ⟨12480462293045630282057699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8320308195363753521371799 12480462293045630282057699)
              ·
                refine ⟨18720693439568445423086549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12480462293045630282057699 18720693439568445423086549)
                ·
                  refine ⟨438766252489885439603591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18720693439568445423086549 438766252489885439603591)
                  ·
                    rfl

theorem cell20_961306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_961306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961306 prefixEnd_961306 := by exact prefixLift 961306
  have htrace : WordTrace (prefixWord ++ tailWord_961306) baseStart_961306 baseEnd_961306 := by
    simpa [prefixWord, tailWord_961306, baseEnd_961306] using wordTrace_append hprefix tailTrace_961306
  have hstable : (prefixWord ++ tailWord_961306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961306).length < 2 ^ (prefixWord ++ tailWord_961306).sum := by decide
  have hdescent : baseEnd_961306 < baseStart_961306 := by decide
  rcases family_descends (prefixWord ++ tailWord_961306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961316 : List Nat := [2, 3, 1, 3, 3, 2, 6]
def baseStart_961316 : Nat := 118140960795 + 961316 * 2 ^ 59
def prefixEnd_961316 : Nat := 4983230072969 + 3 ^ 40 * 961316 * 2
def baseEnd_961316 : Nat := 48752312973596649918913

theorem tailTrace_961316 : CollatzResearch.WordTrace tailWord_961316 prefixEnd_961316 48752312973596649918913 := by
  unfold tailWord_961316
  simp only [CollatzResearch.WordTrace]
  refine ⟨17531037492661893273447901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23374716656882524364597201 17531037492661893273447901)
  ·
    refine ⟨6574139059748209977542963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17531037492661893273447901 6574139059748209977542963)
    ·
      refine ⟨9861208589622314966314445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6574139059748209977542963 9861208589622314966314445)
      ·
        refine ⟨3697953221108368112367917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9861208589622314966314445 3697953221108368112367917)
        ·
          refine ⟨1386732457915638042137969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3697953221108368112367917 1386732457915638042137969)
          ·
            refine ⟨1040049343436728531603477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386732457915638042137969 1040049343436728531603477)
            ·
              refine ⟨48752312973596649918913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1040049343436728531603477 48752312973596649918913)
              ·
                rfl

theorem cell20_961316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 6].length) (baseStart_961316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961316 prefixEnd_961316 := by exact prefixLift 961316
  have htrace : WordTrace (prefixWord ++ tailWord_961316) baseStart_961316 baseEnd_961316 := by
    simpa [prefixWord, tailWord_961316, baseEnd_961316] using wordTrace_append hprefix tailTrace_961316
  have hstable : (prefixWord ++ tailWord_961316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961316).length < 2 ^ (prefixWord ++ tailWord_961316).sum := by decide
  have hdescent : baseEnd_961316 < baseStart_961316 := by decide
  rcases family_descends (prefixWord ++ tailWord_961316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961322 : List Nat := [3, 1, 4, 3, 1, 1, 3, 2, 2]
def baseStart_961322 : Nat := 118140960795 + 961322 * 2 ^ 59
def prefixEnd_961322 : Nat := 4983230072969 + 3 ^ 40 * 961322 * 2
def baseEnd_961322 : Nat := 438773555325860495070193

theorem tailTrace_961322 : CollatzResearch.WordTrace tailWord_961322 prefixEnd_961322 438773555325860495070193 := by
  unfold tailWord_961322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765573455825512392903555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23374862548868033047742813 8765573455825512392903555)
  ·
    refine ⟨13148360183738268589355333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8765573455825512392903555 13148360183738268589355333)
    ·
      refine ⟨2465317534450925360504125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13148360183738268589355333 2465317534450925360504125)
      ·
        refine ⟨924494075419097010189047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2465317534450925360504125 924494075419097010189047)
        ·
          refine ⟨1386741113128645515283571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924494075419097010189047 1386741113128645515283571)
          ·
            refine ⟨2080111669692968272925357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386741113128645515283571 2080111669692968272925357)
            ·
              refine ⟨780041876134863102347009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2080111669692968272925357 780041876134863102347009)
              ·
                refine ⟨585031407101147326760257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780041876134863102347009 585031407101147326760257)
                ·
                  refine ⟨438773555325860495070193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585031407101147326760257 438773555325860495070193)
                  ·
                    rfl

theorem cell20_961322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_961322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961322 prefixEnd_961322 := by exact prefixLift 961322
  have htrace : WordTrace (prefixWord ++ tailWord_961322) baseStart_961322 baseEnd_961322 := by
    simpa [prefixWord, tailWord_961322, baseEnd_961322] using wordTrace_append hprefix tailTrace_961322
  have hstable : (prefixWord ++ tailWord_961322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961322).length < 2 ^ (prefixWord ++ tailWord_961322).sum := by decide
  have hdescent : baseEnd_961322 < baseStart_961322 := by decide
  rcases family_descends (prefixWord ++ tailWord_961322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961326 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_961326 : Nat := 118140960795 + 961326 * 2 ^ 59
def prefixEnd_961326 : Nat := 4983230072969 + 3 ^ 40 * 961326 * 2
def baseEnd_961326 : Nat := 438775381034854258936843

theorem tailTrace_961326 : CollatzResearch.WordTrace tailWord_961326 prefixEnd_961326 438775381034854258936843 := by
  unfold tailWord_961326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4382804964410944781844979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23374959810191705503173221 4382804964410944781844979)
  ·
    refine ⟨6574207446616417172767469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4382804964410944781844979 6574207446616417172767469)
    ·
      refine ⟨2465327792481156439787801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6574207446616417172767469 2465327792481156439787801)
      ·
        refine ⟨1848995844360867329840851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2465327792481156439787801 1848995844360867329840851)
        ·
          refine ⟨2773493766541300994761277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848995844360867329840851 2773493766541300994761277)
          ·
            refine ⟨1040060162452987873035479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2773493766541300994761277 1040060162452987873035479)
            ·
              refine ⟨1560090243679481809553219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040060162452987873035479 1560090243679481809553219)
              ·
                refine ⟨2340135365519222714329829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560090243679481809553219 2340135365519222714329829)
                ·
                  refine ⟨438775381034854258936843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340135365519222714329829 438775381034854258936843)
                  ·
                    rfl

theorem cell20_961326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_961326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961326 prefixEnd_961326 := by exact prefixLift 961326
  have htrace : WordTrace (prefixWord ++ tailWord_961326) baseStart_961326 baseEnd_961326 := by
    simpa [prefixWord, tailWord_961326, baseEnd_961326] using wordTrace_append hprefix tailTrace_961326
  have hstable : (prefixWord ++ tailWord_961326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961326).length < 2 ^ (prefixWord ++ tailWord_961326).sum := by decide
  have hdescent : baseEnd_961326 < baseStart_961326 := by decide
  rcases family_descends (prefixWord ++ tailWord_961326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961351 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_961351 : Nat := 118140960795 + 961351 * 2 ^ 59
def prefixEnd_961351 : Nat := 4983230072969 + 3 ^ 40 * 961351 * 2
def baseEnd_961351 : Nat := 438786791716065283103407

theorem tailTrace_961351 : CollatzResearch.WordTrace tailWord_961351 prefixEnd_961351 438786791716065283103407 := by
  unfold tailWord_961351
  simp only [CollatzResearch.WordTrace]
  refine ⟨35063351540196987524419907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23375567693464658349613271 35063351540196987524419907)
  ·
    refine ⟨52595027310295481286629861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35063351540196987524419907 52595027310295481286629861)
    ·
      refine ⟨9861567620680402741243099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52595027310295481286629861 9861567620680402741243099)
      ·
        refine ⟨14792351431020604111864649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9861567620680402741243099 14792351431020604111864649)
        ·
          refine ⟨11094263573265453083898487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14792351431020604111864649 11094263573265453083898487)
          ·
            refine ⟨16641395359898179625847731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094263573265453083898487 16641395359898179625847731)
            ·
              refine ⟨24962093039847269438771597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16641395359898179625847731 24962093039847269438771597)
              ·
                refine ⟨9360784889942726039539349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24962093039847269438771597 9360784889942726039539349)
                ·
                  refine ⟨438786791716065283103407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9360784889942726039539349 438786791716065283103407)
                  ·
                    rfl

theorem cell20_961351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_961351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961351 prefixEnd_961351 := by exact prefixLift 961351
  have htrace : WordTrace (prefixWord ++ tailWord_961351) baseStart_961351 baseEnd_961351 := by
    simpa [prefixWord, tailWord_961351, baseEnd_961351] using wordTrace_append hprefix tailTrace_961351
  have hstable : (prefixWord ++ tailWord_961351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961351).length < 2 ^ (prefixWord ++ tailWord_961351).sum := by decide
  have hdescent : baseEnd_961351 < baseStart_961351 := by decide
  rcases family_descends (prefixWord ++ tailWord_961351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961444 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_961444 : Nat := 118140960795 + 961444 * 2 ^ 59
def prefixEnd_961444 : Nat := 4983230072969 + 3 ^ 40 * 961444 * 2
def baseEnd_961444 : Nat := 438829239450170293003027

theorem tailTrace_961444 : CollatzResearch.WordTrace tailWord_961444 prefixEnd_961444 438829239450170293003027 := by
  unfold tailWord_961444
  simp only [CollatzResearch.WordTrace]
  refine ⟨17533371764430032203777693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23377829019240042938370257 17533371764430032203777693)
  ·
    refine ⟨6575014411661262076416635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17533371764430032203777693 6575014411661262076416635)
    ·
      refine ⟨9862521617491893114624953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6575014411661262076416635 9862521617491893114624953)
      ·
        refine ⟨7396891213118919835968715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9862521617491893114624953 7396891213118919835968715)
        ·
          refine ⟨11095336819678379753953073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396891213118919835968715 11095336819678379753953073)
          ·
            refine ⟨8321502614758784815464805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11095336819678379753953073 8321502614758784815464805)
            ·
              refine ⟨1560281740267272152899651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8321502614758784815464805 1560281740267272152899651)
              ·
                refine ⟨2340422610400908229349477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560281740267272152899651 2340422610400908229349477)
                ·
                  refine ⟨438829239450170293003027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340422610400908229349477 438829239450170293003027)
                  ·
                    rfl

theorem cell20_961444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_961444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961444 prefixEnd_961444 := by exact prefixLift 961444
  have htrace : WordTrace (prefixWord ++ tailWord_961444) baseStart_961444 baseEnd_961444 := by
    simpa [prefixWord, tailWord_961444, baseEnd_961444] using wordTrace_append hprefix tailTrace_961444
  have hstable : (prefixWord ++ tailWord_961444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961444).length < 2 ^ (prefixWord ++ tailWord_961444).sum := by decide
  have hdescent : baseEnd_961444 < baseStart_961444 := by decide
  rcases family_descends (prefixWord ++ tailWord_961444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961496 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_961496 : Nat := 118140960795 + 961496 * 2 ^ 59
def prefixEnd_961496 : Nat := 4983230072969 + 3 ^ 40 * 961496 * 2
def baseEnd_961496 : Nat := 438852973667089223269481

theorem tailTrace_961496 : CollatzResearch.WordTrace tailWord_961496 prefixEnd_961496 438852973667089223269481 := by
  unfold tailWord_961496
  simp only [CollatzResearch.WordTrace]
  refine ⟨17534320062335838644224171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23379093416447784858965561 17534320062335838644224171)
  ·
    refine ⟨26301480093503757966336257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17534320062335838644224171 26301480093503757966336257)
    ·
      refine ⟨19726110070127818474752193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26301480093503757966336257 19726110070127818474752193)
      ·
        refine ⟨14794582552595863856064145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19726110070127818474752193 14794582552595863856064145)
        ·
          refine ⟨11095936914446897892048109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14794582552595863856064145 11095936914446897892048109)
          ·
            refine ⟨4160976342917586709518041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11095936914446897892048109 4160976342917586709518041)
            ·
              refine ⟨3120732257188190032138531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160976342917586709518041 3120732257188190032138531)
              ·
                refine ⟨4681098385782285048207797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120732257188190032138531 4681098385782285048207797)
                ·
                  refine ⟨438852973667089223269481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4681098385782285048207797 438852973667089223269481)
                  ·
                    rfl

theorem cell20_961496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_961496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961496 prefixEnd_961496 := by exact prefixLift 961496
  have htrace : WordTrace (prefixWord ++ tailWord_961496) baseStart_961496 baseEnd_961496 := by
    simpa [prefixWord, tailWord_961496, baseEnd_961496] using wordTrace_append hprefix tailTrace_961496
  have hstable : (prefixWord ++ tailWord_961496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961496).length < 2 ^ (prefixWord ++ tailWord_961496).sum := by decide
  have hdescent : baseEnd_961496 < baseStart_961496 := by decide
  rcases family_descends (prefixWord ++ tailWord_961496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961506 : List Nat := [3, 3, 3, 1, 1, 1, 1, 7]
def baseStart_961506 : Nat := 118140960795 + 961506 * 2 ^ 59
def prefixEnd_961506 : Nat := 4983230072969 + 3 ^ 40 * 961506 * 2
def baseEnd_961506 : Nat := 146285845979857877645369

theorem tailTrace_961506 : CollatzResearch.WordTrace tailWord_961506 prefixEnd_961506 146285845979857877645369 := by
  unfold tailWord_961506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8767251213658862249078093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23379336569756965997541581 8767251213658862249078093)
  ·
    refine ⟨3287719205122073343404285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8767251213658862249078093 3287719205122073343404285)
    ·
      refine ⟨1232894701920777503776607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3287719205122073343404285 1232894701920777503776607)
      ·
        refine ⟨1849342052881166255664911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232894701920777503776607 1849342052881166255664911)
        ·
          refine ⟨2774013079321749383497367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849342052881166255664911 2774013079321749383497367)
          ·
            refine ⟨4161019618982624075246051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774013079321749383497367 4161019618982624075246051)
            ·
              refine ⟨6241529428473936112869077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161019618982624075246051 6241529428473936112869077)
              ·
                refine ⟨146285845979857877645369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6241529428473936112869077 146285845979857877645369)
                ·
                  rfl

theorem cell20_961506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_961506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961506 prefixEnd_961506 := by exact prefixLift 961506
  have htrace : WordTrace (prefixWord ++ tailWord_961506) baseStart_961506 baseEnd_961506 := by
    simpa [prefixWord, tailWord_961506, baseEnd_961506] using wordTrace_append hprefix tailTrace_961506
  have hstable : (prefixWord ++ tailWord_961506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961506).length < 2 ^ (prefixWord ++ tailWord_961506).sum := by decide
  have hdescent : baseEnd_961506 < baseStart_961506 := by decide
  rcases family_descends (prefixWord ++ tailWord_961506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961548 : List Nat := [2, 2, 1, 2, 3, 10]
def baseStart_961548 : Nat := 118140960795 + 961548 * 2 ^ 59
def prefixEnd_961548 : Nat := 4983230072969 + 3 ^ 40 * 961548 * 2
def baseEnd_961548 : Nat := 16254692884592894575405

theorem tailTrace_961548 : CollatzResearch.WordTrace tailWord_961548 prefixEnd_961548 16254692884592894575405 := by
  unfold tailWord_961548
  simp only [CollatzResearch.WordTrace]
  refine ⟨17535268360241645084670649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23380357813655526779560865 17535268360241645084670649)
  ·
    refine ⟨13151451270181233813502987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17535268360241645084670649 13151451270181233813502987)
    ·
      refine ⟨19727176905271850720254481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13151451270181233813502987 19727176905271850720254481)
      ·
        refine ⟨14795382678953888040190861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19727176905271850720254481 14795382678953888040190861)
        ·
          refine ⟨5548268504607708015071573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14795382678953888040190861 5548268504607708015071573)
          ·
            refine ⟨16254692884592894575405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5548268504607708015071573 16254692884592894575405)
            ·
              rfl

theorem cell20_961548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 10].length) (baseStart_961548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961548 prefixEnd_961548 := by exact prefixLift 961548
  have htrace : WordTrace (prefixWord ++ tailWord_961548) baseStart_961548 baseEnd_961548 := by
    simpa [prefixWord, tailWord_961548, baseEnd_961548] using wordTrace_append hprefix tailTrace_961548
  have hstable : (prefixWord ++ tailWord_961548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961548).length < 2 ^ (prefixWord ++ tailWord_961548).sum := by decide
  have hdescent : baseEnd_961548 < baseStart_961548 := by decide
  rcases family_descends (prefixWord ++ tailWord_961548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961575 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 4]
def baseStart_961575 : Nat := 118140960795 + 961575 * 2 ^ 59
def prefixEnd_961575 : Nat := 4983230072969 + 3 ^ 40 * 961575 * 2
def baseEnd_961575 : Nat := 438889031419716059635825

theorem tailTrace_961575 : CollatzResearch.WordTrace tailWord_961575 prefixEnd_961575 438889031419716059635825 := by
  unfold tailWord_961575
  simp only [CollatzResearch.WordTrace]
  refine ⟨35071521491385473780574179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23381014327590315853716119 35071521491385473780574179)
  ·
    refine ⟨52607282237078210670861269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35071521491385473780574179 52607282237078210670861269)
    ·
      refine ⟨1232983177431520562598311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 52607282237078210670861269 1232983177431520562598311)
      ·
        refine ⟨1849474766147280843897467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232983177431520562598311 1849474766147280843897467)
        ·
          refine ⟨2774212149220921265846201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849474766147280843897467 2774212149220921265846201)
          ·
            refine ⟨2080659111915690949384651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774212149220921265846201 2080659111915690949384651)
            ·
              refine ⟨3120988667873536424076977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080659111915690949384651 3120988667873536424076977)
              ·
                refine ⟨2340741500905152318057733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120988667873536424076977 2340741500905152318057733)
                ·
                  refine ⟨438889031419716059635825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340741500905152318057733 438889031419716059635825)
                  ·
                    rfl

theorem cell20_961575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 4].length) (baseStart_961575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961575 prefixEnd_961575 := by exact prefixLift 961575
  have htrace : WordTrace (prefixWord ++ tailWord_961575) baseStart_961575 baseEnd_961575 := by
    simpa [prefixWord, tailWord_961575, baseEnd_961575] using wordTrace_append hprefix tailTrace_961575
  have hstable : (prefixWord ++ tailWord_961575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961575).length < 2 ^ (prefixWord ++ tailWord_961575).sum := by decide
  have hdescent : baseEnd_961575 < baseStart_961575 := by decide
  rcases family_descends (prefixWord ++ tailWord_961575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961579 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_961579 : Nat := 118140960795 + 961579 * 2 ^ 59
def prefixEnd_961579 : Nat := 4983230072969 + 3 ^ 40 * 961579 * 2
def baseEnd_961579 : Nat := 438890857128709823502475

theorem tailTrace_961579 : CollatzResearch.WordTrace tailWord_961579 prefixEnd_961579 438890857128709823502475 := by
  unfold tailWord_961579
  simp only [CollatzResearch.WordTrace]
  refine ⟨35071667383370982463719791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23381111588913988309146527 35071667383370982463719791)
  ·
    refine ⟨52607501075056473695579687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35071667383370982463719791 52607501075056473695579687)
    ·
      refine ⟨78911251612584710543369531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52607501075056473695579687 78911251612584710543369531)
      ·
        refine ⟨118366877418877065815054297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78911251612584710543369531 118366877418877065815054297)
        ·
          refine ⟨88775158064157799361290723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118366877418877065815054297 88775158064157799361290723)
          ·
            refine ⟨133162737096236699041936085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88775158064157799361290723 133162737096236699041936085)
            ·
              refine ⟨3121001650693047633795377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 133162737096236699041936085 3121001650693047633795377)
              ·
                refine ⟨2340751238019785725346533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121001650693047633795377 2340751238019785725346533)
                ·
                  refine ⟨438890857128709823502475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340751238019785725346533 438890857128709823502475)
                  ·
                    rfl

theorem cell20_961579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_961579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961579 prefixEnd_961579 := by exact prefixLift 961579
  have htrace : WordTrace (prefixWord ++ tailWord_961579) baseStart_961579 baseEnd_961579 := by
    simpa [prefixWord, tailWord_961579, baseEnd_961579] using wordTrace_append hprefix tailTrace_961579
  have hstable : (prefixWord ++ tailWord_961579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961579).length < 2 ^ (prefixWord ++ tailWord_961579).sum := by decide
  have hdescent : baseEnd_961579 < baseStart_961579 := by decide
  rcases family_descends (prefixWord ++ tailWord_961579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961582 : List Nat := [4, 1, 3, 1, 1, 1, 5, 4]
def baseStart_961582 : Nat := 118140960795 + 961582 * 2 ^ 59
def prefixEnd_961582 : Nat := 4983230072969 + 3 ^ 40 * 961582 * 2
def baseEnd_961582 : Nat := 146297408803485048800821

theorem tailTrace_961582 : CollatzResearch.WordTrace tailWord_961582 prefixEnd_961582 146297408803485048800821 := by
  unfold tailWord_961582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383972100295014247009875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23381184534906742650719333 4383972100295014247009875)
  ·
    refine ⟨6575958150442521370514813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4383972100295014247009875 6575958150442521370514813)
    ·
      refine ⟨2465984306415945513943055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6575958150442521370514813 2465984306415945513943055)
      ·
        refine ⟨3698976459623918270914583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465984306415945513943055 3698976459623918270914583)
        ·
          refine ⟨5548464689435877406371875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3698976459623918270914583 5548464689435877406371875)
          ·
            refine ⟨8322697034153816109557813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5548464689435877406371875 8322697034153816109557813)
            ·
              refine ⟨780252846951920260271045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8322697034153816109557813 780252846951920260271045)
              ·
                refine ⟨146297408803485048800821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 780252846951920260271045 146297408803485048800821)
                ·
                  rfl

theorem cell20_961582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_961582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961582 prefixEnd_961582 := by exact prefixLift 961582
  have htrace : WordTrace (prefixWord ++ tailWord_961582) baseStart_961582 baseEnd_961582 := by
    simpa [prefixWord, tailWord_961582, baseEnd_961582] using wordTrace_append hprefix tailTrace_961582
  have hstable : (prefixWord ++ tailWord_961582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961582).length < 2 ^ (prefixWord ++ tailWord_961582).sum := by decide
  have hdescent : baseEnd_961582 < baseStart_961582 := by decide
  rcases family_descends (prefixWord ++ tailWord_961582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961606 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_961606 : Nat := 118140960795 + 961606 * 2 ^ 59
def prefixEnd_961606 : Nat := 4983230072969 + 3 ^ 40 * 961606 * 2
def baseEnd_961606 : Nat := 438903180664417729602365

theorem tailTrace_961606 : CollatzResearch.WordTrace tailWord_961606 prefixEnd_961606 438903180664417729602365 := by
  unfold tailWord_961606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096020379821036439842271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23381768102848777383301781 1096020379821036439842271)
  ·
    refine ⟨1644030569731554659763407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1096020379821036439842271 1644030569731554659763407)
    ·
      refine ⟨2466045854597331989645111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644030569731554659763407 2466045854597331989645111)
      ·
        refine ⟨3699068781895997984467667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2466045854597331989645111 3699068781895997984467667)
        ·
          refine ⟨5548603172843996976701501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3699068781895997984467667 5548603172843996976701501)
          ·
            refine ⟨2080726189816498866263063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5548603172843996976701501 2080726189816498866263063)
            ·
              refine ⟨3121089284724748299394595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080726189816498866263063 3121089284724748299394595)
              ·
                refine ⟨4681633927087122449091893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121089284724748299394595 4681633927087122449091893)
                ·
                  refine ⟨438903180664417729602365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4681633927087122449091893 438903180664417729602365)
                  ·
                    rfl

theorem cell20_961606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_961606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961606 prefixEnd_961606 := by exact prefixLift 961606
  have htrace : WordTrace (prefixWord ++ tailWord_961606) baseStart_961606 baseEnd_961606 := by
    simpa [prefixWord, tailWord_961606, baseEnd_961606] using wordTrace_append hprefix tailTrace_961606
  have hstable : (prefixWord ++ tailWord_961606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961606).length < 2 ^ (prefixWord ++ tailWord_961606).sum := by decide
  have hdescent : baseEnd_961606 < baseStart_961606 := by decide
  rcases family_descends (prefixWord ++ tailWord_961606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961613 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 4]
def baseStart_961613 : Nat := 118140960795 + 961613 * 2 ^ 59
def prefixEnd_961613 : Nat := 4983230072969 + 3 ^ 40 * 961613 * 2
def baseEnd_961613 : Nat := 438906375655156816369003

theorem tailTrace_961613 : CollatzResearch.WordTrace tailWord_961613 prefixEnd_961613 438906375655156816369003 := by
  unfold tailWord_961613
  simp only [CollatzResearch.WordTrace]
  refine ⟨35072907465247806270457493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23381938310165204180304995 35072907465247806270457493)
  ·
    refine ⟨1644042537433490918927695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35072907465247806270457493 1644042537433490918927695)
    ·
      refine ⟨2466063806150236378391543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644042537433490918927695 2466063806150236378391543)
      ·
        refine ⟨3699095709225354567587315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2466063806150236378391543 3699095709225354567587315)
        ·
          refine ⟨5548643563838031851380973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3699095709225354567587315 5548643563838031851380973)
          ·
            refine ⟨2080741336439261944267865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5548643563838031851380973 2080741336439261944267865)
            ·
              refine ⟨1560556002329446458200899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2080741336439261944267865 1560556002329446458200899)
              ·
                refine ⟨2340834003494169687301349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560556002329446458200899 2340834003494169687301349)
                ·
                  refine ⟨438906375655156816369003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340834003494169687301349 438906375655156816369003)
                  ·
                    rfl

theorem cell20_961613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_961613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961613 prefixEnd_961613 := by exact prefixLift 961613
  have htrace : WordTrace (prefixWord ++ tailWord_961613) baseStart_961613 baseEnd_961613 := by
    simpa [prefixWord, tailWord_961613, baseEnd_961613] using wordTrace_append hprefix tailTrace_961613
  have hstable : (prefixWord ++ tailWord_961613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961613).length < 2 ^ (prefixWord ++ tailWord_961613).sum := by decide
  have hdescent : baseEnd_961613 < baseStart_961613 := by decide
  rcases family_descends (prefixWord ++ tailWord_961613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961617 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_961617 : Nat := 118140960795 + 961617 * 2 ^ 59
def prefixEnd_961617 : Nat := 4983230072969 + 3 ^ 40 * 961617 * 2
def baseEnd_961617 : Nat := 438908201364150580235653

theorem tailTrace_961617 : CollatzResearch.WordTrace tailWord_961617 prefixEnd_961617 438908201364150580235653 := by
  unfold tailWord_961617
  simp only [CollatzResearch.WordTrace]
  refine ⟨35073053357233314953603105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23382035571488876635735403 35073053357233314953603105)
  ·
    refine ⟨26304790017924986215202329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35073053357233314953603105 26304790017924986215202329)
    ·
      refine ⟨19728592513443739661401747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26304790017924986215202329 19728592513443739661401747)
      ·
        refine ⟨29592888770165609492102621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19728592513443739661401747 29592888770165609492102621)
        ·
          refine ⟨11097333288812103559538483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29592888770165609492102621 11097333288812103559538483)
          ·
            refine ⟨16645999933218155339307725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11097333288812103559538483 16645999933218155339307725)
            ·
              refine ⟨6242249974956808252240397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16645999933218155339307725 6242249974956808252240397)
              ·
                refine ⟨2340843740608803094590149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6242249974956808252240397 2340843740608803094590149)
                ·
                  refine ⟨438908201364150580235653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340843740608803094590149 438908201364150580235653)
                  ·
                    rfl

theorem cell20_961617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_961617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961617 prefixEnd_961617 := by exact prefixLift 961617
  have htrace : WordTrace (prefixWord ++ tailWord_961617) baseStart_961617 baseEnd_961617 := by
    simpa [prefixWord, tailWord_961617, baseEnd_961617] using wordTrace_append hprefix tailTrace_961617
  have hstable : (prefixWord ++ tailWord_961617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961617).length < 2 ^ (prefixWord ++ tailWord_961617).sum := by decide
  have hdescent : baseEnd_961617 < baseStart_961617 := by decide
  rcases family_descends (prefixWord ++ tailWord_961617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961624 : List Nat := [2, 1, 2, 2, 1, 3, 2, 7]
def baseStart_961624 : Nat := 118140960795 + 961624 * 2 ^ 59
def prefixEnd_961624 : Nat := 4983230072969 + 3 ^ 40 * 961624 * 2
def baseEnd_961624 : Nat := 146303798784963222334097

theorem tailTrace_961624 : CollatzResearch.WordTrace tailWord_961624 prefixEnd_961624 146303798784963222334097 := by
  unfold tailWord_961624
  simp only [CollatzResearch.WordTrace]
  refine ⟨17536654334103977574553963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23382205778805303432738617 17536654334103977574553963)
  ·
    refine ⟨26304981501155966361830945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17536654334103977574553963 26304981501155966361830945)
    ·
      refine ⟨19728736125866974771373209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26304981501155966361830945 19728736125866974771373209)
      ·
        refine ⟨14796552094400231078529907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19728736125866974771373209 14796552094400231078529907)
        ·
          refine ⟨22194828141600346617794861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14796552094400231078529907 22194828141600346617794861)
          ·
            refine ⟨8323060553100129981673073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22194828141600346617794861 8323060553100129981673073)
            ·
              refine ⟨6242295414825097486254805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8323060553100129981673073 6242295414825097486254805)
              ·
                refine ⟨146303798784963222334097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6242295414825097486254805 146303798784963222334097)
                ·
                  rfl

theorem cell20_961624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_961624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961624 prefixEnd_961624 := by exact prefixLift 961624
  have htrace : WordTrace (prefixWord ++ tailWord_961624) baseStart_961624 baseEnd_961624 := by
    simpa [prefixWord, tailWord_961624, baseEnd_961624] using wordTrace_append hprefix tailTrace_961624
  have hstable : (prefixWord ++ tailWord_961624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961624).length < 2 ^ (prefixWord ++ tailWord_961624).sum := by decide
  have hdescent : baseEnd_961624 < baseStart_961624 := by decide
  rcases family_descends (prefixWord ++ tailWord_961624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961630 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_961630 : Nat := 118140960795 + 961630 * 2 ^ 59
def prefixEnd_961630 : Nat := 4983230072969 + 3 ^ 40 * 961630 * 2
def baseEnd_961630 : Nat := 438914134918380312802267

theorem tailTrace_961630 : CollatzResearch.WordTrace tailWord_961630 prefixEnd_961630 438914134918380312802267 := by
  unfold tailWord_961630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4384190938273277271728293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23382351670790812115884229 4384190938273277271728293)
  ·
    refine ⟨822035800926239488449055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4384190938273277271728293 822035800926239488449055)
    ·
      refine ⟨1233053701389359232673583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822035800926239488449055 1233053701389359232673583)
      ·
        refine ⟨1849580552084038849010375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233053701389359232673583 1849580552084038849010375)
        ·
          refine ⟨2774370828126058273515563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849580552084038849010375 2774370828126058273515563)
          ·
            refine ⟨4161556242189087410273345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774370828126058273515563 4161556242189087410273345)
            ·
              refine ⟨3121167181641815557705009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161556242189087410273345 3121167181641815557705009)
              ·
                refine ⟨2340875386231361668278757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121167181641815557705009 2340875386231361668278757)
                ·
                  refine ⟨438914134918380312802267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340875386231361668278757 438914134918380312802267)
                  ·
                    rfl

theorem cell20_961630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_961630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961630 prefixEnd_961630 := by exact prefixLift 961630
  have htrace : WordTrace (prefixWord ++ tailWord_961630) baseStart_961630 baseEnd_961630 := by
    simpa [prefixWord, tailWord_961630, baseEnd_961630] using wordTrace_append hprefix tailTrace_961630
  have hstable : (prefixWord ++ tailWord_961630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961630).length < 2 ^ (prefixWord ++ tailWord_961630).sum := by decide
  have hdescent : baseEnd_961630 < baseStart_961630 := by decide
  rcases family_descends (prefixWord ++ tailWord_961630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961641 : List Nat := [1, 2, 1, 1, 1, 6, 4, 4]
def baseStart_961641 : Nat := 118140960795 + 961641 * 2 ^ 59
def prefixEnd_961641 : Nat := 4983230072969 + 3 ^ 40 * 961641 * 2
def baseEnd_961641 : Nat := 146306385206037721145185

theorem tailTrace_961641 : CollatzResearch.WordTrace tailWord_961641 prefixEnd_961641 146306385206037721145185 := by
  unfold tailWord_961641
  simp only [CollatzResearch.WordTrace]
  refine ⟨35073928709146367052476777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23382619139430911368317851 35073928709146367052476777)
  ·
    refine ⟨26305446531859775289357583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35073928709146367052476777 26305446531859775289357583)
    ·
      refine ⟨39458169797789662934036375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26305446531859775289357583 39458169797789662934036375)
      ·
        refine ⟨59187254696684494401054563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39458169797789662934036375 59187254696684494401054563)
        ·
          refine ⟨88780882045026741601581845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59187254696684494401054563 88780882045026741601581845)
          ·
            refine ⟨4161603845860628512574149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88780882045026741601581845 4161603845860628512574149)
            ·
              refine ⟨780300721098867846107653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4161603845860628512574149 780300721098867846107653)
              ·
                refine ⟨146306385206037721145185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 780300721098867846107653 146306385206037721145185)
                ·
                  rfl

theorem cell20_961641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 4].length) (baseStart_961641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961641 prefixEnd_961641 := by exact prefixLift 961641
  have htrace : WordTrace (prefixWord ++ tailWord_961641) baseStart_961641 baseEnd_961641 := by
    simpa [prefixWord, tailWord_961641, baseEnd_961641] using wordTrace_append hprefix tailTrace_961641
  have hstable : (prefixWord ++ tailWord_961641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961641).length < 2 ^ (prefixWord ++ tailWord_961641).sum := by decide
  have hdescent : baseEnd_961641 < baseStart_961641 := by decide
  rcases family_descends (prefixWord ++ tailWord_961641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961668 : List Nat := [2, 3, 2, 1, 2, 3, 3, 2, 2]
def baseStart_961668 : Nat := 118140960795 + 961668 * 2 ^ 59
def prefixEnd_961668 : Nat := 4983230072969 + 3 ^ 40 * 961668 * 2
def baseEnd_961668 : Nat := 438931479153821069535445

theorem tailTrace_961668 : CollatzResearch.WordTrace tailWord_961668 prefixEnd_961668 438931479153821069535445 := by
  unfold tailWord_961668
  simp only [CollatzResearch.WordTrace]
  refine ⟨17537456740024275331854829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23383275653365700442473105 17537456740024275331854829)
  ·
    refine ⟨6576546277509103249445561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17537456740024275331854829 6576546277509103249445561)
    ·
      refine ⟨4932409708131827437084171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6576546277509103249445561 4932409708131827437084171)
      ·
        refine ⟨7398614562197741155626257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932409708131827437084171 7398614562197741155626257)
        ·
          refine ⟨5548960921648305866719693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7398614562197741155626257 5548960921648305866719693)
          ·
            refine ⟨2080860345618114700019885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5548960921648305866719693 2080860345618114700019885)
            ·
              refine ⟨780322629606793012507457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2080860345618114700019885 780322629606793012507457)
              ·
                refine ⟨585241972205094759380593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780322629606793012507457 585241972205094759380593)
                ·
                  refine ⟨438931479153821069535445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585241972205094759380593 438931479153821069535445)
                  ·
                    rfl

theorem cell20_961668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_961668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961668 prefixEnd_961668 := by exact prefixLift 961668
  have htrace : WordTrace (prefixWord ++ tailWord_961668) baseStart_961668 baseEnd_961668 := by
    simpa [prefixWord, tailWord_961668, baseEnd_961668] using wordTrace_append hprefix tailTrace_961668
  have hstable : (prefixWord ++ tailWord_961668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961668).length < 2 ^ (prefixWord ++ tailWord_961668).sum := by decide
  have hdescent : baseEnd_961668 < baseStart_961668 := by decide
  rcases family_descends (prefixWord ++ tailWord_961668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961682 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_961682 : Nat := 118140960795 + 961682 * 2 ^ 59
def prefixEnd_961682 : Nat := 4983230072969 + 3 ^ 40 * 961682 * 2
def baseEnd_961682 : Nat := 438937869135299243068721

theorem tailTrace_961682 : CollatzResearch.WordTrace tailWord_961682 prefixEnd_961682 438937869135299243068721 := by
  unfold tailWord_961682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8768856025499457763679825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23383616067998554036479533 8768856025499457763679825)
  ·
    refine ⟨6576642019124593322759869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8768856025499457763679825 6576642019124593322759869)
    ·
      refine ⟨2466240757171722496034951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6576642019124593322759869 2466240757171722496034951)
      ·
        refine ⟨3699361135757583744052427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2466240757171722496034951 3699361135757583744052427)
        ·
          refine ⟨5549041703636375616078641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3699361135757583744052427 5549041703636375616078641)
          ·
            refine ⟨4161781277727281712058981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5549041703636375616078641 4161781277727281712058981)
            ·
              refine ⟨780333989573865321011059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4161781277727281712058981 780333989573865321011059)
              ·
                refine ⟨1170500984360797981516589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780333989573865321011059 1170500984360797981516589)
                ·
                  refine ⟨438937869135299243068721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170500984360797981516589 438937869135299243068721)
                  ·
                    rfl

theorem cell20_961682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_961682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961682 prefixEnd_961682 := by exact prefixLift 961682
  have htrace : WordTrace (prefixWord ++ tailWord_961682) baseStart_961682 baseEnd_961682 := by
    simpa [prefixWord, tailWord_961682, baseEnd_961682] using wordTrace_append hprefix tailTrace_961682
  have hstable : (prefixWord ++ tailWord_961682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961682).length < 2 ^ (prefixWord ++ tailWord_961682).sum := by decide
  have hdescent : baseEnd_961682 < baseStart_961682 := by decide
  rcases family_descends (prefixWord ++ tailWord_961682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961693 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_961693 : Nat := 118140960795 + 961693 * 2 ^ 59
def prefixEnd_961693 : Nat := 4983230072969 + 3 ^ 40 * 961693 * 2
def baseEnd_961693 : Nat := 438942889835032093702009

theorem tailTrace_961693 : CollatzResearch.WordTrace tailWord_961693 prefixEnd_961693 438942889835032093702009 := by
  unfold tailWord_961693
  simp only [CollatzResearch.WordTrace]
  refine ⟨35075825304957979933369733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23383883536638653288913155 35075825304957979933369733)
  ·
    refine ⟨6576717244679621237506825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35075825304957979933369733 6576717244679621237506825)
    ·
      refine ⟨4932537933509715928130119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6576717244679621237506825 4932537933509715928130119)
      ·
        refine ⟨7398806900264573892195179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932537933509715928130119 7398806900264573892195179)
        ·
          refine ⟨11098210350396860838292769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7398806900264573892195179 11098210350396860838292769)
          ·
            refine ⟨8323657762797645628719577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11098210350396860838292769 8323657762797645628719577)
            ·
              refine ⟨6242743322098234221539683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8323657762797645628719577 6242743322098234221539683)
              ·
                refine ⟨9364114983147351332309525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6242743322098234221539683 9364114983147351332309525)
                ·
                  refine ⟨438942889835032093702009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9364114983147351332309525 438942889835032093702009)
                  ·
                    rfl

theorem cell20_961693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_961693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_961693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_961693 prefixEnd_961693 := by exact prefixLift 961693
  have htrace : WordTrace (prefixWord ++ tailWord_961693) baseStart_961693 baseEnd_961693 := by
    simpa [prefixWord, tailWord_961693, baseEnd_961693] using wordTrace_append hprefix tailTrace_961693
  have hstable : (prefixWord ++ tailWord_961693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961693).length < 2 ^ (prefixWord ++ tailWord_961693).sum := by decide
  have hdescent : baseEnd_961693 < baseStart_961693 := by decide
  rcases family_descends (prefixWord ++ tailWord_961693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
