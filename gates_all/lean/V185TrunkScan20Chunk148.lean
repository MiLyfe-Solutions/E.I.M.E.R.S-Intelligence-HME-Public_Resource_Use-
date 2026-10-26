import V185TrunkScan20Chunk147

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_899917 : List Nat := [1, 6, 1, 2, 2, 1, 1, 6]
def baseStart_899917 : Nat := 118140960795 + 899917 * 2 ^ 59
def prefixEnd_899917 : Nat := 4983230072969 + 3 ^ 40 * 899917 * 2
def baseEnd_899917 : Nat := 136915546711780979051515

theorem tailTrace_899917 : CollatzResearch.WordTrace tailWord_899917 prefixEnd_899917 136915546711780979051515 := by
  unfold tailWord_899917
  simp only [CollatzResearch.WordTrace]
  refine ⟨32822669480761877432538005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21881779653841251621692003 32822669480761877432538005)
  ·
    refine ⟨1538562631910713004650219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32822669480761877432538005 1538562631910713004650219)
    ·
      refine ⟨2307843947866069506975329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538562631910713004650219 2307843947866069506975329)
      ·
        refine ⟨1730882960899552130231497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2307843947866069506975329 1730882960899552130231497)
        ·
          refine ⟨1298162220674664097673623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1730882960899552130231497 1298162220674664097673623)
          ·
            refine ⟨1947243331011996146510435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298162220674664097673623 1947243331011996146510435)
            ·
              refine ⟨2920864996517994219765653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947243331011996146510435 2920864996517994219765653)
              ·
                refine ⟨136915546711780979051515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2920864996517994219765653 136915546711780979051515)
                ·
                  rfl

theorem cell20_899917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 6].length) (baseStart_899917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899917 prefixEnd_899917 := by exact prefixLift 899917
  have htrace : WordTrace (prefixWord ++ tailWord_899917) baseStart_899917 baseEnd_899917 := by
    simpa [prefixWord, tailWord_899917, baseEnd_899917] using wordTrace_append hprefix tailTrace_899917
  have hstable : (prefixWord ++ tailWord_899917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899917).length < 2 ^ (prefixWord ++ tailWord_899917).sum := by decide
  have hdescent : baseEnd_899917 < baseStart_899917 := by decide
  rcases family_descends (prefixWord ++ tailWord_899917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899948 : List Nat := [2, 2, 1, 1, 4, 1, 5, 2, 2]
def baseStart_899948 : Nat := 118140960795 + 899948 * 2 ^ 59
def prefixEnd_899948 : Nat := 4983230072969 + 3 ^ 40 * 899948 * 2
def baseEnd_899948 : Nat := 410760789380044607121085

theorem tailTrace_899948 : CollatzResearch.WordTrace tailWord_899948 prefixEnd_899948 410760789380044607121085 := by
  unfold tailWord_899948
  simp only [CollatzResearch.WordTrace]
  refine ⟨16411900071824784863458249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21882533429099713151277665 16411900071824784863458249)
  ·
    refine ⟨12308925053868588647593687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16411900071824784863458249 12308925053868588647593687)
    ·
      refine ⟨18463387580802882971390531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12308925053868588647593687 18463387580802882971390531)
      ·
        refine ⟨27695081371204324457085797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18463387580802882971390531 27695081371204324457085797)
        ·
          refine ⟨5192827757100810835703587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27695081371204324457085797 5192827757100810835703587)
          ·
            refine ⟨7789241635651216253555381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5192827757100810835703587 7789241635651216253555381)
            ·
              refine ⟨730241403342301523770817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7789241635651216253555381 730241403342301523770817)
              ·
                refine ⟨547681052506726142828113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730241403342301523770817 547681052506726142828113)
                ·
                  refine ⟨410760789380044607121085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547681052506726142828113 410760789380044607121085)
                  ·
                    rfl

theorem cell20_899948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_899948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899948 prefixEnd_899948 := by exact prefixLift 899948
  have htrace : WordTrace (prefixWord ++ tailWord_899948) baseStart_899948 baseEnd_899948 := by
    simpa [prefixWord, tailWord_899948, baseEnd_899948] using wordTrace_append hprefix tailTrace_899948
  have hstable : (prefixWord ++ tailWord_899948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899948).length < 2 ^ (prefixWord ++ tailWord_899948).sum := by decide
  have hdescent : baseEnd_899948 < baseStart_899948 := by decide
  rcases family_descends (prefixWord ++ tailWord_899948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899952 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_899952 : Nat := 118140960795 + 899952 * 2 ^ 59
def prefixEnd_899952 : Nat := 4983230072969 + 3 ^ 40 * 899952 * 2
def baseEnd_899952 : Nat := 410762615089038370987735

theorem tailTrace_899952 : CollatzResearch.WordTrace tailWord_899952 prefixEnd_899952 410762615089038370987735 := by
  unfold tailWord_899952
  simp only [CollatzResearch.WordTrace]
  refine ⟨16411973017817539205031055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21882630690423385606708073 16411973017817539205031055)
  ·
    refine ⟨24617959526726308807546583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16411973017817539205031055 24617959526726308807546583)
    ·
      refine ⟨36926939290089463211319875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24617959526726308807546583 36926939290089463211319875)
      ·
        refine ⟨55390408935134194816979813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36926939290089463211319875 55390408935134194816979813)
        ·
          refine ⟨10385701675337661528183715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55390408935134194816979813 10385701675337661528183715)
          ·
            refine ⟨15578552513006492292275573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10385701675337661528183715 15578552513006492292275573)
            ·
              refine ⟨1460489298094358652400835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15578552513006492292275573 1460489298094358652400835)
              ·
                refine ⟨2190733947141537978601253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460489298094358652400835 2190733947141537978601253)
                ·
                  refine ⟨410762615089038370987735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2190733947141537978601253 410762615089038370987735)
                  ·
                    rfl

theorem cell20_899952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_899952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899952 prefixEnd_899952 := by exact prefixLift 899952
  have htrace : WordTrace (prefixWord ++ tailWord_899952) baseStart_899952 baseEnd_899952 := by
    simpa [prefixWord, tailWord_899952, baseEnd_899952] using wordTrace_append hprefix tailTrace_899952
  have hstable : (prefixWord ++ tailWord_899952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899952).length < 2 ^ (prefixWord ++ tailWord_899952).sum := by decide
  have hdescent : baseEnd_899952 < baseStart_899952 := by decide
  rcases family_descends (prefixWord ++ tailWord_899952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899958 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_899958 : Nat := 118140960795 + 899958 * 2 ^ 59
def prefixEnd_899958 : Nat := 4983230072969 + 3 ^ 40 * 899958 * 2
def baseEnd_899958 : Nat := 410765353652529016787711

theorem tailTrace_899958 : CollatzResearch.WordTrace tailWord_899958 prefixEnd_899958 410765353652529016787711 := by
  unfold tailWord_899958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2051510304600833839673783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21882776582408894289853685 2051510304600833839673783)
  ·
    refine ⟨3077265456901250759510675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2051510304600833839673783 3077265456901250759510675)
    ·
      refine ⟨4615898185351876139266013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077265456901250759510675 4615898185351876139266013)
      ·
        refine ⟨1730961819506953552224755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4615898185351876139266013 1730961819506953552224755)
        ·
          refine ⟨2596442729260430328337133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730961819506953552224755 2596442729260430328337133)
          ·
            refine ⟨973666023472661373126425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2596442729260430328337133 973666023472661373126425)
            ·
              refine ⟨730249517604496029844819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973666023472661373126425 730249517604496029844819)
              ·
                refine ⟨1095374276406744044767229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730249517604496029844819 1095374276406744044767229)
                ·
                  refine ⟨410765353652529016787711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095374276406744044767229 410765353652529016787711)
                  ·
                    rfl

theorem cell20_899958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_899958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899958 prefixEnd_899958 := by exact prefixLift 899958
  have htrace : WordTrace (prefixWord ++ tailWord_899958) baseStart_899958 baseEnd_899958 := by
    simpa [prefixWord, tailWord_899958, baseEnd_899958] using wordTrace_append hprefix tailTrace_899958
  have hstable : (prefixWord ++ tailWord_899958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899958).length < 2 ^ (prefixWord ++ tailWord_899958).sum := by decide
  have hdescent : baseEnd_899958 < baseStart_899958 := by decide
  rcases family_descends (prefixWord ++ tailWord_899958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900021 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 3]
def baseStart_900021 : Nat := 118140960795 + 900021 * 2 ^ 59
def prefixEnd_900021 : Nat := 4983230072969 + 3 ^ 40 * 900021 * 2
def baseEnd_900021 : Nat := 410794108569180797687453

theorem tailTrace_900021 : CollatzResearch.WordTrace tailWord_900021 prefixEnd_900021 410794108569180797687453 := by
  unfold tailWord_900021
  simp only [CollatzResearch.WordTrace]
  refine ⟨32826462672385103194323917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21884308448256735462882611 32826462672385103194323917)
  ·
    refine ⟨12309923502144413697871469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32826462672385103194323917 12309923502144413697871469)
    ·
      refine ⟨4616221313304155136701801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12309923502144413697871469 4616221313304155136701801)
      ·
        refine ⟨3462165984978116352526351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4616221313304155136701801 3462165984978116352526351)
        ·
          refine ⟨5193248977467174528789527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462165984978116352526351 5193248977467174528789527)
          ·
            refine ⟨7789873466200761793184291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5193248977467174528789527 7789873466200761793184291)
            ·
              refine ⟨11684810199301142689776437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7789873466200761793184291 11684810199301142689776437)
              ·
                refine ⟨1095450956184482127166541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11684810199301142689776437 1095450956184482127166541)
                ·
                  refine ⟨410794108569180797687453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095450956184482127166541 410794108569180797687453)
                  ·
                    rfl

theorem cell20_900021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_900021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900021 prefixEnd_900021 := by exact prefixLift 900021
  have htrace : WordTrace (prefixWord ++ tailWord_900021) baseStart_900021 baseEnd_900021 := by
    simpa [prefixWord, tailWord_900021, baseEnd_900021] using wordTrace_append hprefix tailTrace_900021
  have hstable : (prefixWord ++ tailWord_900021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900021).length < 2 ^ (prefixWord ++ tailWord_900021).sum := by decide
  have hdescent : baseEnd_900021 < baseStart_900021 := by decide
  rcases family_descends (prefixWord ++ tailWord_900021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900042 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_900042 : Nat := 118140960795 + 900042 * 2 ^ 59
def prefixEnd_900042 : Nat := 4983230072969 + 3 ^ 40 * 900042 * 2
def baseEnd_900042 : Nat := 410803693541398057987367

theorem tailTrace_900042 : CollatzResearch.WordTrace tailWord_900042 prefixEnd_900042 410803693541398057987367 := by
  unfold tailWord_900042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206807151327255945209595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21884819070206015853892253 8206807151327255945209595)
  ·
    refine ⟨12310210726990883917814393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8206807151327255945209595 12310210726990883917814393)
    ·
      refine ⟨9232658045243162938360795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12310210726990883917814393 9232658045243162938360795)
      ·
        refine ⟨13848987067864744407541193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9232658045243162938360795 13848987067864744407541193)
        ·
          refine ⟨10386740300898558305655895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13848987067864744407541193 10386740300898558305655895)
          ·
            refine ⟨15580110451347837458483843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10386740300898558305655895 15580110451347837458483843)
            ·
              refine ⟨23370165677021756187725765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15580110451347837458483843 23370165677021756187725765)
              ·
                refine ⟨4381906064441579285198581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23370165677021756187725765 4381906064441579285198581)
                ·
                  refine ⟨410803693541398057987367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4381906064441579285198581 410803693541398057987367)
                  ·
                    rfl

theorem cell20_900042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_900042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900042 prefixEnd_900042 := by exact prefixLift 900042
  have htrace : WordTrace (prefixWord ++ tailWord_900042) baseStart_900042 baseEnd_900042 := by
    simpa [prefixWord, tailWord_900042, baseEnd_900042] using wordTrace_append hprefix tailTrace_900042
  have hstable : (prefixWord ++ tailWord_900042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900042).length < 2 ^ (prefixWord ++ tailWord_900042).sum := by decide
  have hdescent : baseEnd_900042 < baseStart_900042 := by decide
  rcases family_descends (prefixWord ++ tailWord_900042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900049 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_900049 : Nat := 118140960795 + 900049 * 2 ^ 59
def prefixEnd_900049 : Nat := 4983230072969 + 3 ^ 40 * 900049 * 2
def baseEnd_900049 : Nat := 410806888532137144754005

theorem tailTrace_900049 : CollatzResearch.WordTrace tailWord_900049 prefixEnd_900049 410806888532137144754005 := by
  unfold tailWord_900049
  simp only [CollatzResearch.WordTrace]
  refine ⟨32827483916283663976343201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21884989277522442650895467 32827483916283663976343201)
  ·
    refine ⟨24620612937212747982257401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32827483916283663976343201 24620612937212747982257401)
    ·
      refine ⟨18465459702909560986693051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24620612937212747982257401 18465459702909560986693051)
      ·
        refine ⟨27698189554364341480039577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18465459702909560986693051 27698189554364341480039577)
        ·
          refine ⟨20773642165773256110029683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27698189554364341480039577 20773642165773256110029683)
          ·
            refine ⟨31160463248659884165044525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20773642165773256110029683 31160463248659884165044525)
            ·
              refine ⟨11685173718247456561891697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31160463248659884165044525 11685173718247456561891697)
              ·
                refine ⟨8763880288685592421418773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11685173718247456561891697 8763880288685592421418773)
                ·
                  refine ⟨410806888532137144754005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8763880288685592421418773 410806888532137144754005)
                  ·
                    rfl

theorem cell20_900049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_900049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900049 prefixEnd_900049 := by exact prefixLift 900049
  have htrace : WordTrace (prefixWord ++ tailWord_900049) baseStart_900049 baseEnd_900049 := by
    simpa [prefixWord, tailWord_900049, baseEnd_900049] using wordTrace_append hprefix tailTrace_900049
  have hstable : (prefixWord ++ tailWord_900049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900049).length < 2 ^ (prefixWord ++ tailWord_900049).sum := by decide
  have hdescent : baseEnd_900049 < baseStart_900049 := by decide
  rcases family_descends (prefixWord ++ tailWord_900049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900142 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_900142 : Nat := 118140960795 + 900142 * 2 ^ 59
def prefixEnd_900142 : Nat := 4983230072969 + 3 ^ 40 * 900142 * 2
def baseEnd_900142 : Nat := 410849336266242154653625

theorem tailTrace_900142 : CollatzResearch.WordTrace tailWord_900142 prefixEnd_900142 410849336266242154653625 := by
  unfold tailWord_900142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4103859488118342607434835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21887250603297827239652453 4103859488118342607434835)
  ·
    refine ⟨6155789232177513911152253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4103859488118342607434835 6155789232177513911152253)
    ·
      refine ⟨2308420962066567716682095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6155789232177513911152253 2308420962066567716682095)
      ·
        refine ⟨3462631443099851575023143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308420962066567716682095 3462631443099851575023143)
        ·
          refine ⟨5193947164649777362534715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462631443099851575023143 5193947164649777362534715)
          ·
            refine ⟨7790920746974666043802073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5193947164649777362534715 7790920746974666043802073)
            ·
              refine ⟨5843190560230999532851555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7790920746974666043802073 5843190560230999532851555)
              ·
                refine ⟨8764785840346499299277333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5843190560230999532851555 8764785840346499299277333)
                ·
                  refine ⟨410849336266242154653625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8764785840346499299277333 410849336266242154653625)
                  ·
                    rfl

theorem cell20_900142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_900142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900142 prefixEnd_900142 := by exact prefixLift 900142
  have htrace : WordTrace (prefixWord ++ tailWord_900142) baseStart_900142 baseEnd_900142 := by
    simpa [prefixWord, tailWord_900142, baseEnd_900142] using wordTrace_append hprefix tailTrace_900142
  have hstable : (prefixWord ++ tailWord_900142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900142).length < 2 ^ (prefixWord ++ tailWord_900142).sum := by decide
  have hdescent : baseEnd_900142 < baseStart_900142 := by decide
  rcases family_descends (prefixWord ++ tailWord_900142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900166 : List Nat := [6, 1, 1, 1, 1, 10]
def baseStart_900166 : Nat := 118140960795 + 900166 * 2 ^ 59
def prefixEnd_900166 : Nat := 4983230072969 + 3 ^ 40 * 900166 * 2
def baseEnd_900166 : Nat := 15217047797044619920501

theorem tailTrace_900166 : CollatzResearch.WordTrace tailWord_900166 prefixEnd_900166 15217047797044619920501 := by
  unfold tailWord_900166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025992226776868529948511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21887834171239861972234901 1025992226776868529948511)
  ·
    refine ⟨1538988340165302794922767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1025992226776868529948511 1538988340165302794922767)
    ·
      refine ⟨2308482510247954192384151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538988340165302794922767 2308482510247954192384151)
      ·
        refine ⟨3462723765371931288576227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308482510247954192384151 3462723765371931288576227)
        ·
          refine ⟨5194085648057896932864341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462723765371931288576227 5194085648057896932864341)
          ·
            refine ⟨15217047797044619920501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5194085648057896932864341 15217047797044619920501)
            ·
              rfl

theorem cell20_900166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 10].length) (baseStart_900166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900166 prefixEnd_900166 := by exact prefixLift 900166
  have htrace : WordTrace (prefixWord ++ tailWord_900166) baseStart_900166 baseEnd_900166 := by
    simpa [prefixWord, tailWord_900166, baseEnd_900166] using wordTrace_append hprefix tailTrace_900166
  have hstable : (prefixWord ++ tailWord_900166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900166).length < 2 ^ (prefixWord ++ tailWord_900166).sum := by decide
  have hdescent : baseEnd_900166 < baseStart_900166 := by decide
  rcases family_descends (prefixWord ++ tailWord_900166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900201 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_900201 : Nat := 118140960795 + 900201 * 2 ^ 59
def prefixEnd_900201 : Nat := 4983230072969 + 3 ^ 40 * 900201 * 2
def baseEnd_900201 : Nat := 410876265473900171686717

theorem tailTrace_900201 : CollatzResearch.WordTrace tailWord_900201 prefixEnd_900201 410876265473900171686717 := by
  unfold tailWord_900201
  simp only [CollatzResearch.WordTrace]
  refine ⟨32833027811732993935876457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21888685207821995957250971 32833027811732993935876457)
  ·
    refine ⟨24624770858799745451907343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32833027811732993935876457 24624770858799745451907343)
    ·
      refine ⟨36937156288199618177861015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24624770858799745451907343 36937156288199618177861015)
      ·
        refine ⟨55405734432299427266791523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36937156288199618177861015 55405734432299427266791523)
        ·
          refine ⟨83108601648449140900187285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55405734432299427266791523 83108601648449140900187285)
          ·
            refine ⟨3895715702271053479696279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83108601648449140900187285 3895715702271053479696279)
            ·
              refine ⟨5843573553406580219544419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3895715702271053479696279 5843573553406580219544419)
              ·
                refine ⟨8765360330109870329316629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5843573553406580219544419 8765360330109870329316629)
                ·
                  refine ⟨410876265473900171686717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8765360330109870329316629 410876265473900171686717)
                  ·
                    rfl

theorem cell20_900201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_900201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900201 prefixEnd_900201 := by exact prefixLift 900201
  have htrace : WordTrace (prefixWord ++ tailWord_900201) baseStart_900201 baseEnd_900201 := by
    simpa [prefixWord, tailWord_900201, baseEnd_900201] using wordTrace_append hprefix tailTrace_900201
  have hstable : (prefixWord ++ tailWord_900201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900201).length < 2 ^ (prefixWord ++ tailWord_900201).sum := by decide
  have hdescent : baseEnd_900201 < baseStart_900201 := by decide
  rcases family_descends (prefixWord ++ tailWord_900201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900214 : List Nat := [5, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_900214 : Nat := 118140960795 + 900214 * 2 ^ 59
def prefixEnd_900214 : Nat := 4983230072969 + 3 ^ 40 * 900214 * 2
def baseEnd_900214 : Nat := 410882199028129904253331

theorem tailTrace_900214 : CollatzResearch.WordTrace tailWord_900214 prefixEnd_900214 410882199028129904253331 := by
  unfold tailWord_900214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2052093872542868572256231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21889001307123931437399797 2052093872542868572256231)
  ·
    refine ⟨3078140808814302858384347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2052093872542868572256231 3078140808814302858384347)
    ·
      refine ⟨4617211213221454287576521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3078140808814302858384347 4617211213221454287576521)
      ·
        refine ⟨3462908409916090715682391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4617211213221454287576521 3462908409916090715682391)
        ·
          refine ⟨5194362614874136073523587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462908409916090715682391 5194362614874136073523587)
          ·
            refine ⟨7791543922311204110285381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194362614874136073523587 7791543922311204110285381)
            ·
              refine ⟨1460914485433350770678509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7791543922311204110285381 1460914485433350770678509)
              ·
                refine ⟨547842932037506539004441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1460914485433350770678509 547842932037506539004441)
                ·
                  refine ⟨410882199028129904253331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547842932037506539004441 410882199028129904253331)
                  ·
                    rfl

theorem cell20_900214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_900214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900214 prefixEnd_900214 := by exact prefixLift 900214
  have htrace : WordTrace (prefixWord ++ tailWord_900214) baseStart_900214 baseEnd_900214 := by
    simpa [prefixWord, tailWord_900214, baseEnd_900214] using wordTrace_append hprefix tailTrace_900214
  have hstable : (prefixWord ++ tailWord_900214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900214).length < 2 ^ (prefixWord ++ tailWord_900214).sum := by decide
  have hdescent : baseEnd_900214 < baseStart_900214 := by decide
  rcases family_descends (prefixWord ++ tailWord_900214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900225 : List Nat := [1, 2, 4, 2, 2, 2, 7]
def baseStart_900225 : Nat := 118140960795 + 900225 * 2 ^ 59
def prefixEnd_900225 : Nat := 4983230072969 + 3 ^ 40 * 900225 * 2
def baseEnd_900225 : Nat := 45654135525318083876291

theorem tailTrace_900225 : CollatzResearch.WordTrace tailWord_900225 prefixEnd_900225 45654135525318083876291 := by
  unfold tailWord_900225
  simp only [CollatzResearch.WordTrace]
  refine ⟨32833903163646046034750129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21889268775764030689833419 32833903163646046034750129)
  ·
    refine ⟨24625427372734534526062597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32833903163646046034750129 24625427372734534526062597)
    ·
      refine ⟨4617267632387725223636737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24625427372734534526062597 4617267632387725223636737)
      ·
        refine ⟨3462950724290793917727553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4617267632387725223636737 3462950724290793917727553)
        ·
          refine ⟨2597213043218095438295665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3462950724290793917727553 2597213043218095438295665)
          ·
            refine ⟨1947909782413571578721749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2597213043218095438295665 1947909782413571578721749)
            ·
              refine ⟨45654135525318083876291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1947909782413571578721749 45654135525318083876291)
              ·
                rfl

theorem cell20_900225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 7].length) (baseStart_900225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900225 prefixEnd_900225 := by exact prefixLift 900225
  have htrace : WordTrace (prefixWord ++ tailWord_900225) baseStart_900225 baseEnd_900225 := by
    simpa [prefixWord, tailWord_900225, baseEnd_900225] using wordTrace_append hprefix tailTrace_900225
  have hstable : (prefixWord ++ tailWord_900225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900225).length < 2 ^ (prefixWord ++ tailWord_900225).sum := by decide
  have hdescent : baseEnd_900225 < baseStart_900225 := by decide
  rcases family_descends (prefixWord ++ tailWord_900225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900228 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 3]
def baseStart_900228 : Nat := 118140960795 + 900228 * 2 ^ 59
def prefixEnd_900228 : Nat := 4983230072969 + 3 ^ 40 * 900228 * 2
def baseEnd_900228 : Nat := 410888589009608077786607

theorem tailTrace_900228 : CollatzResearch.WordTrace tailWord_900228 prefixEnd_900228 410888589009608077786607 := by
  unfold tailWord_900228
  simp only [CollatzResearch.WordTrace]
  refine ⟨16417006291317588773554669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21889341721756785031406225 16417006291317588773554669)
  ·
    refine ⟨6156377359244095790083001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16417006291317588773554669 6156377359244095790083001)
    ·
      refine ⟨4617283019433071842562251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6156377359244095790083001 4617283019433071842562251)
      ·
        refine ⟨6925924529149607763843377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4617283019433071842562251 6925924529149607763843377)
        ·
          refine ⟨5194443396862205822882533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6925924529149607763843377 5194443396862205822882533)
          ·
            refine ⟨973958136911663591790475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5194443396862205822882533 973958136911663591790475)
            ·
              refine ⟨1460937205367495387685713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973958136911663591790475 1460937205367495387685713)
              ·
                refine ⟨1095702904025621540764285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460937205367495387685713 1095702904025621540764285)
                ·
                  refine ⟨410888589009608077786607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095702904025621540764285 410888589009608077786607)
                  ·
                    rfl

theorem cell20_900228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_900228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900228 prefixEnd_900228 := by exact prefixLift 900228
  have htrace : WordTrace (prefixWord ++ tailWord_900228) baseStart_900228 baseEnd_900228 := by
    simpa [prefixWord, tailWord_900228, baseEnd_900228] using wordTrace_append hprefix tailTrace_900228
  have hstable : (prefixWord ++ tailWord_900228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900228).length < 2 ^ (prefixWord ++ tailWord_900228).sum := by decide
  have hdescent : baseEnd_900228 < baseStart_900228 := by decide
  rcases family_descends (prefixWord ++ tailWord_900228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900269 : List Nat := [1, 5, 2, 1, 3, 2, 1, 3, 2]
def baseStart_900269 : Nat := 118140960795 + 900269 * 2 ^ 59
def prefixEnd_900269 : Nat := 4983230072969 + 3 ^ 40 * 900269 * 2
def baseEnd_900269 : Nat := 410907302526794157419773

theorem tailTrace_900269 : CollatzResearch.WordTrace tailWord_900269 prefixEnd_900269 410907302526794157419773 := by
  unfold tailWord_900269
  simp only [CollatzResearch.WordTrace]
  refine ⟨32835507975486641549351861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21890338650324427699567907 32835507975486641549351861)
  ·
    refine ⟨3078328872701872645251737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32835507975486641549351861 3078328872701872645251737)
    ·
      refine ⟨2308746654526404483938803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3078328872701872645251737 2308746654526404483938803)
      ·
        refine ⟨3463119981789606725908205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308746654526404483938803 3463119981789606725908205)
        ·
          refine ⟨1298669993171102522215577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3463119981789606725908205 1298669993171102522215577)
          ·
            refine ⟨974002494878326891661683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1298669993171102522215577 974002494878326891661683)
            ·
              refine ⟨1461003742317490337492525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974002494878326891661683 1461003742317490337492525)
              ·
                refine ⟨547876403369058876559697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1461003742317490337492525 547876403369058876559697)
                ·
                  refine ⟨410907302526794157419773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547876403369058876559697 410907302526794157419773)
                  ·
                    rfl

theorem cell20_900269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_900269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900269 prefixEnd_900269 := by exact prefixLift 900269
  have htrace : WordTrace (prefixWord ++ tailWord_900269) baseStart_900269 baseEnd_900269 := by
    simpa [prefixWord, tailWord_900269, baseEnd_900269] using wordTrace_append hprefix tailTrace_900269
  have hstable : (prefixWord ++ tailWord_900269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900269).length < 2 ^ (prefixWord ++ tailWord_900269).sum := by decide
  have hdescent : baseEnd_900269 < baseStart_900269 := by decide
  rcases family_descends (prefixWord ++ tailWord_900269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900356 : List Nat := [2, 3, 2, 2, 2, 3, 1, 5]
def baseStart_900356 : Nat := 118140960795 + 900356 * 2 ^ 59
def prefixEnd_900356 : Nat := 4983230072969 + 3 ^ 40 * 900356 * 2
def baseEnd_900356 : Nat := 136982337232469507173139

theorem tailTrace_900356 : CollatzResearch.WordTrace tailWord_900356 prefixEnd_900356 136982337232469507173139 := by
  unfold tailWord_900356
  simp only [CollatzResearch.WordTrace]
  refine ⟨16419340563085727703884461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21892454084114303605179281 16419340563085727703884461)
  ·
    refine ⟨6157252711157147888956673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16419340563085727703884461 6157252711157147888956673)
    ·
      refine ⟨4617939533367860916717505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6157252711157147888956673 4617939533367860916717505)
      ·
        refine ⟨3463454650025895687538129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4617939533367860916717505 3463454650025895687538129)
        ·
          refine ⟨2597590987519421765653597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3463454650025895687538129 2597590987519421765653597)
          ·
            refine ⟨974096620319783162120099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2597590987519421765653597 974096620319783162120099)
            ·
              refine ⟨1461144930479674743180149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974096620319783162120099 1461144930479674743180149)
              ·
                refine ⟨136982337232469507173139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1461144930479674743180149 136982337232469507173139)
                ·
                  rfl

theorem cell20_900356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_900356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900356 prefixEnd_900356 := by exact prefixLift 900356
  have htrace : WordTrace (prefixWord ++ tailWord_900356) baseStart_900356 baseEnd_900356 := by
    simpa [prefixWord, tailWord_900356, baseEnd_900356] using wordTrace_append hprefix tailTrace_900356
  have hstable : (prefixWord ++ tailWord_900356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900356).length < 2 ^ (prefixWord ++ tailWord_900356).sum := by decide
  have hdescent : baseEnd_900356 < baseStart_900356 := by decide
  rcases family_descends (prefixWord ++ tailWord_900356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900367 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_900367 : Nat := 118140960795 + 900367 * 2 ^ 59
def prefixEnd_900367 : Nat := 4983230072969 + 3 ^ 40 * 900367 * 2
def baseEnd_900367 : Nat := 410952032397141372152705

theorem tailTrace_900367 : CollatzResearch.WordTrace tailWord_900367 prefixEnd_900367 410952032397141372152705 := by
  unfold tailWord_900367
  simp only [CollatzResearch.WordTrace]
  refine ⟨32839082329131604286419355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21892721552754402857612903 32839082329131604286419355)
  ·
    refine ⟨49258623493697406429629033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32839082329131604286419355 49258623493697406429629033)
    ·
      refine ⟨36943967620273054822221775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49258623493697406429629033 36943967620273054822221775)
      ·
        refine ⟨55415951430409582233332663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36943967620273054822221775 55415951430409582233332663)
        ·
          refine ⟨83123927145614373349998995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55415951430409582233332663 83123927145614373349998995)
          ·
            refine ⟨124685890718421560024998493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83123927145614373349998995 124685890718421560024998493)
            ·
              refine ⟨46757209019408085009374435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124685890718421560024998493 46757209019408085009374435)
              ·
                refine ⟨70135813529112127514061653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46757209019408085009374435 70135813529112127514061653)
                ·
                  refine ⟨410952032397141372152705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70135813529112127514061653 410952032397141372152705)
                  ·
                    rfl

theorem cell20_900367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_900367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900367 prefixEnd_900367 := by exact prefixLift 900367
  have htrace : WordTrace (prefixWord ++ tailWord_900367) baseStart_900367 baseEnd_900367 := by
    simpa [prefixWord, tailWord_900367, baseEnd_900367] using wordTrace_append hprefix tailTrace_900367
  have hstable : (prefixWord ++ tailWord_900367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900367).length < 2 ^ (prefixWord ++ tailWord_900367).sum := by decide
  have hdescent : baseEnd_900367 < baseStart_900367 := by decide
  rcases family_descends (prefixWord ++ tailWord_900367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900387 : List Nat := [1, 1, 1, 4, 2, 4, 2, 3, 2]
def baseStart_900387 : Nat := 118140960795 + 900387 * 2 ^ 59
def prefixEnd_900387 : Nat := 4983230072969 + 3 ^ 40 * 900387 * 2
def baseEnd_900387 : Nat := 410961160942110191485957

theorem tailTrace_900387 : CollatzResearch.WordTrace tailWord_900387 prefixEnd_900387 410961160942110191485957 := by
  unfold tailWord_900387
  simp only [CollatzResearch.WordTrace]
  refine ⟨32839811789059147702147415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21893207859372765134764943 32839811789059147702147415)
  ·
    refine ⟨49259717683588721553221123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32839811789059147702147415 49259717683588721553221123)
    ·
      refine ⟨73889576525383082329831685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49259717683588721553221123 73889576525383082329831685)
      ·
        refine ⟨13854295598509327936843441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73889576525383082329831685 13854295598509327936843441)
        ·
          refine ⟨10390721698881995952632581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13854295598509327936843441 10390721698881995952632581)
          ·
            refine ⟨1948260318540374241118609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10390721698881995952632581 1948260318540374241118609)
            ·
              refine ⟨1461195238905280680838957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1948260318540374241118609 1461195238905280680838957)
              ·
                refine ⟨547948214589480255314609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1461195238905280680838957 547948214589480255314609)
                ·
                  refine ⟨410961160942110191485957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547948214589480255314609 410961160942110191485957)
                  ·
                    rfl

theorem cell20_900387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 2].length) (baseStart_900387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900387 prefixEnd_900387 := by exact prefixLift 900387
  have htrace : WordTrace (prefixWord ++ tailWord_900387) baseStart_900387 baseEnd_900387 := by
    simpa [prefixWord, tailWord_900387, baseEnd_900387] using wordTrace_append hprefix tailTrace_900387
  have hstable : (prefixWord ++ tailWord_900387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900387).length < 2 ^ (prefixWord ++ tailWord_900387).sum := by decide
  have hdescent : baseEnd_900387 < baseStart_900387 := by decide
  rcases family_descends (prefixWord ++ tailWord_900387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900397 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 3]
def baseStart_900397 : Nat := 118140960795 + 900397 * 2 ^ 59
def prefixEnd_900397 : Nat := 4983230072969 + 3 ^ 40 * 900397 * 2
def baseEnd_900397 : Nat := 410965725214594601152583

theorem tailTrace_900397 : CollatzResearch.WordTrace tailWord_900397 prefixEnd_900397 410965725214594601152583 := by
  unfold tailWord_900397
  simp only [CollatzResearch.WordTrace]
  refine ⟨32840176519022919410011445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21893451012681946273340963 32840176519022919410011445)
  ·
    refine ⟨3078766548658398694688573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32840176519022919410011445 3078766548658398694688573)
    ·
      refine ⟨1154537455746899510508215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3078766548658398694688573 1154537455746899510508215)
      ·
        refine ⟨1731806183620349265762323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154537455746899510508215 1731806183620349265762323)
        ·
          refine ⟨2597709275430523898643485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731806183620349265762323 2597709275430523898643485)
          ·
            refine ⟨974140978286446461991307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2597709275430523898643485 974140978286446461991307)
            ·
              refine ⟨1461211467429669692986961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974140978286446461991307 1461211467429669692986961)
              ·
                refine ⟨1095908600572252269740221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461211467429669692986961 1095908600572252269740221)
                ·
                  refine ⟨410965725214594601152583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095908600572252269740221 410965725214594601152583)
                  ·
                    rfl

theorem cell20_900397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_900397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900397 prefixEnd_900397 := by exact prefixLift 900397
  have htrace : WordTrace (prefixWord ++ tailWord_900397) baseStart_900397 baseEnd_900397 := by
    simpa [prefixWord, tailWord_900397, baseEnd_900397] using wordTrace_append hprefix tailTrace_900397
  have hstable : (prefixWord ++ tailWord_900397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900397).length < 2 ^ (prefixWord ++ tailWord_900397).sum := by decide
  have hdescent : baseEnd_900397 < baseStart_900397 := by decide
  rcases family_descends (prefixWord ++ tailWord_900397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900401 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 3]
def baseStart_900401 : Nat := 118140960795 + 900401 * 2 ^ 59
def prefixEnd_900401 : Nat := 4983230072969 + 3 ^ 40 * 900401 * 2
def baseEnd_900401 : Nat := 410967550923588365019233

theorem tailTrace_900401 : CollatzResearch.WordTrace tailWord_900401 prefixEnd_900401 410967550923588365019233 := by
  unfold tailWord_900401
  simp only [CollatzResearch.WordTrace]
  refine ⟨32840322411008428093157057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21893548274005618728771371 32840322411008428093157057)
  ·
    refine ⟨24630241808256321069867793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32840322411008428093157057 24630241808256321069867793)
    ·
      refine ⟨18472681356192240802400845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24630241808256321069867793 18472681356192240802400845)
      ·
        refine ⟨6927255508572090300900317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18472681356192240802400845 6927255508572090300900317)
        ·
          refine ⟨2597720815714533862837619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6927255508572090300900317 2597720815714533862837619)
          ·
            refine ⟨3896581223571800794256429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597720815714533862837619 3896581223571800794256429)
            ·
              refine ⟨1461217958839425297846161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3896581223571800794256429 1461217958839425297846161)
              ·
                refine ⟨1095913469129568973384621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461217958839425297846161 1095913469129568973384621)
                ·
                  refine ⟨410967550923588365019233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095913469129568973384621 410967550923588365019233)
                  ·
                    rfl

theorem cell20_900401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_900401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900401 prefixEnd_900401 := by exact prefixLift 900401
  have htrace : WordTrace (prefixWord ++ tailWord_900401) baseStart_900401 baseEnd_900401 := by
    simpa [prefixWord, tailWord_900401, baseEnd_900401] using wordTrace_append hprefix tailTrace_900401
  have hstable : (prefixWord ++ tailWord_900401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900401).length < 2 ^ (prefixWord ++ tailWord_900401).sum := by decide
  have hdescent : baseEnd_900401 < baseStart_900401 := by decide
  rcases family_descends (prefixWord ++ tailWord_900401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900460 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_900460 : Nat := 118140960795 + 900460 * 2 ^ 59
def prefixEnd_900460 : Nat := 4983230072969 + 3 ^ 40 * 900460 * 2
def baseEnd_900460 : Nat := 410994480131246382052325

theorem tailTrace_900460 : CollatzResearch.WordTrace tailWord_900460 prefixEnd_900460 410994480131246382052325 := by
  unfold tailWord_900460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16421237158897340584777417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21894982878529787446369889 16421237158897340584777417)
  ·
    refine ⟨12315927869173005438583063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16421237158897340584777417 12315927869173005438583063)
    ·
      refine ⟨18473891803759508157874595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12315927869173005438583063 18473891803759508157874595)
      ·
        refine ⟨27710837705639262236811893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18473891803759508157874595 27710837705639262236811893)
        ·
          refine ⟨2597891034903680834701115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27710837705639262236811893 2597891034903680834701115)
          ·
            refine ⟨3896836552355521252051673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597891034903680834701115 3896836552355521252051673)
            ·
              refine ⟨2922627414266640939038755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3896836552355521252051673 2922627414266640939038755)
              ·
                refine ⟨4383941121399961408558133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922627414266640939038755 4383941121399961408558133)
                ·
                  refine ⟨410994480131246382052325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4383941121399961408558133 410994480131246382052325)
                  ·
                    rfl

theorem cell20_900460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_900460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900460 prefixEnd_900460 := by exact prefixLift 900460
  have htrace : WordTrace (prefixWord ++ tailWord_900460) baseStart_900460 baseEnd_900460 := by
    simpa [prefixWord, tailWord_900460, baseEnd_900460] using wordTrace_append hprefix tailTrace_900460
  have hstable : (prefixWord ++ tailWord_900460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900460).length < 2 ^ (prefixWord ++ tailWord_900460).sum := by decide
  have hdescent : baseEnd_900460 < baseStart_900460 := by decide
  rcases family_descends (prefixWord ++ tailWord_900460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900463 : List Nat := [1, 1, 2, 1, 3, 1, 7, 2, 2]
def baseStart_900463 : Nat := 118140960795 + 900463 * 2 ^ 59
def prefixEnd_900463 : Nat := 4983230072969 + 3 ^ 40 * 900463 * 2
def baseEnd_900463 : Nat := 410995849412991704952313

theorem tailTrace_900463 : CollatzResearch.WordTrace tailWord_900463 prefixEnd_900463 410995849412991704952313 := by
  unfold tailWord_900463
  simp only [CollatzResearch.WordTrace]
  refine ⟨32842583736783812681914043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21895055824522541787942695 32842583736783812681914043)
  ·
    refine ⟨49263875605175719022871065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32842583736783812681914043 49263875605175719022871065)
    ·
      refine ⟨36947906703881789267153299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49263875605175719022871065 36947906703881789267153299)
      ·
        refine ⟨55421860055822683900729949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36947906703881789267153299 55421860055822683900729949)
        ·
          refine ⟨20783197520933506462773731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55421860055822683900729949 20783197520933506462773731)
          ·
            refine ⟨31174796281400259694160597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20783197520933506462773731 31174796281400259694160597)
            ·
              refine ⟨730659287845318586581889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31174796281400259694160597 730659287845318586581889)
              ·
                refine ⟨547994465883988939936417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730659287845318586581889 547994465883988939936417)
                ·
                  refine ⟨410995849412991704952313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547994465883988939936417 410995849412991704952313)
                  ·
                    rfl

theorem cell20_900463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 2].length) (baseStart_900463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900463 prefixEnd_900463 := by exact prefixLift 900463
  have htrace : WordTrace (prefixWord ++ tailWord_900463) baseStart_900463 baseEnd_900463 := by
    simpa [prefixWord, tailWord_900463, baseEnd_900463] using wordTrace_append hprefix tailTrace_900463
  have hstable : (prefixWord ++ tailWord_900463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900463).length < 2 ^ (prefixWord ++ tailWord_900463).sum := by decide
  have hdescent : baseEnd_900463 < baseStart_900463 := by decide
  rcases family_descends (prefixWord ++ tailWord_900463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900508 : List Nat := [2, 2, 3, 4, 2, 7]
def baseStart_900508 : Nat := 118140960795 + 900508 * 2 ^ 59
def prefixEnd_900508 : Nat := 4983230072969 + 3 ^ 40 * 900508 * 2
def baseEnd_900508 : Nat := 15222829208858205498227

theorem tailTrace_900508 : CollatzResearch.WordTrace tailWord_900508 prefixEnd_900508 15222829208858205498227 := by
  unfold tailWord_900508
  simp only [CollatzResearch.WordTrace]
  refine ⟨16422112510810392683651089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21896150014413856911534785 16422112510810392683651089)
  ·
    refine ⟨12316584383107794512738317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16422112510810392683651089 12316584383107794512738317)
    ·
      refine ⟨4618719143665422942276869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12316584383107794512738317 4618719143665422942276869)
      ·
        refine ⟨866009839437266801676913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4618719143665422942276869 866009839437266801676913)
        ·
          refine ⟨649507379577950101257685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866009839437266801676913 649507379577950101257685)
          ·
            refine ⟨15222829208858205498227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 649507379577950101257685 15222829208858205498227)
            ·
              rfl

theorem cell20_900508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 7].length) (baseStart_900508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900508 prefixEnd_900508 := by exact prefixLift 900508
  have htrace : WordTrace (prefixWord ++ tailWord_900508) baseStart_900508 baseEnd_900508 := by
    simpa [prefixWord, tailWord_900508, baseEnd_900508] using wordTrace_append hprefix tailTrace_900508
  have hstable : (prefixWord ++ tailWord_900508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900508).length < 2 ^ (prefixWord ++ tailWord_900508).sum := by decide
  have hdescent : baseEnd_900508 < baseStart_900508 := by decide
  rcases family_descends (prefixWord ++ tailWord_900508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900536 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 3]
def baseStart_900536 : Nat := 118140960795 + 900536 * 2 ^ 59
def prefixEnd_900536 : Nat := 4983230072969 + 3 ^ 40 * 900536 * 2
def baseEnd_900536 : Nat := 411029168602127895518681

theorem tailTrace_900536 : CollatzResearch.WordTrace tailWord_900536 prefixEnd_900536 411029168602127895518681 := by
  unfold tailWord_900536
  simp only [CollatzResearch.WordTrace]
  refine ⟨16422623132759673074660731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21896830843679564099547641 16422623132759673074660731)
  ·
    refine ⟨24633934699139509611991097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16422623132759673074660731 24633934699139509611991097)
    ·
      refine ⟨18475451024354632208993323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24633934699139509611991097 18475451024354632208993323)
      ·
        refine ⟨27713176536531948313489985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18475451024354632208993323 27713176536531948313489985)
        ·
          refine ⟨20784882402398961235117489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27713176536531948313489985 20784882402398961235117489)
          ·
            refine ⟨15588661801799220926338117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20784882402398961235117489 15588661801799220926338117)
            ·
              refine ⟨2922874087837353923688397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15588661801799220926338117 2922874087837353923688397)
              ·
                refine ⟨1096077782939007721383149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2922874087837353923688397 1096077782939007721383149)
                ·
                  refine ⟨411029168602127895518681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096077782939007721383149 411029168602127895518681)
                  ·
                    rfl

theorem cell20_900536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_900536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900536 prefixEnd_900536 := by exact prefixLift 900536
  have htrace : WordTrace (prefixWord ++ tailWord_900536) baseStart_900536 baseEnd_900536 := by
    simpa [prefixWord, tailWord_900536, baseEnd_900536] using wordTrace_append hprefix tailTrace_900536
  have hstable : (prefixWord ++ tailWord_900536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900536).length < 2 ^ (prefixWord ++ tailWord_900536).sum := by decide
  have hdescent : baseEnd_900536 < baseStart_900536 := by decide
  rcases family_descends (prefixWord ++ tailWord_900536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900598 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_900598 : Nat := 118140960795 + 900598 * 2 ^ 59
def prefixEnd_900598 : Nat := 4983230072969 + 3 ^ 40 * 900598 * 2
def baseEnd_900598 : Nat := 411057467091531235451761

theorem tailTrace_900598 : CollatzResearch.WordTrace tailWord_900598 prefixEnd_900598 411057467091531235451761 := by
  unfold tailWord_900598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2052969224455920671129903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21898338394196487158718965 2052969224455920671129903)
  ·
    refine ⟨3079453836683881006694855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2052969224455920671129903 3079453836683881006694855)
    ·
      refine ⟨4619180755025821510042283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3079453836683881006694855 4619180755025821510042283)
      ·
        refine ⟨6928771132538732265063425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4619180755025821510042283 6928771132538732265063425)
        ·
          refine ⟨5196578349404049198797569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6928771132538732265063425 5196578349404049198797569)
          ·
            refine ⟨3897433762053036899098177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5196578349404049198797569 3897433762053036899098177)
            ·
              refine ⟨2923075321539777674323633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897433762053036899098177 2923075321539777674323633)
              ·
                refine ⟨2192306491154833255742725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923075321539777674323633 2192306491154833255742725)
                ·
                  refine ⟨411057467091531235451761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2192306491154833255742725 411057467091531235451761)
                  ·
                    rfl

theorem cell20_900598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_900598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900598 prefixEnd_900598 := by exact prefixLift 900598
  have htrace : WordTrace (prefixWord ++ tailWord_900598) baseStart_900598 baseEnd_900598 := by
    simpa [prefixWord, tailWord_900598, baseEnd_900598] using wordTrace_append hprefix tailTrace_900598
  have hstable : (prefixWord ++ tailWord_900598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900598).length < 2 ^ (prefixWord ++ tailWord_900598).sum := by decide
  have hdescent : baseEnd_900598 < baseStart_900598 := by decide
  rcases family_descends (prefixWord ++ tailWord_900598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900605 : List Nat := [1, 4, 1, 1, 1, 4, 4, 4]
def baseStart_900605 : Nat := 118140960795 + 900605 * 2 ^ 59
def prefixEnd_900605 : Nat := 4983230072969 + 3 ^ 40 * 900605 * 2
def baseEnd_900605 : Nat := 137020220694090107406133

theorem tailTrace_900605 : CollatzResearch.WordTrace tailWord_900605 prefixEnd_900605 137020220694090107406133 := by
  unfold tailWord_900605
  simp only [CollatzResearch.WordTrace]
  refine ⟨32847762902269370933583269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21898508601512913955722179 32847762902269370933583269)
  ·
    refine ⟨6158955544175507050046863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32847762902269370933583269 6158955544175507050046863)
    ·
      refine ⟨9238433316263260575070295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158955544175507050046863 9238433316263260575070295)
      ·
        refine ⟨13857649974394890862605443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9238433316263260575070295 13857649974394890862605443)
        ·
          refine ⟨20786474961592336293908165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13857649974394890862605443 20786474961592336293908165)
          ·
            refine ⟨3897464055298563055107781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20786474961592336293908165 3897464055298563055107781)
            ·
              refine ⟨730774510368480572832709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3897464055298563055107781 730774510368480572832709)
              ·
                refine ⟨137020220694090107406133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730774510368480572832709 137020220694090107406133)
                ·
                  rfl

theorem cell20_900605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 4].length) (baseStart_900605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900605 prefixEnd_900605 := by exact prefixLift 900605
  have htrace : WordTrace (prefixWord ++ tailWord_900605) baseStart_900605 baseEnd_900605 := by
    simpa [prefixWord, tailWord_900605, baseEnd_900605] using wordTrace_append hprefix tailTrace_900605
  have hstable : (prefixWord ++ tailWord_900605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900605).length < 2 ^ (prefixWord ++ tailWord_900605).sum := by decide
  have hdescent : baseEnd_900605 < baseStart_900605 := by decide
  rcases family_descends (prefixWord ++ tailWord_900605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900615 : List Nat := [1, 1, 4, 3, 2, 1, 3, 3, 2]
def baseStart_900615 : Nat := 118140960795 + 900615 * 2 ^ 59
def prefixEnd_900615 : Nat := 4983230072969 + 3 ^ 40 * 900615 * 2
def baseEnd_900615 : Nat := 411065226354754731885025

theorem tailTrace_900615 : CollatzResearch.WordTrace tailWord_900615 prefixEnd_900615 411065226354754731885025 := by
  unfold tailWord_900615
  simp only [CollatzResearch.WordTrace]
  refine ⟨32848127632233142641447299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21898751754822095094298199 32848127632233142641447299)
  ·
    refine ⟨49272191448349713962170949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32848127632233142641447299 49272191448349713962170949)
    ·
      refine ⟨9238535896565571367907053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49272191448349713962170949 9238535896565571367907053)
      ·
        refine ⟨3464450961212089262965145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9238535896565571367907053 3464450961212089262965145)
        ·
          refine ⟨2598338220909066947223859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3464450961212089262965145 2598338220909066947223859)
          ·
            refine ⟨3897507331363600420835789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598338220909066947223859 3897507331363600420835789)
            ·
              refine ⟨1461565249261350157813421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3897507331363600420835789 1461565249261350157813421)
              ·
                refine ⟨548086968473006309180033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1461565249261350157813421 548086968473006309180033)
                ·
                  refine ⟨411065226354754731885025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548086968473006309180033 411065226354754731885025)
                  ·
                    rfl

theorem cell20_900615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 2].length) (baseStart_900615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900615 prefixEnd_900615 := by exact prefixLift 900615
  have htrace : WordTrace (prefixWord ++ tailWord_900615) baseStart_900615 baseEnd_900615 := by
    simpa [prefixWord, tailWord_900615, baseEnd_900615] using wordTrace_append hprefix tailTrace_900615
  have hstable : (prefixWord ++ tailWord_900615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900615).length < 2 ^ (prefixWord ++ tailWord_900615).sum := by decide
  have hdescent : baseEnd_900615 < baseStart_900615 := by decide
  rcases family_descends (prefixWord ++ tailWord_900615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900622 : List Nat := [4, 1, 1, 2, 5, 1, 6]
def baseStart_900622 : Nat := 118140960795 + 900622 * 2 ^ 59
def prefixEnd_900622 : Nat := 4983230072969 + 3 ^ 40 * 900622 * 2
def baseEnd_900622 : Nat := 45674269038388202072407

theorem tailTrace_900622 : CollatzResearch.WordTrace tailWord_900622 prefixEnd_900622 45674269038388202072407 := by
  unfold tailWord_900622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106047867900972854619015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21898921962138521891301413 4106047867900972854619015)
  ·
    refine ⟨6159071801851459281928523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4106047867900972854619015 6159071801851459281928523)
    ·
      refine ⟨9238607702777188922892785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6159071801851459281928523 9238607702777188922892785)
      ·
        refine ⟨6928955777082891692169589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9238607702777188922892785 6928955777082891692169589)
        ·
          refine ⟨649589604101521096140899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6928955777082891692169589 649589604101521096140899)
          ·
            refine ⟨974384406152281644211349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649589604101521096140899 974384406152281644211349)
            ·
              refine ⟨45674269038388202072407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 974384406152281644211349 45674269038388202072407)
              ·
                rfl

theorem cell20_900622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 6].length) (baseStart_900622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900622 prefixEnd_900622 := by exact prefixLift 900622
  have htrace : WordTrace (prefixWord ++ tailWord_900622) baseStart_900622 baseEnd_900622 := by
    simpa [prefixWord, tailWord_900622, baseEnd_900622] using wordTrace_append hprefix tailTrace_900622
  have hstable : (prefixWord ++ tailWord_900622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900622).length < 2 ^ (prefixWord ++ tailWord_900622).sum := by decide
  have hdescent : baseEnd_900622 < baseStart_900622 := by decide
  rcases family_descends (prefixWord ++ tailWord_900622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900632 : List Nat := [2, 1, 2, 3, 4, 1, 3, 2, 2]
def baseStart_900632 : Nat := 118140960795 + 900632 * 2 ^ 59
def prefixEnd_900632 : Nat := 4983230072969 + 3 ^ 40 * 900632 * 2
def baseEnd_900632 : Nat := 411072985617978228318289

theorem tailTrace_900632 : CollatzResearch.WordTrace tailWord_900632 prefixEnd_900632 411072985617978228318289 := by
  unfold tailWord_900632
  simp only [CollatzResearch.WordTrace]
  refine ⟨16424373836585777272408075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21899165115447703029877433 16424373836585777272408075)
  ·
    refine ⟨24636560754878665908612113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16424373836585777272408075 24636560754878665908612113)
    ·
      refine ⟨18477420566158999431459085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24636560754878665908612113 18477420566158999431459085)
      ·
        refine ⟨6929032712309624786797157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18477420566158999431459085 6929032712309624786797157)
        ·
          refine ⟨1299193633558054647524467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6929032712309624786797157 1299193633558054647524467)
          ·
            refine ⟨1948790450337081971286701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299193633558054647524467 1948790450337081971286701)
            ·
              refine ⟨730796418876405739232513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1948790450337081971286701 730796418876405739232513)
              ·
                refine ⟨548097314157304304424385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730796418876405739232513 548097314157304304424385)
                ·
                  refine ⟨411072985617978228318289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548097314157304304424385 411072985617978228318289)
                  ·
                    rfl

theorem cell20_900632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_900632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900632 prefixEnd_900632 := by exact prefixLift 900632
  have htrace : WordTrace (prefixWord ++ tailWord_900632) baseStart_900632 baseEnd_900632 := by
    simpa [prefixWord, tailWord_900632, baseEnd_900632] using wordTrace_append hprefix tailTrace_900632
  have hstable : (prefixWord ++ tailWord_900632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900632).length < 2 ^ (prefixWord ++ tailWord_900632).sum := by decide
  have hdescent : baseEnd_900632 < baseStart_900632 := by decide
  rcases family_descends (prefixWord ++ tailWord_900632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900638 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_900638 : Nat := 118140960795 + 900638 * 2 ^ 59
def prefixEnd_900638 : Nat := 4983230072969 + 3 ^ 40 * 900638 * 2
def baseEnd_900638 : Nat := 411075724181468874118265

theorem tailTrace_900638 : CollatzResearch.WordTrace tailWord_900638 prefixEnd_900638 411075724181468874118265 := by
  unfold tailWord_900638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106120813893727196191821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21899311007433211713023045 4106120813893727196191821)
  ·
    refine ⟨1539795305210147698571933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4106120813893727196191821 1539795305210147698571933)
    ·
      refine ⟨577423239453805386964475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1539795305210147698571933 577423239453805386964475)
      ·
        refine ⟨866134859180708080446713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577423239453805386964475 866134859180708080446713)
        ·
          refine ⟨649601144385531060335035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866134859180708080446713 649601144385531060335035)
          ·
            refine ⟨974401716578296590502553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649601144385531060335035 974401716578296590502553)
            ·
              refine ⟨730801287433722442876915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 974401716578296590502553 730801287433722442876915)
              ·
                refine ⟨1096201931150583664315373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730801287433722442876915 1096201931150583664315373)
                ·
                  refine ⟨411075724181468874118265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096201931150583664315373 411075724181468874118265)
                  ·
                    rfl

theorem cell20_900638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_900638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900638 prefixEnd_900638 := by exact prefixLift 900638
  have htrace : WordTrace (prefixWord ++ tailWord_900638) baseStart_900638 baseEnd_900638 := by
    simpa [prefixWord, tailWord_900638, baseEnd_900638] using wordTrace_append hprefix tailTrace_900638
  have hstable : (prefixWord ++ tailWord_900638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900638).length < 2 ^ (prefixWord ++ tailWord_900638).sum := by decide
  have hdescent : baseEnd_900638 < baseStart_900638 := by decide
  rcases family_descends (prefixWord ++ tailWord_900638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900643 : List Nat := [1, 1, 1, 4, 5, 1, 2, 5]
def baseStart_900643 : Nat := 118140960795 + 900643 * 2 ^ 59
def prefixEnd_900643 : Nat := 4983230072969 + 3 ^ 40 * 900643 * 2
def baseEnd_900643 : Nat := 137026002105903692983859

theorem tailTrace_900643 : CollatzResearch.WordTrace tailWord_900643 prefixEnd_900643 137026002105903692983859 := by
  unfold tailWord_900643
  simp only [CollatzResearch.WordTrace]
  refine ⟨32849148876131703423466583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21899432584087802282311055 32849148876131703423466583)
  ·
    refine ⟨49273723314197555135199875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32849148876131703423466583 49273723314197555135199875)
    ·
      refine ⟨73910584971296332702799813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49273723314197555135199875 73910584971296332702799813)
      ·
        refine ⟨13858234682118062381774965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73910584971296332702799813 13858234682118062381774965)
        ·
          refine ⟨1299209501448568348291403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13858234682118062381774965 1299209501448568348291403)
          ·
            refine ⟨1948814252172852522437105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299209501448568348291403 1948814252172852522437105)
            ·
              refine ⟨1461610689129639391827829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1948814252172852522437105 1461610689129639391827829)
              ·
                refine ⟨137026002105903692983859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1461610689129639391827829 137026002105903692983859)
                ·
                  rfl

theorem cell20_900643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 5].length) (baseStart_900643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900643 prefixEnd_900643 := by exact prefixLift 900643
  have htrace : WordTrace (prefixWord ++ tailWord_900643) baseStart_900643 baseEnd_900643 := by
    simpa [prefixWord, tailWord_900643, baseEnd_900643] using wordTrace_append hprefix tailTrace_900643
  have hstable : (prefixWord ++ tailWord_900643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900643).length < 2 ^ (prefixWord ++ tailWord_900643).sum := by decide
  have hdescent : baseEnd_900643 < baseStart_900643 := by decide
  rcases family_descends (prefixWord ++ tailWord_900643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900664 : List Nat := [2, 1, 2, 1, 4, 2, 2, 6]
def baseStart_900664 : Nat := 118140960795 + 900664 * 2 ^ 59
def prefixEnd_900664 : Nat := 4983230072969 + 3 ^ 40 * 900664 * 2
def baseEnd_900664 : Nat := 137029197096642779750497

theorem tailTrace_900664 : CollatzResearch.WordTrace tailWord_900664 prefixEnd_900664 137029197096642779750497 := by
  unfold tailWord_900664
  simp only [CollatzResearch.WordTrace]
  refine ⟨16424957404527812004990523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21899943206037082673320697 16424957404527812004990523)
  ·
    refine ⟨24637436106791718007485785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16424957404527812004990523 24637436106791718007485785)
    ·
      refine ⟨18478077080093788505614339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24637436106791718007485785 18478077080093788505614339)
      ·
        refine ⟨27717115620140682758421509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18478077080093788505614339 27717115620140682758421509)
        ·
          refine ⟨5196959178776378017204033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27717115620140682758421509 5196959178776378017204033)
          ·
            refine ⟨3897719384082283512903025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5196959178776378017204033 3897719384082283512903025)
            ·
              refine ⟨2923289538061712634677269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897719384082283512903025 2923289538061712634677269)
              ·
                refine ⟨137029197096642779750497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2923289538061712634677269 137029197096642779750497)
                ·
                  rfl

theorem cell20_900664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_900664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900664 prefixEnd_900664 := by exact prefixLift 900664
  have htrace : WordTrace (prefixWord ++ tailWord_900664) baseStart_900664 baseEnd_900664 := by
    simpa [prefixWord, tailWord_900664, baseEnd_900664] using wordTrace_append hprefix tailTrace_900664
  have hstable : (prefixWord ++ tailWord_900664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900664).length < 2 ^ (prefixWord ++ tailWord_900664).sum := by decide
  have hdescent : baseEnd_900664 < baseStart_900664 := by decide
  rcases family_descends (prefixWord ++ tailWord_900664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900688 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 3]
def baseStart_900688 : Nat := 118140960795 + 900688 * 2 ^ 59
def prefixEnd_900688 : Nat := 4983230072969 + 3 ^ 40 * 900688 * 2
def baseEnd_900688 : Nat := 411098545543890922451393

theorem tailTrace_900688 : CollatzResearch.WordTrace tailWord_900688 prefixEnd_900688 411098545543890922451393 := by
  unfold tailWord_900688
  simp only [CollatzResearch.WordTrace]
  refine ⟨16425395080484338054427359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21900526773979117405903145 16425395080484338054427359)
  ·
    refine ⟨24638092620726507081641039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16425395080484338054427359 24638092620726507081641039)
    ·
      refine ⟨36957138931089760622461559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24638092620726507081641039 36957138931089760622461559)
      ·
        refine ⟨55435708396634640933692339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36957138931089760622461559 55435708396634640933692339)
        ·
          refine ⟨83153562594951961400538509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55435708396634640933692339 83153562594951961400538509)
          ·
            refine ⟨31182585973106985525201941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83153562594951961400538509 31182585973106985525201941)
            ·
              refine ⟨1461683717489389946493841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31182585973106985525201941 1461683717489389946493841)
              ·
                refine ⟨1096262788117042459870381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461683717489389946493841 1096262788117042459870381)
                ·
                  refine ⟨411098545543890922451393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096262788117042459870381 411098545543890922451393)
                  ·
                    rfl

theorem cell20_900688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_900688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900688 prefixEnd_900688 := by exact prefixLift 900688
  have htrace : WordTrace (prefixWord ++ tailWord_900688) baseStart_900688 baseEnd_900688 := by
    simpa [prefixWord, tailWord_900688, baseEnd_900688] using wordTrace_append hprefix tailTrace_900688
  have hstable : (prefixWord ++ tailWord_900688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900688).length < 2 ^ (prefixWord ++ tailWord_900688).sum := by decide
  have hdescent : baseEnd_900688 < baseStart_900688 := by decide
  rcases family_descends (prefixWord ++ tailWord_900688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900694 : List Nat := [5, 2, 2, 2, 1, 2, 1, 5]
def baseStart_900694 : Nat := 118140960795 + 900694 * 2 ^ 59
def prefixEnd_900694 : Nat := 4983230072969 + 3 ^ 40 * 900694 * 2
def baseEnd_900694 : Nat := 137033761369127189417123

theorem tailTrace_900694 : CollatzResearch.WordTrace tailWord_900694 prefixEnd_900694 137033761369127189417123 := by
  unfold tailWord_900694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2053188062434183695848321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21900672665964626089048757 2053188062434183695848321)
  ·
    refine ⟨1539891046825637771886241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2053188062434183695848321 1539891046825637771886241)
    ·
      refine ⟨1154918285119228328914681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1539891046825637771886241 1154918285119228328914681)
      ·
        refine ⟨866188713839421246686011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1154918285119228328914681 866188713839421246686011)
        ·
          refine ⟨1299283070759131870029017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866188713839421246686011 1299283070759131870029017)
          ·
            refine ⟨974462303069348902521763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1299283070759131870029017 974462303069348902521763)
            ·
              refine ⟨1461693454604023353782645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974462303069348902521763 1461693454604023353782645)
              ·
                refine ⟨137033761369127189417123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1461693454604023353782645 137033761369127189417123)
                ·
                  rfl

theorem cell20_900694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_900694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900694 prefixEnd_900694 := by exact prefixLift 900694
  have htrace : WordTrace (prefixWord ++ tailWord_900694) baseStart_900694 baseEnd_900694 := by
    simpa [prefixWord, tailWord_900694, baseEnd_900694] using wordTrace_append hprefix tailTrace_900694
  have hstable : (prefixWord ++ tailWord_900694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900694).length < 2 ^ (prefixWord ++ tailWord_900694).sum := by decide
  have hdescent : baseEnd_900694 < baseStart_900694 := by decide
  rcases family_descends (prefixWord ++ tailWord_900694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900712 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_900712 : Nat := 118140960795 + 900712 * 2 ^ 59
def prefixEnd_900712 : Nat := 4983230072969 + 3 ^ 40 * 900712 * 2
def baseEnd_900712 : Nat := 411109499797853505651295

theorem tailTrace_900712 : CollatzResearch.WordTrace tailWord_900712 prefixEnd_900712 411109499797853505651295 := by
  unfold tailWord_900712
  simp only [CollatzResearch.WordTrace]
  refine ⟨16425832756440864103864195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21901110341921152138485593 16425832756440864103864195)
  ·
    refine ⟨24638749134661296155796293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16425832756440864103864195 24638749134661296155796293)
    ·
      refine ⟨4619765462748993029211805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24638749134661296155796293 4619765462748993029211805)
      ·
        refine ⟨1732412048530872385954427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4619765462748993029211805 1732412048530872385954427)
        ·
          refine ⟨2598618072796308578931641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1732412048530872385954427 2598618072796308578931641)
          ·
            refine ⟨1948963554597231434198731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2598618072796308578931641 1948963554597231434198731)
            ·
              refine ⟨2923445331895847151298097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948963554597231434198731 2923445331895847151298097)
              ·
                refine ⟨2192583998921885363473573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923445331895847151298097 2192583998921885363473573)
                ·
                  refine ⟨411109499797853505651295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2192583998921885363473573 411109499797853505651295)
                  ·
                    rfl

theorem cell20_900712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_900712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900712 prefixEnd_900712 := by exact prefixLift 900712
  have htrace : WordTrace (prefixWord ++ tailWord_900712) baseStart_900712 baseEnd_900712 := by
    simpa [prefixWord, tailWord_900712, baseEnd_900712] using wordTrace_append hprefix tailTrace_900712
  have hstable : (prefixWord ++ tailWord_900712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900712).length < 2 ^ (prefixWord ++ tailWord_900712).sum := by decide
  have hdescent : baseEnd_900712 < baseStart_900712 := by decide
  rcases family_descends (prefixWord ++ tailWord_900712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900743 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 3]
def baseStart_900743 : Nat := 118140960795 + 900743 * 2 ^ 59
def prefixEnd_900743 : Nat := 4983230072969 + 3 ^ 40 * 900743 * 2
def baseEnd_900743 : Nat := 411123649042555175617835

theorem tailTrace_900743 : CollatzResearch.WordTrace tailWord_900743 prefixEnd_900743 411123649042555175617835 := by
  unfold tailWord_900743
  simp only [CollatzResearch.WordTrace]
  refine ⟨32852796175769420502106883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21901864117179613668071255 32852796175769420502106883)
  ·
    refine ⟨49279194263654130753160325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32852796175769420502106883 49279194263654130753160325)
    ·
      refine ⟨9239848924435149516217561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49279194263654130753160325 9239848924435149516217561)
      ·
        refine ⟨6929886693326362137163171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9239848924435149516217561 6929886693326362137163171)
        ·
          refine ⟨10394830039989543205744757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6929886693326362137163171 10394830039989543205744757)
          ·
            refine ⟨974515316249019675538571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10394830039989543205744757 974515316249019675538571)
            ·
              refine ⟨1461772974373529513307857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974515316249019675538571 1461772974373529513307857)
              ·
                refine ⟨1096329730780147134980893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461772974373529513307857 1096329730780147134980893)
                ·
                  refine ⟨411123649042555175617835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096329730780147134980893 411123649042555175617835)
                  ·
                    rfl

theorem cell20_900743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 3].length) (baseStart_900743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900743 prefixEnd_900743 := by exact prefixLift 900743
  have htrace : WordTrace (prefixWord ++ tailWord_900743) baseStart_900743 baseEnd_900743 := by
    simpa [prefixWord, tailWord_900743, baseEnd_900743] using wordTrace_append hprefix tailTrace_900743
  have hstable : (prefixWord ++ tailWord_900743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900743).length < 2 ^ (prefixWord ++ tailWord_900743).sum := by decide
  have hdescent : baseEnd_900743 < baseStart_900743 := by decide
  rcases family_descends (prefixWord ++ tailWord_900743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900747 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_900747 : Nat := 118140960795 + 900747 * 2 ^ 59
def prefixEnd_900747 : Nat := 4983230072969 + 3 ^ 40 * 900747 * 2
def baseEnd_900747 : Nat := 411125474751548939484485

theorem tailTrace_900747 : CollatzResearch.WordTrace tailWord_900747 prefixEnd_900747 411125474751548939484485 := by
  unfold tailWord_900747
  simp only [CollatzResearch.WordTrace]
  refine ⟨32852942067754929185252495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21901961378503286123501663 32852942067754929185252495)
  ·
    refine ⟨49279413101632393777878743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32852942067754929185252495 49279413101632393777878743)
    ·
      refine ⟨73919119652448590666818115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49279413101632393777878743 73919119652448590666818115)
      ·
        refine ⟨110878679478672886000227173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73919119652448590666818115 110878679478672886000227173)
        ·
          refine ⟨20789752402251166125042595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110878679478672886000227173 20789752402251166125042595)
          ·
            refine ⟨31184628603376749187563893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20789752402251166125042595 31184628603376749187563893)
            ·
              refine ⟨2923558931566570236334115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31184628603376749187563893 2923558931566570236334115)
              ·
                refine ⟨4385338397349855354501173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923558931566570236334115 4385338397349855354501173)
                ·
                  refine ⟨411125474751548939484485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4385338397349855354501173 411125474751548939484485)
                  ·
                    rfl

theorem cell20_900747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_900747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900747 prefixEnd_900747 := by exact prefixLift 900747
  have htrace : WordTrace (prefixWord ++ tailWord_900747) baseStart_900747 baseEnd_900747 := by
    simpa [prefixWord, tailWord_900747, baseEnd_900747] using wordTrace_append hprefix tailTrace_900747
  have hstable : (prefixWord ++ tailWord_900747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900747).length < 2 ^ (prefixWord ++ tailWord_900747).sum := by decide
  have hdescent : baseEnd_900747 < baseStart_900747 := by decide
  rcases family_descends (prefixWord ++ tailWord_900747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900750 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_900750 : Nat := 118140960795 + 900750 * 2 ^ 59
def prefixEnd_900750 : Nat := 4983230072969 + 3 ^ 40 * 900750 * 2
def baseEnd_900750 : Nat := 411126844033294262384473

theorem tailTrace_900750 : CollatzResearch.WordTrace tailWord_900750 prefixEnd_900750 411126844033294262384473 := by
  unfold tailWord_900750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106631435843007587201463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21902034324496040465074469 4106631435843007587201463)
  ·
    refine ⟨6159947153764511380802195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4106631435843007587201463 6159947153764511380802195)
    ·
      refine ⟨9239920730646767071203293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6159947153764511380802195 9239920730646767071203293)
      ·
        refine ⟨3464970273992537651701235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9239920730646767071203293 3464970273992537651701235)
        ·
          refine ⟨5197455410988806477551853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464970273992537651701235 5197455410988806477551853)
          ·
            refine ⟨1949045779120802429081945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5197455410988806477551853 1949045779120802429081945)
            ·
              refine ⟨1461784334340601821811459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1949045779120802429081945 1461784334340601821811459)
              ·
                refine ⟨2192676501510902732717189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461784334340601821811459 2192676501510902732717189)
                ·
                  refine ⟨411126844033294262384473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2192676501510902732717189 411126844033294262384473)
                  ·
                    rfl

theorem cell20_900750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_900750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900750 prefixEnd_900750 := by exact prefixLift 900750
  have htrace : WordTrace (prefixWord ++ tailWord_900750) baseStart_900750 baseEnd_900750 := by
    simpa [prefixWord, tailWord_900750, baseEnd_900750] using wordTrace_append hprefix tailTrace_900750
  have hstable : (prefixWord ++ tailWord_900750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900750).length < 2 ^ (prefixWord ++ tailWord_900750).sum := by decide
  have hdescent : baseEnd_900750 < baseStart_900750 := by decide
  rcases family_descends (prefixWord ++ tailWord_900750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900770 : List Nat := [3, 3, 1, 4, 2, 1, 2, 4]
def baseStart_900770 : Nat := 118140960795 + 900770 * 2 ^ 59
def prefixEnd_900770 : Nat := 4983230072969 + 3 ^ 40 * 900770 * 2
def baseEnd_900770 : Nat := 137045324192754360572575

theorem tailTrace_900770 : CollatzResearch.WordTrace tailWord_900770 prefixEnd_900770 137045324192754360572575 := by
  unfold tailWord_900770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8213445236667901028334941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21902520631114402742226509 8213445236667901028334941)
  ·
    refine ⟨3080041963750462885625603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8213445236667901028334941 3080041963750462885625603)
    ·
      refine ⟨4620062945625694328438405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3080041963750462885625603 4620062945625694328438405)
      ·
        refine ⟨866261802304817686582201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4620062945625694328438405 866261802304817686582201)
        ·
          refine ⟨649696351728613264936651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866261802304817686582201 649696351728613264936651)
          ·
            refine ⟨974544527592919897404977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649696351728613264936651 974544527592919897404977)
            ·
              refine ⟨730908395694689923053733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 974544527592919897404977 730908395694689923053733)
              ·
                refine ⟨137045324192754360572575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730908395694689923053733 137045324192754360572575)
                ·
                  rfl

theorem cell20_900770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_900770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900770 prefixEnd_900770 := by exact prefixLift 900770
  have htrace : WordTrace (prefixWord ++ tailWord_900770) baseStart_900770 baseEnd_900770 := by
    simpa [prefixWord, tailWord_900770, baseEnd_900770] using wordTrace_append hprefix tailTrace_900770
  have hstable : (prefixWord ++ tailWord_900770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900770).length < 2 ^ (prefixWord ++ tailWord_900770).sum := by decide
  have hdescent : baseEnd_900770 < baseStart_900770 := by decide
  rcases family_descends (prefixWord ++ tailWord_900770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900792 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_900792 : Nat := 118140960795 + 900792 * 2 ^ 59
def prefixEnd_900792 : Nat := 4983230072969 + 3 ^ 40 * 900792 * 2
def baseEnd_900792 : Nat := 411146013977728782984301

theorem tailTrace_900792 : CollatzResearch.WordTrace tailWord_900792 prefixEnd_900792 411146013977728782984301 := by
  unfold tailWord_900792
  simp only [CollatzResearch.WordTrace]
  refine ⟨16427291676295950935320315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21903055568394601247093753 16427291676295950935320315)
  ·
    refine ⟨24640937514443926402980473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16427291676295950935320315 24640937514443926402980473)
    ·
      refine ⟨18480703135832944802235355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24640937514443926402980473 18480703135832944802235355)
      ·
        refine ⟨27721054703749417203353033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18480703135832944802235355 27721054703749417203353033)
        ·
          refine ⟨20790791027812062902514775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27721054703749417203353033 20790791027812062902514775)
          ·
            refine ⟨31186186541718094353772163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20790791027812062902514775 31186186541718094353772163)
            ·
              refine ⟨46779279812577141530658245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31186186541718094353772163 46779279812577141530658245)
              ·
                refine ⟨8771114964858214036998421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46779279812577141530658245 8771114964858214036998421)
                ·
                  refine ⟨411146013977728782984301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8771114964858214036998421 411146013977728782984301)
                  ·
                    rfl

theorem cell20_900792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_900792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900792 prefixEnd_900792 := by exact prefixLift 900792
  have htrace : WordTrace (prefixWord ++ tailWord_900792) baseStart_900792 baseEnd_900792 := by
    simpa [prefixWord, tailWord_900792, baseEnd_900792] using wordTrace_append hprefix tailTrace_900792
  have hstable : (prefixWord ++ tailWord_900792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900792).length < 2 ^ (prefixWord ++ tailWord_900792).sum := by decide
  have hdescent : baseEnd_900792 < baseStart_900792 := by decide
  rcases family_descends (prefixWord ++ tailWord_900792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900854 : List Nat := [5, 1, 1, 1, 1, 11]
def baseStart_900854 : Nat := 118140960795 + 900854 * 2 ^ 59
def prefixEnd_900854 : Nat := 4983230072969 + 3 ^ 40 * 900854 * 2
def baseEnd_900854 : Nat := 15228678239523411959903

theorem tailTrace_900854 : CollatzResearch.WordTrace tailWord_900854 prefixEnd_900854 15228678239523411959903 := by
  unfold tailWord_900854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2053552792397955403712351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21904563118911524306265077 2053552792397955403712351)
  ·
    refine ⟨3080329188596933105568527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2053552792397955403712351 3080329188596933105568527)
    ·
      refine ⟨4620493782895399658352791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3080329188596933105568527 4620493782895399658352791)
      ·
        refine ⟨6930740674343099487529187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4620493782895399658352791 6930740674343099487529187)
        ·
          refine ⟨10396111011514649231293781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6930740674343099487529187 10396111011514649231293781)
          ·
            refine ⟨15228678239523411959903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10396111011514649231293781 15228678239523411959903)
            ·
              rfl

theorem cell20_900854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 11].length) (baseStart_900854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900854 prefixEnd_900854 := by exact prefixLift 900854
  have htrace : WordTrace (prefixWord ++ tailWord_900854) baseStart_900854 baseEnd_900854 := by
    simpa [prefixWord, tailWord_900854, baseEnd_900854] using wordTrace_append hprefix tailTrace_900854
  have hstable : (prefixWord ++ tailWord_900854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900854).length < 2 ^ (prefixWord ++ tailWord_900854).sum := by decide
  have hdescent : baseEnd_900854 < baseStart_900854 := by decide
  rcases family_descends (prefixWord ++ tailWord_900854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900877 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 4]
def baseStart_900877 : Nat := 118140960795 + 900877 * 2 ^ 59
def prefixEnd_900877 : Nat := 4983230072969 + 3 ^ 40 * 900877 * 2
def baseEnd_900877 : Nat := 411184810293846265150621

theorem tailTrace_900877 : CollatzResearch.WordTrace tailWord_900877 prefixEnd_900877 411184810293846265150621 := by
  unfold tailWord_900877
  simp only [CollatzResearch.WordTrace]
  refine ⟨32857683557283961387484885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21905122371522640924989923 32857683557283961387484885)
  ·
    refine ⟨770101958373842845019177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32857683557283961387484885 770101958373842845019177)
    ·
      refine ⟨577576468780382133764383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 770101958373842845019177 577576468780382133764383)
      ·
        refine ⟨866364703170573200646575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577576468780382133764383 866364703170573200646575)
        ·
          refine ⟨1299547054755859800969863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866364703170573200646575 1299547054755859800969863)
          ·
            refine ⟨1949320582133789701454795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299547054755859800969863 1949320582133789701454795)
            ·
              refine ⟨2923980873200684552182193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1949320582133789701454795 2923980873200684552182193)
              ·
                refine ⟨2192985654900513414136645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923980873200684552182193 2192985654900513414136645)
                ·
                  refine ⟨411184810293846265150621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2192985654900513414136645 411184810293846265150621)
                  ·
                    rfl

theorem cell20_900877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_900877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900877 prefixEnd_900877 := by exact prefixLift 900877
  have htrace : WordTrace (prefixWord ++ tailWord_900877) baseStart_900877 baseEnd_900877 := by
    simpa [prefixWord, tailWord_900877, baseEnd_900877] using wordTrace_append hprefix tailTrace_900877
  have hstable : (prefixWord ++ tailWord_900877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900877).length < 2 ^ (prefixWord ++ tailWord_900877).sum := by decide
  have hdescent : baseEnd_900877 < baseStart_900877 := by decide
  rcases family_descends (prefixWord ++ tailWord_900877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900878 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_900878 : Nat := 118140960795 + 900878 * 2 ^ 59
def prefixEnd_900878 : Nat := 4983230072969 + 3 ^ 40 * 900878 * 2
def baseEnd_900878 : Nat := 411185266721094706117283

theorem tailTrace_900878 : CollatzResearch.WordTrace tailWord_900878 prefixEnd_900878 411185266721094706117283 := by
  unfold tailWord_900878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4107215003785042319783911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21905146686853559038847525 4107215003785042319783911)
  ·
    refine ⟨6160822505677563479675867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4107215003785042319783911 6160822505677563479675867)
    ·
      refine ⟨9241233758516345219513801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6160822505677563479675867 9241233758516345219513801)
      ·
        refine ⟨6930925318887258914635351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9241233758516345219513801 6930925318887258914635351)
        ·
          refine ⟨10396387978330888371953027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6930925318887258914635351 10396387978330888371953027)
          ·
            refine ⟨15594581967496332557929541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10396387978330888371953027 15594581967496332557929541)
            ·
              refine ⟨2923984118905562354611789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15594581967496332557929541 2923984118905562354611789)
              ·
                refine ⟨1096494044589585882979421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2923984118905562354611789 1096494044589585882979421)
                ·
                  refine ⟨411185266721094706117283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096494044589585882979421 411185266721094706117283)
                  ·
                    rfl

theorem cell20_900878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_900878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900878 prefixEnd_900878 := by exact prefixLift 900878
  have htrace : WordTrace (prefixWord ++ tailWord_900878) baseStart_900878 baseEnd_900878 := by
    simpa [prefixWord, tailWord_900878, baseEnd_900878] using wordTrace_append hprefix tailTrace_900878
  have hstable : (prefixWord ++ tailWord_900878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900878).length < 2 ^ (prefixWord ++ tailWord_900878).sum := by decide
  have hdescent : baseEnd_900878 < baseStart_900878 := by decide
  rcases family_descends (prefixWord ++ tailWord_900878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900884 : List Nat := [2, 4, 4, 1, 1, 1, 3, 4]
def baseStart_900884 : Nat := 118140960795 + 900884 * 2 ^ 59
def prefixEnd_900884 : Nat := 4983230072969 + 3 ^ 40 * 900884 * 2
def baseEnd_900884 : Nat := 137062668428195117305753

theorem tailTrace_900884 : CollatzResearch.WordTrace tailWord_900884 prefixEnd_900884 137062668428195117305753 := by
  unfold tailWord_900884
  simp only [CollatzResearch.WordTrace]
  refine ⟨16428969434129300791494853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21905292578839067721993137 16428969434129300791494853)
  ·
    refine ⟨3080431768899243898405285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16428969434129300791494853 3080431768899243898405285)
    ·
      refine ⟨577580956668608230950991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3080431768899243898405285 577580956668608230950991)
      ·
        refine ⟨866371435002912346426487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577580956668608230950991 866371435002912346426487)
        ·
          refine ⟨1299557152504368519639731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866371435002912346426487 1299557152504368519639731)
          ·
            refine ⟨1949335728756552779459597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299557152504368519639731 1949335728756552779459597)
            ·
              refine ⟨731000898283707292297349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1949335728756552779459597 731000898283707292297349)
              ·
                refine ⟨137062668428195117305753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 731000898283707292297349 137062668428195117305753)
                ·
                  rfl

theorem cell20_900884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_900884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900884 prefixEnd_900884 := by exact prefixLift 900884
  have htrace : WordTrace (prefixWord ++ tailWord_900884) baseStart_900884 baseEnd_900884 := by
    simpa [prefixWord, tailWord_900884, baseEnd_900884] using wordTrace_append hprefix tailTrace_900884
  have hstable : (prefixWord ++ tailWord_900884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900884).length < 2 ^ (prefixWord ++ tailWord_900884).sum := by decide
  have hdescent : baseEnd_900884 < baseStart_900884 := by decide
  rcases family_descends (prefixWord ++ tailWord_900884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900885 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 4]
def baseStart_900885 : Nat := 118140960795 + 900885 * 2 ^ 59
def prefixEnd_900885 : Nat := 4983230072969 + 3 ^ 40 * 900885 * 2
def baseEnd_900885 : Nat := 411188461711833792883921

theorem tailTrace_900885 : CollatzResearch.WordTrace tailWord_900885 prefixEnd_900885 411188461711833792883921 := by
  unfold tailWord_900885
  simp only [CollatzResearch.WordTrace]
  refine ⟨32857975341254978753776109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21905316894169985835850739 32857975341254978753776109)
  ·
    refine ⟨12321740752970617032666041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32857975341254978753776109 12321740752970617032666041)
    ·
      refine ⟨9241305564727962774499531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12321740752970617032666041 9241305564727962774499531)
      ·
        refine ⟨13861958347091944161749297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9241305564727962774499531 13861958347091944161749297)
        ·
          refine ⟨10396468760318958121311973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13861958347091944161749297 10396468760318958121311973)
          ·
            refine ⟨1949337892559804647745995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10396468760318958121311973 1949337892559804647745995)
            ·
              refine ⟨2924006838839706971618993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1949337892559804647745995 2924006838839706971618993)
              ·
                refine ⟨2193005129129780228714245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2924006838839706971618993 2193005129129780228714245)
                ·
                  refine ⟨411188461711833792883921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2193005129129780228714245 411188461711833792883921)
                  ·
                    rfl

theorem cell20_900885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_900885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900885 prefixEnd_900885 := by exact prefixLift 900885
  have htrace : WordTrace (prefixWord ++ tailWord_900885) baseStart_900885 baseEnd_900885 := by
    simpa [prefixWord, tailWord_900885, baseEnd_900885] using wordTrace_append hprefix tailTrace_900885
  have hstable : (prefixWord ++ tailWord_900885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900885).length < 2 ^ (prefixWord ++ tailWord_900885).sum := by decide
  have hdescent : baseEnd_900885 < baseStart_900885 := by decide
  rcases family_descends (prefixWord ++ tailWord_900885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900974 : List Nat := [4, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_900974 : Nat := 118140960795 + 900974 * 2 ^ 59
def prefixEnd_900974 : Nat := 4983230072969 + 3 ^ 40 * 900974 * 2
def baseEnd_900974 : Nat := 411229083736945038916891

theorem tailTrace_900974 : CollatzResearch.WordTrace tailWord_900974 prefixEnd_900974 411229083736945038916891 := by
  unfold tailWord_900974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4107652679741568369220747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21907480958621697969177317 4107652679741568369220747)
  ·
    refine ⟨6161479019612352553831121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4107652679741568369220747 6161479019612352553831121)
    ·
      refine ⟨4621109264709264415373341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6161479019612352553831121 4621109264709264415373341)
      ·
        refine ⟨1732915974265974155765003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4621109264709264415373341 1732915974265974155765003)
        ·
          refine ⟨2599373961398961233647505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1732915974265974155765003 2599373961398961233647505)
          ·
            refine ⟨1949530471049220925235629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2599373961398961233647505 1949530471049220925235629)
            ·
              refine ⟨731073926643457846963361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1949530471049220925235629 731073926643457846963361)
              ·
                refine ⟨548305444982593385222521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731073926643457846963361 548305444982593385222521)
                ·
                  refine ⟨411229083736945038916891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548305444982593385222521 411229083736945038916891)
                  ·
                    rfl

theorem cell20_900974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_900974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_900974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_900974 prefixEnd_900974 := by exact prefixLift 900974
  have htrace : WordTrace (prefixWord ++ tailWord_900974) baseStart_900974 baseEnd_900974 := by
    simpa [prefixWord, tailWord_900974, baseEnd_900974] using wordTrace_append hprefix tailTrace_900974
  have hstable : (prefixWord ++ tailWord_900974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900974).length < 2 ^ (prefixWord ++ tailWord_900974).sum := by decide
  have hdescent : baseEnd_900974 < baseStart_900974 := by decide
  rcases family_descends (prefixWord ++ tailWord_900974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901082 : List Nat := [3, 1, 1, 2, 5, 1, 7]
def baseStart_901082 : Nat := 118140960795 + 901082 * 2 ^ 59
def prefixEnd_901082 : Nat := 4983230072969 + 3 ^ 40 * 901082 * 2
def baseEnd_901082 : Nat := 45697597542197407035161

theorem tailTrace_901082 : CollatzResearch.WordTrace tailWord_901082 prefixEnd_901082 45697597542197407035161 := by
  unfold tailWord_901082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8216290130385320349674375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21910107014360854265798333 8216290130385320349674375)
  ·
    refine ⟨12324435195577980524511563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8216290130385320349674375 12324435195577980524511563)
    ·
      refine ⟨18486652793366970786767345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12324435195577980524511563 18486652793366970786767345)
      ·
        refine ⟨13864989595025228090075509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18486652793366970786767345 13864989595025228090075509)
        ·
          refine ⟨1299842774533615133444579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13864989595025228090075509 1299842774533615133444579)
          ·
            refine ⟨1949764161800422700166869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299842774533615133444579 1949764161800422700166869)
            ·
              refine ⟨45697597542197407035161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1949764161800422700166869 45697597542197407035161)
              ·
                rfl

theorem cell20_901082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 7].length) (baseStart_901082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901082 prefixEnd_901082 := by exact prefixLift 901082
  have htrace : WordTrace (prefixWord ++ tailWord_901082) baseStart_901082 baseEnd_901082 := by
    simpa [prefixWord, tailWord_901082, baseEnd_901082] using wordTrace_append hprefix tailTrace_901082
  have hstable : (prefixWord ++ tailWord_901082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901082).length < 2 ^ (prefixWord ++ tailWord_901082).sum := by decide
  have hdescent : baseEnd_901082 < baseStart_901082 := by decide
  rcases family_descends (prefixWord ++ tailWord_901082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901103 : List Nat := [1, 1, 2, 1, 4, 2, 2, 7]
def baseStart_901103 : Nat := 118140960795 + 901103 * 2 ^ 59
def prefixEnd_901103 : Nat := 4983230072969 + 3 ^ 40 * 901103 * 2
def baseEnd_901103 : Nat := 137095987617331307872121

theorem tailTrace_901103 : CollatzResearch.WordTrace tailWord_901103 prefixEnd_901103 137095987617331307872121 := by
  unfold tailWord_901103
  simp only [CollatzResearch.WordTrace]
  refine ⟨32865926454465201985211963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21910617636310134656807975 32865926454465201985211963)
  ·
    refine ⟨49298889681697802977817945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32865926454465201985211963 49298889681697802977817945)
    ·
      refine ⟨36974167261273352233363459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49298889681697802977817945 36974167261273352233363459)
      ·
        refine ⟨55461250891910028350045189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36974167261273352233363459 55461250891910028350045189)
        ·
          refine ⟨10398984542233130315633473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55461250891910028350045189 10398984542233130315633473)
          ·
            refine ⟨7799238406674847736725105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10398984542233130315633473 7799238406674847736725105)
            ·
              refine ⟨5849428805006135802543829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7799238406674847736725105 5849428805006135802543829)
              ·
                refine ⟨137095987617331307872121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5849428805006135802543829 137095987617331307872121)
                ·
                  rfl

theorem cell20_901103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_901103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901103 prefixEnd_901103 := by exact prefixLift 901103
  have htrace : WordTrace (prefixWord ++ tailWord_901103) baseStart_901103 baseEnd_901103 := by
    simpa [prefixWord, tailWord_901103, baseEnd_901103] using wordTrace_append hprefix tailTrace_901103
  have hstable : (prefixWord ++ tailWord_901103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901103).length < 2 ^ (prefixWord ++ tailWord_901103).sum := by decide
  have hdescent : baseEnd_901103 < baseStart_901103 := by decide
  rcases family_descends (prefixWord ++ tailWord_901103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901127 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_901127 : Nat := 118140960795 + 901127 * 2 ^ 59
def prefixEnd_901127 : Nat := 4983230072969 + 3 ^ 40 * 901127 * 2
def baseEnd_901127 : Nat := 411298917105956506816265

theorem tailTrace_901127 : CollatzResearch.WordTrace tailWord_901127 prefixEnd_901127 411298917105956506816265 := by
  unfold tailWord_901127
  simp only [CollatzResearch.WordTrace]
  refine ⟨32866801806378254084085635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21911201204252169389390423 32866801806378254084085635)
  ·
    refine ⟨49300202709567381126128453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32866801806378254084085635 49300202709567381126128453)
    ·
      refine ⟨9243788008043883961149085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49300202709567381126128453 9243788008043883961149085)
      ·
        refine ⟨3466420503016456485430907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9243788008043883961149085 3466420503016456485430907)
        ·
          refine ⟨5199630754524684728146361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466420503016456485430907 5199630754524684728146361)
          ·
            refine ⟨3899723065893513546109771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5199630754524684728146361 3899723065893513546109771)
            ·
              refine ⟨5849584598840270319164657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899723065893513546109771 5849584598840270319164657)
              ·
                refine ⟨4387188449130202739373493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5849584598840270319164657 4387188449130202739373493)
                ·
                  refine ⟨411298917105956506816265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4387188449130202739373493 411298917105956506816265)
                  ·
                    rfl

theorem cell20_901127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_901127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901127 prefixEnd_901127 := by exact prefixLift 901127
  have htrace : WordTrace (prefixWord ++ tailWord_901127) baseStart_901127 baseEnd_901127 := by
    simpa [prefixWord, tailWord_901127, baseEnd_901127] using wordTrace_append hprefix tailTrace_901127
  have hstable : (prefixWord ++ tailWord_901127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901127).length < 2 ^ (prefixWord ++ tailWord_901127).sum := by decide
  have hdescent : baseEnd_901127 < baseStart_901127 := by decide
  rcases family_descends (prefixWord ++ tailWord_901127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901133 : List Nat := [1, 7, 1, 2, 1, 2, 6]
def baseStart_901133 : Nat := 118140960795 + 901133 * 2 ^ 59
def prefixEnd_901133 : Nat := 4983230072969 + 3 ^ 40 * 901133 * 2
def baseEnd_901133 : Nat := 45700183963271905846249

theorem tailTrace_901133 : CollatzResearch.WordTrace tailWord_901133 prefixEnd_901133 45700183963271905846249 := by
  unfold tailWord_901133
  simp only [CollatzResearch.WordTrace]
  refine ⟨32867020644356517108804053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21911347096237678072536035 32867020644356517108804053)
  ·
    refine ⟨770320796352105869737595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32867020644356517108804053 770320796352105869737595)
    ·
      refine ⟨1155481194528158804606393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 770320796352105869737595 1155481194528158804606393)
      ·
        refine ⟨866610895896119103454795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1155481194528158804606393 866610895896119103454795)
        ·
          refine ⟨1299916343844178655182193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866610895896119103454795 1299916343844178655182193)
          ·
            refine ⟨974937257883133991386645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1299916343844178655182193 974937257883133991386645)
            ·
              refine ⟨45700183963271905846249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 974937257883133991386645 45700183963271905846249)
              ·
                rfl

theorem cell20_901133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 6].length) (baseStart_901133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901133 prefixEnd_901133 := by exact prefixLift 901133
  have htrace : WordTrace (prefixWord ++ tailWord_901133) baseStart_901133 baseEnd_901133 := by
    simpa [prefixWord, tailWord_901133, baseEnd_901133] using wordTrace_append hprefix tailTrace_901133
  have hstable : (prefixWord ++ tailWord_901133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901133).length < 2 ^ (prefixWord ++ tailWord_901133).sum := by decide
  have hdescent : baseEnd_901133 < baseStart_901133 := by decide
  rcases family_descends (prefixWord ++ tailWord_901133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901189 : List Nat := [1, 3, 1, 1, 1, 3, 1, 7, 2]
def baseStart_901189 : Nat := 118140960795 + 901189 * 2 ^ 59
def prefixEnd_901189 : Nat := 4983230072969 + 3 ^ 40 * 901189 * 2
def baseEnd_901189 : Nat := 411327215595359846749345

theorem tailTrace_901189 : CollatzResearch.WordTrace tailWord_901189 prefixEnd_901189 411327215595359846749345 := by
  unfold tailWord_901189
  simp only [CollatzResearch.WordTrace]
  refine ⟨32869063132153638672842621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21912708754769092448561747 32869063132153638672842621)
  ·
    refine ⟨12325898674557614502315983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32869063132153638672842621 12325898674557614502315983)
    ·
      refine ⟨18488848011836421753473975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12325898674557614502315983 18488848011836421753473975)
      ·
        refine ⟨27733272017754632630210963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18488848011836421753473975 27733272017754632630210963)
        ·
          refine ⟨41599908026631948945316445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27733272017754632630210963 41599908026631948945316445)
          ·
            refine ⟨15599965509986980854493667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41599908026631948945316445 15599965509986980854493667)
            ·
              refine ⟨23399948264980471281740501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15599965509986980854493667 23399948264980471281740501)
              ·
                refine ⟨548436287460479795665793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23399948264980471281740501 548436287460479795665793)
                ·
                  refine ⟨411327215595359846749345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548436287460479795665793 411327215595359846749345)
                  ·
                    rfl

theorem cell20_901189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_901189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901189 prefixEnd_901189 := by exact prefixLift 901189
  have htrace : WordTrace (prefixWord ++ tailWord_901189) baseStart_901189 baseEnd_901189 := by
    simpa [prefixWord, tailWord_901189, baseEnd_901189] using wordTrace_append hprefix tailTrace_901189
  have hstable : (prefixWord ++ tailWord_901189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901189).length < 2 ^ (prefixWord ++ tailWord_901189).sum := by decide
  have hdescent : baseEnd_901189 < baseStart_901189 := by decide
  rcases family_descends (prefixWord ++ tailWord_901189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901202 : List Nat := [3, 2, 2, 1, 4, 2, 2, 2, 2]
def baseStart_901202 : Nat := 118140960795 + 901202 * 2 ^ 59
def prefixEnd_901202 : Nat := 4983230072969 + 3 ^ 40 * 901202 * 2
def baseEnd_901202 : Nat := 411333149149589579315959

theorem tailTrace_901202 : CollatzResearch.WordTrace tailWord_901202 prefixEnd_901202 411333149149589579315959 := by
  unfold tailWord_901202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217384320276635473266465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21913024854071027928710573 8217384320276635473266465)
  ·
    refine ⟨6163038240207476604949849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8217384320276635473266465 6163038240207476604949849)
    ·
      refine ⟨4622278680155607453712387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6163038240207476604949849 4622278680155607453712387)
      ·
        refine ⟨6933418020233411180568581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622278680155607453712387 6933418020233411180568581)
        ·
          refine ⟨1300015878793764596356609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6933418020233411180568581 1300015878793764596356609)
          ·
            refine ⟨975011909095323447267457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1300015878793764596356609 975011909095323447267457)
            ·
              refine ⟨731258931821492585450593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975011909095323447267457 731258931821492585450593)
              ·
                refine ⟨548444198866119439087945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731258931821492585450593 548444198866119439087945)
                ·
                  refine ⟨411333149149589579315959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548444198866119439087945 411333149149589579315959)
                  ·
                    rfl

theorem cell20_901202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_901202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901202 prefixEnd_901202 := by exact prefixLift 901202
  have htrace : WordTrace (prefixWord ++ tailWord_901202) baseStart_901202 baseEnd_901202 := by
    simpa [prefixWord, tailWord_901202, baseEnd_901202] using wordTrace_append hprefix tailTrace_901202
  have hstable : (prefixWord ++ tailWord_901202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901202).length < 2 ^ (prefixWord ++ tailWord_901202).sum := by decide
  have hdescent : baseEnd_901202 < baseStart_901202 := by decide
  rcases family_descends (prefixWord ++ tailWord_901202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901210 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_901210 : Nat := 118140960795 + 901210 * 2 ^ 59
def prefixEnd_901210 : Nat := 4983230072969 + 3 ^ 40 * 901210 * 2
def baseEnd_901210 : Nat := 411336800567577107049259

theorem tailTrace_901210 : CollatzResearch.WordTrace tailWord_901210 prefixEnd_901210 411336800567577107049259 := by
  unfold tailWord_901210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217457266269389814839271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21913219376718372839571389 8217457266269389814839271)
  ·
    refine ⟨12326185899404084722258907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8217457266269389814839271 12326185899404084722258907)
    ·
      refine ⟨18489278849106127083388361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12326185899404084722258907 18489278849106127083388361)
      ·
        refine ⟨13866959136829595312541271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18489278849106127083388361 13866959136829595312541271)
        ·
          refine ⟨20800438705244392968811907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13866959136829595312541271 20800438705244392968811907)
          ·
            refine ⟨31200658057866589453217861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20800438705244392968811907 31200658057866589453217861)
            ·
              refine ⟨5850123385849985522478349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31200658057866589453217861 5850123385849985522478349)
              ·
                refine ⟨2193796269693744570929381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5850123385849985522478349 2193796269693744570929381)
                ·
                  refine ⟨411336800567577107049259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2193796269693744570929381 411336800567577107049259)
                  ·
                    rfl

theorem cell20_901210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_901210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901210 prefixEnd_901210 := by exact prefixLift 901210
  have htrace : WordTrace (prefixWord ++ tailWord_901210) baseStart_901210 baseEnd_901210 := by
    simpa [prefixWord, tailWord_901210, baseEnd_901210] using wordTrace_append hprefix tailTrace_901210
  have hstable : (prefixWord ++ tailWord_901210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901210).length < 2 ^ (prefixWord ++ tailWord_901210).sum := by decide
  have hdescent : baseEnd_901210 < baseStart_901210 := by decide
  rcases family_descends (prefixWord ++ tailWord_901210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901213 : List Nat := [1, 4, 4, 1, 1, 1, 3, 5]
def baseStart_901213 : Nat := 118140960795 + 901213 * 2 ^ 59
def prefixEnd_901213 : Nat := 4983230072969 + 3 ^ 40 * 901213 * 2
def baseEnd_901213 : Nat := 137112723283107476649749

theorem tailTrace_901213 : CollatzResearch.WordTrace tailWord_901213 prefixEnd_901213 137112723283107476649749 := by
  unfold tailWord_901213
  simp only [CollatzResearch.WordTrace]
  refine ⟨32869938484066690771716293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21913292322711127181144195 32869938484066690771716293)
  ·
    refine ⟨6163113465762504519696805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32869938484066690771716293 6163113465762504519696805)
    ·
      refine ⟨1155583774830469597443151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6163113465762504519696805 1155583774830469597443151)
      ·
        refine ⟨1733375662245704396164727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155583774830469597443151 1733375662245704396164727)
        ·
          refine ⟨2600063493368556594247091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733375662245704396164727 2600063493368556594247091)
          ·
            refine ⟨3900095240052834891370637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600063493368556594247091 3900095240052834891370637)
            ·
              refine ⟨1462535715019813084263989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3900095240052834891370637 1462535715019813084263989)
              ·
                refine ⟨137112723283107476649749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1462535715019813084263989 137112723283107476649749)
                ·
                  rfl

theorem cell20_901213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 5].length) (baseStart_901213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901213 prefixEnd_901213 := by exact prefixLift 901213
  have htrace : WordTrace (prefixWord ++ tailWord_901213) baseStart_901213 baseEnd_901213 := by
    simpa [prefixWord, tailWord_901213, baseEnd_901213] using wordTrace_append hprefix tailTrace_901213
  have hstable : (prefixWord ++ tailWord_901213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901213).length < 2 ^ (prefixWord ++ tailWord_901213).sum := by decide
  have hdescent : baseEnd_901213 < baseStart_901213 := by decide
  rcases family_descends (prefixWord ++ tailWord_901213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901244 : List Nat := [2, 2, 2, 1, 1, 5, 2, 3, 2]
def baseStart_901244 : Nat := 118140960795 + 901244 * 2 ^ 59
def prefixEnd_901244 : Nat := 4983230072969 + 3 ^ 40 * 901244 * 2
def baseEnd_901244 : Nat := 411352319094024099915787

theorem tailTrace_901244 : CollatzResearch.WordTrace tailWord_901244 prefixEnd_901244 411352319094024099915787 := by
  unfold tailWord_901244
  simp only [CollatzResearch.WordTrace]
  refine ⟨16435534573477191533047393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21914046097969588710729857 16435534573477191533047393)
  ·
    refine ⟨12326650930107893649785545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16435534573477191533047393 12326650930107893649785545)
    ·
      refine ⟨9244988197580920237339159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12326650930107893649785545 9244988197580920237339159)
      ·
        refine ⟨13867482296371380356008739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9244988197580920237339159 13867482296371380356008739)
        ·
          refine ⟨20801223444557070534013109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13867482296371380356008739 20801223444557070534013109)
          ·
            refine ⟨1950114697927225362563729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20801223444557070534013109 1950114697927225362563729)
            ·
              refine ⟨1462586023445419021922797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1950114697927225362563729 1462586023445419021922797)
              ·
                refine ⟨548469758792032133221049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1462586023445419021922797 548469758792032133221049)
                ·
                  refine ⟨411352319094024099915787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548469758792032133221049 411352319094024099915787)
                  ·
                    rfl

theorem cell20_901244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_901244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901244 prefixEnd_901244 := by exact prefixLift 901244
  have htrace : WordTrace (prefixWord ++ tailWord_901244) baseStart_901244 baseEnd_901244 := by
    simpa [prefixWord, tailWord_901244, baseEnd_901244] using wordTrace_append hprefix tailTrace_901244
  have hstable : (prefixWord ++ tailWord_901244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901244).length < 2 ^ (prefixWord ++ tailWord_901244).sum := by decide
  have hdescent : baseEnd_901244 < baseStart_901244 := by decide
  rcases family_descends (prefixWord ++ tailWord_901244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901258 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_901258 : Nat := 118140960795 + 901258 * 2 ^ 59
def prefixEnd_901258 : Nat := 4983230072969 + 3 ^ 40 * 901258 * 2
def baseEnd_901258 : Nat := 411358709075502273449063

theorem tailTrace_901258 : CollatzResearch.WordTrace tailWord_901258 prefixEnd_901258 411358709075502273449063 := by
  unfold tailWord_901258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217894942225915864276107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21914386512602442304736285 8217894942225915864276107)
  ·
    refine ⟨12326842413338873796414161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8217894942225915864276107 12326842413338873796414161)
    ·
      refine ⟨9245131810004155347310621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12326842413338873796414161 9245131810004155347310621)
      ·
        refine ⟨3466924428751558255241483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9245131810004155347310621 3466924428751558255241483)
        ·
          refine ⟨5200386643127337382862225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466924428751558255241483 5200386643127337382862225)
          ·
            refine ⟨3900289982345503037146669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5200386643127337382862225 3900289982345503037146669)
            ·
              refine ⟨1462608743379563638930001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3900289982345503037146669 1462608743379563638930001)
              ·
                refine ⟨1096956557534672729197501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462608743379563638930001 1096956557534672729197501)
                ·
                  refine ⟨411358709075502273449063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096956557534672729197501 411358709075502273449063)
                  ·
                    rfl

theorem cell20_901258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_901258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901258 prefixEnd_901258 := by exact prefixLift 901258
  have htrace : WordTrace (prefixWord ++ tailWord_901258) baseStart_901258 baseEnd_901258 := by
    simpa [prefixWord, tailWord_901258, baseEnd_901258] using wordTrace_append hprefix tailTrace_901258
  have hstable : (prefixWord ++ tailWord_901258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901258).length < 2 ^ (prefixWord ++ tailWord_901258).sum := by decide
  have hdescent : baseEnd_901258 < baseStart_901258 := by decide
  rcases family_descends (prefixWord ++ tailWord_901258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901372 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 3]
def baseStart_901372 : Nat := 118140960795 + 901372 * 2 ^ 59
def prefixEnd_901372 : Nat := 4983230072969 + 3 ^ 40 * 901372 * 2
def baseEnd_901372 : Nat := 411410741781824543648597

theorem tailTrace_901372 : CollatzResearch.WordTrace tailWord_901372 prefixEnd_901372 411410741781824543648597 := by
  unfold tailWord_901372
  simp only [CollatzResearch.WordTrace]
  refine ⟨16437868845245330463377185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21917158460327107284502913 16437868845245330463377185)
  ·
    refine ⟨12328401633933997847532889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16437868845245330463377185 12328401633933997847532889)
    ·
      refine ⟨9246301225450498385649667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12328401633933997847532889 9246301225450498385649667)
      ·
        refine ⟨13869451838175747578474501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9246301225450498385649667 13869451838175747578474501)
        ·
          refine ⟨2600522219657952670963969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13869451838175747578474501 2600522219657952670963969)
          ·
            refine ⟨1950391664743464503222977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2600522219657952670963969 1950391664743464503222977)
            ·
              refine ⟨1462793748557598377417233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1950391664743464503222977 1462793748557598377417233)
              ·
                refine ⟨1097095311418198783062925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462793748557598377417233 1097095311418198783062925)
                ·
                  refine ⟨411410741781824543648597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1097095311418198783062925 411410741781824543648597)
                  ·
                    rfl

theorem cell20_901372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_901372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901372 prefixEnd_901372 := by exact prefixLift 901372
  have htrace : WordTrace (prefixWord ++ tailWord_901372) baseStart_901372 baseEnd_901372 := by
    simpa [prefixWord, tailWord_901372, baseEnd_901372] using wordTrace_append hprefix tailTrace_901372
  have hstable : (prefixWord ++ tailWord_901372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901372).length < 2 ^ (prefixWord ++ tailWord_901372).sum := by decide
  have hdescent : baseEnd_901372 < baseStart_901372 := by decide
  rcases family_descends (prefixWord ++ tailWord_901372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901376 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_901376 : Nat := 118140960795 + 901376 * 2 ^ 59
def prefixEnd_901376 : Nat := 4983230072969 + 3 ^ 40 * 901376 * 2
def baseEnd_901376 : Nat := 411412567490818307515247

theorem tailTrace_901376 : CollatzResearch.WordTrace tailWord_901376 prefixEnd_901376 411412567490818307515247 := by
  unfold tailWord_901376
  simp only [CollatzResearch.WordTrace]
  refine ⟨16437941791238084804949991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21917255721650779739933321 16437941791238084804949991)
  ·
    refine ⟨24656912686857127207424987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16437941791238084804949991 24656912686857127207424987)
    ·
      refine ⟨36985369030285690811137481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24656912686857127207424987 36985369030285690811137481)
      ·
        refine ⟨27739026772714268108353111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36985369030285690811137481 27739026772714268108353111)
        ·
          refine ⟨41608540159071402162529667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27739026772714268108353111 41608540159071402162529667)
          ·
            refine ⟨62412810238607103243794501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41608540159071402162529667 62412810238607103243794501)
            ·
              refine ⟨11702401919738831858211469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62412810238607103243794501 11702401919738831858211469)
              ·
                refine ⟨4388400719902061946829301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11702401919738831858211469 4388400719902061946829301)
                ·
                  refine ⟨411412567490818307515247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4388400719902061946829301 411412567490818307515247)
                  ·
                    rfl

theorem cell20_901376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_901376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901376 prefixEnd_901376 := by exact prefixLift 901376
  have htrace : WordTrace (prefixWord ++ tailWord_901376) baseStart_901376 baseEnd_901376 := by
    simpa [prefixWord, tailWord_901376, baseEnd_901376] using wordTrace_append hprefix tailTrace_901376
  have hstable : (prefixWord ++ tailWord_901376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901376).length < 2 ^ (prefixWord ++ tailWord_901376).sum := by decide
  have hdescent : baseEnd_901376 < baseStart_901376 := by decide
  rcases family_descends (prefixWord ++ tailWord_901376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901379 : List Nat := [1, 1, 1, 3, 2, 3, 3, 4, 2]
def baseStart_901379 : Nat := 118140960795 + 901379 * 2 ^ 59
def prefixEnd_901379 : Nat := 4983230072969 + 3 ^ 40 * 901379 * 2
def baseEnd_901379 : Nat := 411413936772563630415235

theorem tailTrace_901379 : CollatzResearch.WordTrace tailWord_901379 prefixEnd_901379 411413936772563630415235 := by
  unfold tailWord_901379
  simp only [CollatzResearch.WordTrace]
  refine ⟨32875993001465301122259191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21917328667643534081506127 32875993001465301122259191)
  ·
    refine ⟨49313989502197951683388787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32875993001465301122259191 49313989502197951683388787)
    ·
      refine ⟨73970984253296927525083181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49313989502197951683388787 73970984253296927525083181)
      ·
        refine ⟨27739119094986347821906193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73970984253296927525083181 27739119094986347821906193)
        ·
          refine ⟨20804339321239760866429645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27739119094986347821906193 20804339321239760866429645)
          ·
            refine ⟨7801627245464910324911117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20804339321239760866429645 7801627245464910324911117)
            ·
              refine ⟨2925610217049341371841669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7801627245464910324911117 2925610217049341371841669)
              ·
                refine ⟨548551915696751507220313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2925610217049341371841669 548551915696751507220313)
                ·
                  refine ⟨411413936772563630415235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548551915696751507220313 411413936772563630415235)
                  ·
                    rfl

theorem cell20_901379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 2].length) (baseStart_901379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901379 prefixEnd_901379 := by exact prefixLift 901379
  have htrace : WordTrace (prefixWord ++ tailWord_901379) baseStart_901379 baseEnd_901379 := by
    simpa [prefixWord, tailWord_901379, baseEnd_901379] using wordTrace_append hprefix tailTrace_901379
  have hstable : (prefixWord ++ tailWord_901379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901379).length < 2 ^ (prefixWord ++ tailWord_901379).sum := by decide
  have hdescent : baseEnd_901379 < baseStart_901379 := by decide
  rcases family_descends (prefixWord ++ tailWord_901379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901393 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 3]
def baseStart_901393 : Nat := 118140960795 + 901393 * 2 ^ 59
def prefixEnd_901393 : Nat := 4983230072969 + 3 ^ 40 * 901393 * 2
def baseEnd_901393 : Nat := 411420326754041803948511

theorem tailTrace_901393 : CollatzResearch.WordTrace tailWord_901393 prefixEnd_901393 411420326754041803948511 := by
  unfold tailWord_901393
  simp only [CollatzResearch.WordTrace]
  refine ⟨32876503623414581513268833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21917669082276387675512555 32876503623414581513268833)
  ·
    refine ⟨24657377717560936134951625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32876503623414581513268833 24657377717560936134951625)
    ·
      refine ⟨18493033288170702101213719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24657377717560936134951625 18493033288170702101213719)
      ·
        refine ⟨27739549932256053151820579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18493033288170702101213719 27739549932256053151820579)
        ·
          refine ⟨41609324898384079727730869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27739549932256053151820579 41609324898384079727730869)
          ·
            refine ⟨3900874209223507474474769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41609324898384079727730869 3900874209223507474474769)
            ·
              refine ⟨2925655656917630605856077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3900874209223507474474769 2925655656917630605856077)
              ·
                refine ⟨1097120871344111477196029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2925655656917630605856077 1097120871344111477196029)
                ·
                  refine ⟨411420326754041803948511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1097120871344111477196029 411420326754041803948511)
                  ·
                    rfl

theorem cell20_901393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_901393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901393 prefixEnd_901393 := by exact prefixLift 901393
  have htrace : WordTrace (prefixWord ++ tailWord_901393) baseStart_901393 baseEnd_901393 := by
    simpa [prefixWord, tailWord_901393, baseEnd_901393] using wordTrace_append hprefix tailTrace_901393
  have hstable : (prefixWord ++ tailWord_901393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901393).length < 2 ^ (prefixWord ++ tailWord_901393).sum := by decide
  have hdescent : baseEnd_901393 < baseStart_901393 := by decide
  rcases family_descends (prefixWord ++ tailWord_901393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901400 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_901400 : Nat := 118140960795 + 901400 * 2 ^ 59
def prefixEnd_901400 : Nat := 4983230072969 + 3 ^ 40 * 901400 * 2
def baseEnd_901400 : Nat := 411423521744780890715149

theorem tailTrace_901400 : CollatzResearch.WordTrace tailWord_901400 prefixEnd_901400 411423521744780890715149 := by
  unfold tailWord_901400
  simp only [CollatzResearch.WordTrace]
  refine ⟨16438379467194610854386827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21917839289592814472515769 16438379467194610854386827)
  ·
    refine ⟨24657569200791916281580241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16438379467194610854386827 24657569200791916281580241)
    ·
      refine ⟨18493176900593937211185181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24657569200791916281580241 18493176900593937211185181)
      ·
        refine ⟨6934941337722726454194443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18493176900593937211185181 6934941337722726454194443)
        ·
          refine ⟨10402412006584089681291665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6934941337722726454194443 10402412006584089681291665)
          ·
            refine ⟨7801809004938067260968749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10402412006584089681291665 7801809004938067260968749)
            ·
              refine ⟨2925678376851775222863281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7801809004938067260968749 2925678376851775222863281)
              ·
                refine ⟨2194258782638831417147461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2925678376851775222863281 2194258782638831417147461)
                ·
                  refine ⟨411423521744780890715149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194258782638831417147461 411423521744780890715149)
                  ·
                    rfl

theorem cell20_901400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_901400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901400 prefixEnd_901400 := by exact prefixLift 901400
  have htrace : WordTrace (prefixWord ++ tailWord_901400) baseStart_901400 baseEnd_901400 := by
    simpa [prefixWord, tailWord_901400, baseEnd_901400] using wordTrace_append hprefix tailTrace_901400
  have hstable : (prefixWord ++ tailWord_901400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901400).length < 2 ^ (prefixWord ++ tailWord_901400).sum := by decide
  have hdescent : baseEnd_901400 < baseStart_901400 := by decide
  rcases family_descends (prefixWord ++ tailWord_901400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901444 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 3]
def baseStart_901444 : Nat := 118140960795 + 901444 * 2 ^ 59
def prefixEnd_901444 : Nat := 4983230072969 + 3 ^ 40 * 901444 * 2
def baseEnd_901444 : Nat := 411443604543712293248303

theorem tailTrace_901444 : CollatzResearch.WordTrace tailWord_901444 prefixEnd_901444 411443604543712293248303 := by
  unfold tailWord_901444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16439181873114908611687693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21918909164153211482250257 16439181873114908611687693)
  ·
    refine ⟨6164693202418090729382885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16439181873114908611687693 6164693202418090729382885)
    ·
      refine ⟨1155879975453392011759291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6164693202418090729382885 1155879975453392011759291)
      ·
        refine ⟨1733819963180088017638937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155879975453392011759291 1733819963180088017638937)
        ·
          refine ⟨1300364972385066013229203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733819963180088017638937 1300364972385066013229203)
          ·
            refine ⟨1950547458577599019843805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300364972385066013229203 1950547458577599019843805)
            ·
              refine ⟨731455296966599632441427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1950547458577599019843805 731455296966599632441427)
              ·
                refine ⟨1097182945449899448662141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731455296966599632441427 1097182945449899448662141)
                ·
                  refine ⟨411443604543712293248303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1097182945449899448662141 411443604543712293248303)
                  ·
                    rfl

theorem cell20_901444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_901444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901444 prefixEnd_901444 := by exact prefixLift 901444
  have htrace : WordTrace (prefixWord ++ tailWord_901444) baseStart_901444 baseEnd_901444 := by
    simpa [prefixWord, tailWord_901444, baseEnd_901444] using wordTrace_append hprefix tailTrace_901444
  have hstable : (prefixWord ++ tailWord_901444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901444).length < 2 ^ (prefixWord ++ tailWord_901444).sum := by decide
  have hdescent : baseEnd_901444 < baseStart_901444 := by decide
  rcases family_descends (prefixWord ++ tailWord_901444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901459 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_901459 : Nat := 118140960795 + 901459 * 2 ^ 59
def prefixEnd_901459 : Nat := 4983230072969 + 3 ^ 40 * 901459 * 2
def baseEnd_901459 : Nat := 411450450952438907748241

theorem tailTrace_901459 : CollatzResearch.WordTrace tailWord_901459 prefixEnd_901459 411450450952438907748241 := by
  unfold tailWord_901459
  simp only [CollatzResearch.WordTrace]
  refine ⟨32878910841175474785171431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21919273894116983190114287 32878910841175474785171431)
  ·
    refine ⟨49318366261763212177757147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32878910841175474785171431 49318366261763212177757147)
    ·
      refine ⟨73977549392644818266635721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49318366261763212177757147 73977549392644818266635721)
      ·
        refine ⟨55483162044483613699976791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73977549392644818266635721 55483162044483613699976791)
        ·
          refine ⟨83224743066725420549965187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55483162044483613699976791 83224743066725420549965187)
          ·
            refine ⟨124837114600088130824947781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83224743066725420549965187 124837114600088130824947781)
            ·
              refine ⟨23406958987516524529677709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124837114600088130824947781 23406958987516524529677709)
              ·
                refine ⟨8777609620318696698629141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23406958987516524529677709 8777609620318696698629141)
                ·
                  refine ⟨411450450952438907748241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8777609620318696698629141 411450450952438907748241)
                  ·
                    rfl

theorem cell20_901459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_901459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901459 prefixEnd_901459 := by exact prefixLift 901459
  have htrace : WordTrace (prefixWord ++ tailWord_901459) baseStart_901459 baseEnd_901459 := by
    simpa [prefixWord, tailWord_901459, baseEnd_901459] using wordTrace_append hprefix tailTrace_901459
  have hstable : (prefixWord ++ tailWord_901459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901459).length < 2 ^ (prefixWord ++ tailWord_901459).sum := by decide
  have hdescent : baseEnd_901459 < baseStart_901459 := by decide
  rcases family_descends (prefixWord ++ tailWord_901459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901468 : List Nat := [2, 2, 4, 3, 1, 2, 1, 3, 2]
def baseStart_901468 : Nat := 118140960795 + 901468 * 2 ^ 59
def prefixEnd_901468 : Nat := 4983230072969 + 3 ^ 40 * 901468 * 2
def baseEnd_901468 : Nat := 411454558797674876448205

theorem tailTrace_901468 : CollatzResearch.WordTrace tailWord_901468 prefixEnd_901468 411454558797674876448205 := by
  unfold tailWord_901468
  simp only [CollatzResearch.WordTrace]
  refine ⟨16439619549071434661124529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21919492732095246214832705 16439619549071434661124529)
  ·
    refine ⟨12329714661803575995843397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16439619549071434661124529 12329714661803575995843397)
    ·
      refine ⟨2311821499088170499220637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12329714661803575995843397 2311821499088170499220637)
      ·
        refine ⟨866933062158063937207739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2311821499088170499220637 866933062158063937207739)
        ·
          refine ⟨1300399593237095905811609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866933062158063937207739 1300399593237095905811609)
          ·
            refine ⟨975299694927821929358707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1300399593237095905811609 975299694927821929358707)
            ·
              refine ⟨1462949542391732894038061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975299694927821929358707 1462949542391732894038061)
              ·
                refine ⟨548606078396899835264273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1462949542391732894038061 548606078396899835264273)
                ·
                  refine ⟨411454558797674876448205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548606078396899835264273 411454558797674876448205)
                  ·
                    rfl

theorem cell20_901468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_901468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901468 prefixEnd_901468 := by exact prefixLift 901468
  have htrace : WordTrace (prefixWord ++ tailWord_901468) baseStart_901468 baseEnd_901468 := by
    simpa [prefixWord, tailWord_901468, baseEnd_901468] using wordTrace_append hprefix tailTrace_901468
  have hstable : (prefixWord ++ tailWord_901468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901468).length < 2 ^ (prefixWord ++ tailWord_901468).sum := by decide
  have hdescent : baseEnd_901468 < baseStart_901468 := by decide
  rcases family_descends (prefixWord ++ tailWord_901468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901493 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 4]
def baseStart_901493 : Nat := 118140960795 + 901493 * 2 ^ 59
def prefixEnd_901493 : Nat := 4983230072969 + 3 ^ 40 * 901493 * 2
def baseEnd_901493 : Nat := 411465969478885900614769

theorem tailTrace_901493 : CollatzResearch.WordTrace tailWord_901493 prefixEnd_901493 411465969478885900614769 := by
  unfold tailWord_901493
  simp only [CollatzResearch.WordTrace]
  refine ⟨32880150923052298591909133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21920100615368199061272755 32880150923052298591909133)
  ·
    refine ⟨12330056596144611971965925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32880150923052298591909133 12330056596144611971965925)
    ·
      refine ⟨2311885611777114744743611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12330056596144611971965925 2311885611777114744743611)
      ·
        refine ⟨3467828417665672117115417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311885611777114744743611 3467828417665672117115417)
        ·
          refine ⟨2600871313249254087836563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3467828417665672117115417 2600871313249254087836563)
          ·
            refine ⟨3901306969873881131754845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600871313249254087836563 3901306969873881131754845)
            ·
              refine ⟨1462990113702705424408067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3901306969873881131754845 1462990113702705424408067)
              ·
                refine ⟨2194485170554058136612101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462990113702705424408067 2194485170554058136612101)
                ·
                  refine ⟨411465969478885900614769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194485170554058136612101 411465969478885900614769)
                  ·
                    rfl

theorem cell20_901493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_901493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901493 prefixEnd_901493 := by exact prefixLift 901493
  have htrace : WordTrace (prefixWord ++ tailWord_901493) baseStart_901493 baseEnd_901493 := by
    simpa [prefixWord, tailWord_901493, baseEnd_901493] using wordTrace_append hprefix tailTrace_901493
  have hstable : (prefixWord ++ tailWord_901493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901493).length < 2 ^ (prefixWord ++ tailWord_901493).sum := by decide
  have hdescent : baseEnd_901493 < baseStart_901493 := by decide
  rcases family_descends (prefixWord ++ tailWord_901493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901542 : List Nat := [20]
def baseStart_901542 : Nat := 118140960795 + 901542 * 2 ^ 59
def prefixEnd_901542 : Nat := 4983230072969 + 3 ^ 40 * 901542 * 2
def baseEnd_901542 : Nat := 62717319679021415635

theorem tailTrace_901542 : CollatzResearch.WordTrace tailWord_901542 prefixEnd_901542 62717319679021415635 := by
  unfold tailWord_901542
  simp only [CollatzResearch.WordTrace]
  refine ⟨62717319679021415635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 20 21921292066583186640295253 62717319679021415635)
  ·
    rfl

theorem cell20_901542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 20].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 20].length) (baseStart_901542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901542 prefixEnd_901542 := by exact prefixLift 901542
  have htrace : WordTrace (prefixWord ++ tailWord_901542) baseStart_901542 baseEnd_901542 := by
    simpa [prefixWord, tailWord_901542, baseEnd_901542] using wordTrace_append hprefix tailTrace_901542
  have hstable : (prefixWord ++ tailWord_901542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901542).length < 2 ^ (prefixWord ++ tailWord_901542).sum := by decide
  have hdescent : baseEnd_901542 < baseStart_901542 := by decide
  rcases family_descends (prefixWord ++ tailWord_901542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901544 : List Nat := [2, 1, 6, 1, 1, 3, 2, 2, 2]
def baseStart_901544 : Nat := 118140960795 + 901544 * 2 ^ 59
def prefixEnd_901544 : Nat := 4983230072969 + 3 ^ 40 * 901544 * 2
def baseEnd_901544 : Nat := 411489247268556389914561

theorem tailTrace_901544 : CollatzResearch.WordTrace tailWord_901544 prefixEnd_901544 411489247268556389914561 := by
  unfold tailWord_901544
  simp only [CollatzResearch.WordTrace]
  refine ⟨16441005522933767151007843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21921340697245022868010457 16441005522933767151007843)
  ·
    refine ⟨24661508284400650726511765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16441005522933767151007843 24661508284400650726511765)
    ·
      refine ⟨1156008200831280502805239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24661508284400650726511765 1156008200831280502805239)
      ·
        refine ⟨1734012301246920754207859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156008200831280502805239 1734012301246920754207859)
        ·
          refine ⟨2601018451870381131311789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734012301246920754207859 2601018451870381131311789)
          ·
            refine ⟨975381919451392924241921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2601018451870381131311789 975381919451392924241921)
            ·
              refine ⟨731536439588544693181441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975381919451392924241921 731536439588544693181441)
              ·
                refine ⟨548652329691408519886081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731536439588544693181441 548652329691408519886081)
                ·
                  refine ⟨411489247268556389914561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548652329691408519886081 411489247268556389914561)
                  ·
                    rfl

theorem cell20_901544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_901544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901544 prefixEnd_901544 := by exact prefixLift 901544
  have htrace : WordTrace (prefixWord ++ tailWord_901544) baseStart_901544 baseEnd_901544 := by
    simpa [prefixWord, tailWord_901544, baseEnd_901544] using wordTrace_append hprefix tailTrace_901544
  have hstable : (prefixWord ++ tailWord_901544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901544).length < 2 ^ (prefixWord ++ tailWord_901544).sum := by decide
  have hdescent : baseEnd_901544 < baseStart_901544 := by decide
  rcases family_descends (prefixWord ++ tailWord_901544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901559 : List Nat := [1, 1, 3, 1, 3, 3, 3, 5]
def baseStart_901559 : Nat := 118140960795 + 901559 * 2 ^ 59
def prefixEnd_901559 : Nat := 4983230072969 + 3 ^ 40 * 901559 * 2
def baseEnd_901559 : Nat := 137165364559094334804833

theorem tailTrace_901559 : CollatzResearch.WordTrace tailWord_901559 prefixEnd_901559 137165364559094334804833 := by
  unfold tailWord_901559
  simp only [CollatzResearch.WordTrace]
  refine ⟨32882558140813191863811731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21921705427208794575874487 32882558140813191863811731)
  ·
    refine ⟨49323837211219787795717597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32882558140813191863811731 49323837211219787795717597)
    ·
      refine ⟨18496438954207420423394099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49323837211219787795717597 18496438954207420423394099)
      ·
        refine ⟨27744658431311130635091149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18496438954207420423394099 27744658431311130635091149)
        ·
          refine ⟨10404246911741673988159181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27744658431311130635091149 10404246911741673988159181)
          ·
            refine ⟨3901592591903127745559693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10404246911741673988159181 3901592591903127745559693)
            ·
              refine ⟨1463097221963672904584885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3901592591903127745559693 1463097221963672904584885)
              ·
                refine ⟨137165364559094334804833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1463097221963672904584885 137165364559094334804833)
                ·
                  rfl

theorem cell20_901559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_901559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901559 prefixEnd_901559 := by exact prefixLift 901559
  have htrace : WordTrace (prefixWord ++ tailWord_901559) baseStart_901559 baseEnd_901559 := by
    simpa [prefixWord, tailWord_901559, baseEnd_901559] using wordTrace_append hprefix tailTrace_901559
  have hstable : (prefixWord ++ tailWord_901559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901559).length < 2 ^ (prefixWord ++ tailWord_901559).sum := by decide
  have hdescent : baseEnd_901559 < baseStart_901559 := by decide
  rcases family_descends (prefixWord ++ tailWord_901559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901576 : List Nat := [2, 1, 3, 1, 3, 3, 3, 4]
def baseStart_901576 : Nat := 118140960795 + 901576 * 2 ^ 59
def prefixEnd_901576 : Nat := 4983230072969 + 3 ^ 40 * 901576 * 2
def baseEnd_901576 : Nat := 137167950980168833615921

theorem tailTrace_901576 : CollatzResearch.WordTrace tailWord_901576 prefixEnd_901576 137167950980168833615921 := by
  unfold tailWord_901576
  simp only [CollatzResearch.WordTrace]
  refine ⟨16441589090875801883590291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21922118787834402511453721 16441589090875801883590291)
  ·
    refine ⟨24662383636313702825385437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16441589090875801883590291 24662383636313702825385437)
    ·
      refine ⟨9248393863617638559519539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24662383636313702825385437 9248393863617638559519539)
      ·
        refine ⟨13872590795426457839279309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9248393863617638559519539 13872590795426457839279309)
        ·
          refine ⟨5202221548284921689729741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13872590795426457839279309 5202221548284921689729741)
          ·
            refine ⟨1950833080606845633648653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5202221548284921689729741 1950833080606845633648653)
            ·
              refine ⟨731562405227567112618245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1950833080606845633648653 731562405227567112618245)
              ·
                refine ⟨137167950980168833615921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 731562405227567112618245 137167950980168833615921)
                ·
                  rfl

theorem cell20_901576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_901576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901576 prefixEnd_901576 := by exact prefixLift 901576
  have htrace : WordTrace (prefixWord ++ tailWord_901576) baseStart_901576 baseEnd_901576 := by
    simpa [prefixWord, tailWord_901576, baseEnd_901576] using wordTrace_append hprefix tailTrace_901576
  have hstable : (prefixWord ++ tailWord_901576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901576).length < 2 ^ (prefixWord ++ tailWord_901576).sum := by decide
  have hdescent : baseEnd_901576 < baseStart_901576 := by decide
  rcases family_descends (prefixWord ++ tailWord_901576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901597 : List Nat := [1, 4, 3, 1, 1, 1, 9]
def baseStart_901597 : Nat := 118140960795 + 901597 * 2 ^ 59
def prefixEnd_901597 : Nat := 4983230072969 + 3 ^ 40 * 901597 * 2
def baseEnd_901597 : Nat := 45723715323635973460853

theorem tailTrace_901597 : CollatzResearch.WordTrace tailWord_901597 prefixEnd_901597 45723715323635973460853 := by
  unfold tailWord_901597
  simp only [CollatzResearch.WordTrace]
  refine ⟨32883944114675524353695045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21922629409783682902463363 32883944114675524353695045)
  ·
    refine ⟨6165739521501660816317821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32883944114675524353695045 6165739521501660816317821)
    ·
      refine ⟨2312152320563122806119183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6165739521501660816317821 2312152320563122806119183)
      ·
        refine ⟨3468228480844684209178775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312152320563122806119183 3468228480844684209178775)
        ·
          refine ⟨5202342721267026313768163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468228480844684209178775 5202342721267026313768163)
          ·
            refine ⟨7803514081900539470652245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202342721267026313768163 7803514081900539470652245)
            ·
              refine ⟨45723715323635973460853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7803514081900539470652245 45723715323635973460853)
              ·
                rfl

theorem cell20_901597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 9].length) (baseStart_901597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901597 prefixEnd_901597 := by exact prefixLift 901597
  have htrace : WordTrace (prefixWord ++ tailWord_901597) baseStart_901597 baseEnd_901597 := by
    simpa [prefixWord, tailWord_901597, baseEnd_901597] using wordTrace_append hprefix tailTrace_901597
  have hstable : (prefixWord ++ tailWord_901597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901597).length < 2 ^ (prefixWord ++ tailWord_901597).sum := by decide
  have hdescent : baseEnd_901597 < baseStart_901597 := by decide
  rcases family_descends (prefixWord ++ tailWord_901597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901607 : List Nat := [1, 1, 5, 2, 1, 1, 1, 6, 2]
def baseStart_901607 : Nat := 118140960795 + 901607 * 2 ^ 59
def prefixEnd_901607 : Nat := 4983230072969 + 3 ^ 40 * 901607 * 2
def baseEnd_901607 : Nat := 411518002185208170814303

theorem tailTrace_901607 : CollatzResearch.WordTrace tailWord_901607 prefixEnd_901607 411518002185208170814303 := by
  unfold tailWord_901607
  simp only [CollatzResearch.WordTrace]
  refine ⟨32884308844639296061559075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21922872563092864041039383 32884308844639296061559075)
  ·
    refine ⟨49326463266958944092338613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32884308844639296061559075 49326463266958944092338613)
    ·
      refine ⟨4624355931277401008656745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49326463266958944092338613 4624355931277401008656745)
      ·
        refine ⟨3468266948458050756492559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4624355931277401008656745 3468266948458050756492559)
        ·
          refine ⟨5202400422687076134738839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468266948458050756492559 5202400422687076134738839)
          ·
            refine ⟨7803600634030614202108259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202400422687076134738839 7803600634030614202108259)
            ·
              refine ⟨11705400951045921303162389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7803600634030614202108259 11705400951045921303162389)
              ·
                refine ⟨548690669580277561085737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11705400951045921303162389 548690669580277561085737)
                ·
                  refine ⟨411518002185208170814303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548690669580277561085737 411518002185208170814303)
                  ·
                    rfl

theorem cell20_901607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 2].length) (baseStart_901607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901607 prefixEnd_901607 := by exact prefixLift 901607
  have htrace : WordTrace (prefixWord ++ tailWord_901607) baseStart_901607 baseEnd_901607 := by
    simpa [prefixWord, tailWord_901607, baseEnd_901607] using wordTrace_append hprefix tailTrace_901607
  have hstable : (prefixWord ++ tailWord_901607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901607).length < 2 ^ (prefixWord ++ tailWord_901607).sum := by decide
  have hdescent : baseEnd_901607 < baseStart_901607 := by decide
  rcases family_descends (prefixWord ++ tailWord_901607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901642 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_901642 : Nat := 118140960795 + 901642 * 2 ^ 59
def prefixEnd_901642 : Nat := 4983230072969 + 3 ^ 40 * 901642 * 2
def baseEnd_901642 : Nat := 411533977138903604647493

theorem tailTrace_901642 : CollatzResearch.WordTrace tailWord_901642 prefixEnd_901642 411533977138903604647493 := by
  unfold tailWord_901642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8221396349878124259770795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21923723599674998026055453 8221396349878124259770795)
  ·
    refine ⟨12332094524817186389656193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8221396349878124259770795 12332094524817186389656193)
    ·
      refine ⟨9249070893612889792242145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12332094524817186389656193 9249070893612889792242145)
      ·
        refine ⟨6936803170209667344181609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9249070893612889792242145 6936803170209667344181609)
        ·
          refine ⟨5202602377657250508136207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6936803170209667344181609 5202602377657250508136207)
          ·
            refine ⟨7803903566485875762204311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202602377657250508136207 7803903566485875762204311)
            ·
              refine ⟨11705855349728813643306467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7803903566485875762204311 11705855349728813643306467)
              ·
                refine ⟨17558783024593220464959701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11705855349728813643306467 17558783024593220464959701)
                ·
                  refine ⟨411533977138903604647493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17558783024593220464959701 411533977138903604647493)
                  ·
                    rfl

theorem cell20_901642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_901642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901642 prefixEnd_901642 := by exact prefixLift 901642
  have htrace : WordTrace (prefixWord ++ tailWord_901642) baseStart_901642 baseEnd_901642 := by
    simpa [prefixWord, tailWord_901642, baseEnd_901642] using wordTrace_append hprefix tailTrace_901642
  have hstable : (prefixWord ++ tailWord_901642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901642).length < 2 ^ (prefixWord ++ tailWord_901642).sum := by decide
  have hdescent : baseEnd_901642 < baseStart_901642 := by decide
  rcases family_descends (prefixWord ++ tailWord_901642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901652 : List Nat := [2, 4, 3, 1, 1, 1, 8]
def baseStart_901652 : Nat := 118140960795 + 901652 * 2 ^ 59
def prefixEnd_901652 : Nat := 4983230072969 + 3 ^ 40 * 901652 * 2
def baseEnd_901652 : Nat := 45726504601265334923791

theorem tailTrace_901652 : CollatzResearch.WordTrace tailWord_901652 prefixEnd_901652 45726504601265334923791 := by
  unfold tailWord_901652
  simp only [CollatzResearch.WordTrace]
  refine ⟨16442975064738134373473605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21923966752984179164631473 16442975064738134373473605)
  ·
    refine ⟨3083057824638400195026301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16442975064738134373473605 3083057824638400195026301)
    ·
      refine ⟨1156146684239400073134863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3083057824638400195026301 1156146684239400073134863)
      ·
        refine ⟨1734220026359100109702295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156146684239400073134863 1734220026359100109702295)
        ·
          refine ⟨2601330039538650164553443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734220026359100109702295 2601330039538650164553443)
          ·
            refine ⟨3901995059307975246830165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601330039538650164553443 3901995059307975246830165)
            ·
              refine ⟨45726504601265334923791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3901995059307975246830165 45726504601265334923791)
              ·
                rfl

theorem cell20_901652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 8].length) (baseStart_901652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901652 prefixEnd_901652 := by exact prefixLift 901652
  have htrace : WordTrace (prefixWord ++ tailWord_901652) baseStart_901652 baseEnd_901652 := by
    simpa [prefixWord, tailWord_901652, baseEnd_901652] using wordTrace_append hprefix tailTrace_901652
  have hstable : (prefixWord ++ tailWord_901652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901652).length < 2 ^ (prefixWord ++ tailWord_901652).sum := by decide
  have hdescent : baseEnd_901652 < baseStart_901652 := by decide
  rcases family_descends (prefixWord ++ tailWord_901652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901687 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_901687 : Nat := 118140960795 + 901687 * 2 ^ 59
def prefixEnd_901687 : Nat := 4983230072969 + 3 ^ 40 * 901687 * 2
def baseEnd_901687 : Nat := 411554516365083448147309

theorem tailTrace_901687 : CollatzResearch.WordTrace tailWord_901687 prefixEnd_901687 411554516365083448147309 := by
  unfold tailWord_901687
  simp only [CollatzResearch.WordTrace]
  refine ⟨32887226684349469724471315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21924817789566313149647543 32887226684349469724471315)
  ·
    refine ⟨49330840026524204586706973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32887226684349469724471315 49330840026524204586706973)
    ·
      refine ⟨18499065009946576720015115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49330840026524204586706973 18499065009946576720015115)
      ·
        refine ⟨27748597514919865080022673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18499065009946576720015115 27748597514919865080022673)
        ·
          refine ⟨20811448136189898810017005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27748597514919865080022673 20811448136189898810017005)
          ·
            refine ⟨7804293051071212053756377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20811448136189898810017005 7804293051071212053756377)
            ·
              refine ⟨5853219788303409040317283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7804293051071212053756377 5853219788303409040317283)
              ·
                refine ⟨8779829682455113560475925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853219788303409040317283 8779829682455113560475925)
                ·
                  refine ⟨411554516365083448147309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8779829682455113560475925 411554516365083448147309)
                  ·
                    rfl

theorem cell20_901687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_901687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901687 prefixEnd_901687 := by exact prefixLift 901687
  have htrace : WordTrace (prefixWord ++ tailWord_901687) baseStart_901687 baseEnd_901687 := by
    simpa [prefixWord, tailWord_901687, baseEnd_901687] using wordTrace_append hprefix tailTrace_901687
  have hstable : (prefixWord ++ tailWord_901687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901687).length < 2 ^ (prefixWord ++ tailWord_901687).sum := by decide
  have hdescent : baseEnd_901687 < baseStart_901687 := by decide
  rcases family_descends (prefixWord ++ tailWord_901687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901742 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_901742 : Nat := 118140960795 + 901742 * 2 ^ 59
def prefixEnd_901742 : Nat := 4983230072969 + 3 ^ 40 * 901742 * 2
def baseEnd_901742 : Nat := 411579619863747701313751

theorem tailTrace_901742 : CollatzResearch.WordTrace tailWord_901742 prefixEnd_901742 411579619863747701313751 := by
  unfold tailWord_901742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4111154087393776764715435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21926155132766809411815653 4111154087393776764715435)
  ·
    refine ⟨6166731131090665147073153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4111154087393776764715435 6166731131090665147073153)
    ·
      refine ⟨4625048348317998860304865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6166731131090665147073153 4625048348317998860304865)
      ·
        refine ⟨3468786261238499145228649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4625048348317998860304865 3468786261238499145228649)
        ·
          refine ⟨2601589695928874358921487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3468786261238499145228649 2601589695928874358921487)
          ·
            refine ⟨3902384543893311538382231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601589695928874358921487 3902384543893311538382231)
            ·
              refine ⟨5853576815839967307573347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3902384543893311538382231 5853576815839967307573347)
              ·
                refine ⟨8780365223759950961360021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853576815839967307573347 8780365223759950961360021)
                ·
                  refine ⟨411579619863747701313751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8780365223759950961360021 411579619863747701313751)
                  ·
                    rfl

theorem cell20_901742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_901742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901742 prefixEnd_901742 := by exact prefixLift 901742
  have htrace : WordTrace (prefixWord ++ tailWord_901742) baseStart_901742 baseEnd_901742 := by
    simpa [prefixWord, tailWord_901742, baseEnd_901742] using wordTrace_append hprefix tailTrace_901742
  have hstable : (prefixWord ++ tailWord_901742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901742).length < 2 ^ (prefixWord ++ tailWord_901742).sum := by decide
  have hdescent : baseEnd_901742 < baseStart_901742 := by decide
  rcases family_descends (prefixWord ++ tailWord_901742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901762 : List Nat := [3, 4, 3, 1, 1, 1, 7]
def baseStart_901762 : Nat := 118140960795 + 901762 * 2 ^ 59
def prefixEnd_901762 : Nat := 4983230072969 + 3 ^ 40 * 901762 * 2
def baseEnd_901762 : Nat := 45732083156524057849667

theorem tailTrace_901762 : CollatzResearch.WordTrace tailWord_901762 prefixEnd_901762 45732083156524057849667 := by
  unfold tailWord_901762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8222490539769439383362885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21926641439385171688967693 8222490539769439383362885)
  ·
    refine ⟨1541716976206769884380541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8222490539769439383362885 1541716976206769884380541)
    ·
      refine ⟨578143866077538706642703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1541716976206769884380541 578143866077538706642703)
      ·
        refine ⟨867215799116308059964055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578143866077538706642703 867215799116308059964055)
        ·
          refine ⟨1300823698674462089946083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867215799116308059964055 1300823698674462089946083)
          ·
            refine ⟨1951235548011693134919125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300823698674462089946083 1951235548011693134919125)
            ·
              refine ⟨45732083156524057849667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1951235548011693134919125 45732083156524057849667)
              ·
                rfl

theorem cell20_901762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 7].length) (baseStart_901762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901762 prefixEnd_901762 := by exact prefixLift 901762
  have htrace : WordTrace (prefixWord ++ tailWord_901762) baseStart_901762 baseEnd_901762 := by
    simpa [prefixWord, tailWord_901762, baseEnd_901762] using wordTrace_append hprefix tailTrace_901762
  have hstable : (prefixWord ++ tailWord_901762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901762).length < 2 ^ (prefixWord ++ tailWord_901762).sum := by decide
  have hdescent : baseEnd_901762 < baseStart_901762 := by decide
  rcases family_descends (prefixWord ++ tailWord_901762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901832 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_901832 : Nat := 118140960795 + 901832 * 2 ^ 59
def prefixEnd_901832 : Nat := 4983230072969 + 3 ^ 40 * 901832 * 2
def baseEnd_901832 : Nat := 411620698316107388313383

theorem tailTrace_901832 : CollatzResearch.WordTrace tailWord_901832 prefixEnd_901832 411620698316107388313383 := by
  unfold tailWord_901832
  simp only [CollatzResearch.WordTrace]
  refine ⟨16446257634412079744249875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21928343512549439658999833 16446257634412079744249875)
  ·
    refine ⟨24669386451618119616374813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16446257634412079744249875 24669386451618119616374813)
    ·
      refine ⟨9251019919356794856140555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24669386451618119616374813 9251019919356794856140555)
      ·
        refine ⟨13876529879035192284210833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9251019919356794856140555 13876529879035192284210833)
        ·
          refine ⟨10407397409276394213158125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13876529879035192284210833 10407397409276394213158125)
          ·
            refine ⟨3902774028478647829934297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10407397409276394213158125 3902774028478647829934297)
            ·
              refine ⟨2927080521358985872450723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3902774028478647829934297 2927080521358985872450723)
              ·
                refine ⟨4390620782038478808676085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927080521358985872450723 4390620782038478808676085)
                ·
                  refine ⟨411620698316107388313383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4390620782038478808676085 411620698316107388313383)
                  ·
                    rfl

theorem cell20_901832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_901832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901832 prefixEnd_901832 := by exact prefixLift 901832
  have htrace : WordTrace (prefixWord ++ tailWord_901832) baseStart_901832 baseEnd_901832 := by
    simpa [prefixWord, tailWord_901832, baseEnd_901832] using wordTrace_append hprefix tailTrace_901832
  have hstable : (prefixWord ++ tailWord_901832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901832).length < 2 ^ (prefixWord ++ tailWord_901832).sum := by decide
  have hdescent : baseEnd_901832 < baseStart_901832 := by decide
  rcases family_descends (prefixWord ++ tailWord_901832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901842 : List Nat := [3, 2, 2, 2, 3, 1, 2, 5]
def baseStart_901842 : Nat := 118140960795 + 901842 * 2 ^ 59
def prefixEnd_901842 : Nat := 4983230072969 + 3 ^ 40 * 901842 * 2
def baseEnd_901842 : Nat := 137208420862863932660003

theorem tailTrace_901842 : CollatzResearch.WordTrace tailWord_901842 prefixEnd_901842 137208420862863932660003 := by
  unfold tailWord_901842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8223219999696982799090945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21928586665858620797575853 8223219999696982799090945)
  ·
    refine ⟨6167414999772737099318209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8223219999696982799090945 6167414999772737099318209)
    ·
      refine ⟨4625561249829552824488657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6167414999772737099318209 4625561249829552824488657)
      ·
        refine ⟨3469170937372164618366493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4625561249829552824488657 3469170937372164618366493)
        ·
          refine ⟨1300939101514561731887435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3469170937372164618366493 1300939101514561731887435)
          ·
            refine ⟨1951408652271842597831153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300939101514561731887435 1951408652271842597831153)
            ·
              refine ⟨1463556489203881948373365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951408652271842597831153 1463556489203881948373365)
              ·
                refine ⟨137208420862863932660003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1463556489203881948373365 137208420862863932660003)
                ·
                  rfl

theorem cell20_901842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_901842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901842 prefixEnd_901842 := by exact prefixLift 901842
  have htrace : WordTrace (prefixWord ++ tailWord_901842) baseStart_901842 baseEnd_901842 := by
    simpa [prefixWord, tailWord_901842, baseEnd_901842] using wordTrace_append hprefix tailTrace_901842
  have hstable : (prefixWord ++ tailWord_901842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901842).length < 2 ^ (prefixWord ++ tailWord_901842).sum := by decide
  have hdescent : baseEnd_901842 < baseStart_901842 := by decide
  rcases family_descends (prefixWord ++ tailWord_901842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901884 : List Nat := [2, 2, 2, 1, 3, 10]
def baseStart_901884 : Nat := 118140960795 + 901884 * 2 ^ 59
def prefixEnd_901884 : Nat := 4983230072969 + 3 ^ 40 * 901884 * 2
def baseEnd_901884 : Nat := 15246090093815789577031

theorem tailTrace_901884 : CollatzResearch.WordTrace tailWord_901884 prefixEnd_901884 15246090093815789577031 := by
  unfold tailWord_901884
  simp only [CollatzResearch.WordTrace]
  refine ⟨16447205932317886184696353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21929607909757181579595137 16447205932317886184696353)
  ·
    refine ⟨12335404449238414638522265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16447205932317886184696353 12335404449238414638522265)
    ·
      refine ⟨9251553336928810978891699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12335404449238414638522265 9251553336928810978891699)
      ·
        refine ⟨13877330005393216468337549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9251553336928810978891699 13877330005393216468337549)
        ·
          refine ⟨5203998752022456175626581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13877330005393216468337549 5203998752022456175626581)
          ·
            refine ⟨15246090093815789577031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5203998752022456175626581 15246090093815789577031)
            ·
              rfl

theorem cell20_901884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 10].length) (baseStart_901884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901884 prefixEnd_901884 := by exact prefixLift 901884
  have htrace : WordTrace (prefixWord ++ tailWord_901884) baseStart_901884 baseEnd_901884 := by
    simpa [prefixWord, tailWord_901884, baseEnd_901884] using wordTrace_append hprefix tailTrace_901884
  have hstable : (prefixWord ++ tailWord_901884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901884).length < 2 ^ (prefixWord ++ tailWord_901884).sum := by decide
  have hdescent : baseEnd_901884 < baseStart_901884 := by decide
  rcases family_descends (prefixWord ++ tailWord_901884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901890 : List Nat := [3, 4, 1, 1, 1, 3, 1, 4, 2]
def baseStart_901890 : Nat := 118140960795 + 901890 * 2 ^ 59
def prefixEnd_901890 : Nat := 4983230072969 + 3 ^ 40 * 901890 * 2
def baseEnd_901890 : Nat := 411647171096516964379813

theorem tailTrace_901890 : CollatzResearch.WordTrace tailWord_901890 prefixEnd_901890 411647171096516964379813 := by
  unfold tailWord_901890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8223657675653508848527781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21929753801742690262740749 8223657675653508848527781)
  ·
    refine ⟨1541935814185032909098959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8223657675653508848527781 1541935814185032909098959)
    ·
      refine ⟨2312903721277549363648439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1541935814185032909098959 2312903721277549363648439)
      ·
        refine ⟨3469355581916324045472659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312903721277549363648439 3469355581916324045472659)
        ·
          refine ⟨5204033372874486068208989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469355581916324045472659 5204033372874486068208989)
          ·
            refine ⟨1951512514827932275578371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5204033372874486068208989 1951512514827932275578371)
            ·
              refine ⟨2927268772241898413367557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951512514827932275578371 2927268772241898413367557)
              ·
                refine ⟨548862894795355952506417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2927268772241898413367557 548862894795355952506417)
                ·
                  refine ⟨411647171096516964379813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548862894795355952506417 411647171096516964379813)
                  ·
                    rfl

theorem cell20_901890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_901890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901890 prefixEnd_901890 := by exact prefixLift 901890
  have htrace : WordTrace (prefixWord ++ tailWord_901890) baseStart_901890 baseEnd_901890 := by
    simpa [prefixWord, tailWord_901890, baseEnd_901890] using wordTrace_append hprefix tailTrace_901890
  have hstable : (prefixWord ++ tailWord_901890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901890).length < 2 ^ (prefixWord ++ tailWord_901890).sum := by decide
  have hdescent : baseEnd_901890 < baseStart_901890 := by decide
  rcases family_descends (prefixWord ++ tailWord_901890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901929 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_901929 : Nat := 118140960795 + 901929 * 2 ^ 59
def prefixEnd_901929 : Nat := 4983230072969 + 3 ^ 40 * 901929 * 2
def baseEnd_901929 : Nat := 411664971759206162079653

theorem tailTrace_901929 : CollatzResearch.WordTrace tailWord_901929 prefixEnd_901929 411664971759206162079653 := by
  unfold tailWord_901929
  simp only [CollatzResearch.WordTrace]
  refine ⟨32896053149472745054780841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21930702099648496703187227 32896053149472745054780841)
  ·
    refine ⟨24672039862104558791085631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32896053149472745054780841 24672039862104558791085631)
    ·
      refine ⟨37008059793156838186628447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24672039862104558791085631 37008059793156838186628447)
      ·
        refine ⟨55512089689735257279942671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37008059793156838186628447 55512089689735257279942671)
        ·
          refine ⟨83268134534602885919914007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55512089689735257279942671 83268134534602885919914007)
          ·
            refine ⟨124902201801904328879871011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83268134534602885919914007 124902201801904328879871011)
            ·
              refine ⟨187353302702856493319806517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124902201801904328879871011 187353302702856493319806517)
              ·
                refine ⟨17564372128392796248731861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187353302702856493319806517 17564372128392796248731861)
                ·
                  refine ⟨411664971759206162079653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17564372128392796248731861 411664971759206162079653)
                  ·
                    rfl

theorem cell20_901929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_901929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901929 prefixEnd_901929 := by exact prefixLift 901929
  have htrace : WordTrace (prefixWord ++ tailWord_901929) baseStart_901929 baseEnd_901929 := by
    simpa [prefixWord, tailWord_901929, baseEnd_901929] using wordTrace_append hprefix tailTrace_901929
  have hstable : (prefixWord ++ tailWord_901929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901929).length < 2 ^ (prefixWord ++ tailWord_901929).sum := by decide
  have hdescent : baseEnd_901929 < baseStart_901929 := by decide
  rcases family_descends (prefixWord ++ tailWord_901929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901942 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_901942 : Nat := 118140960795 + 901942 * 2 ^ 59
def prefixEnd_901942 : Nat := 4983230072969 + 3 ^ 40 * 901942 * 2
def baseEnd_901942 : Nat := 411670905313435894646267

theorem tailTrace_901942 : CollatzResearch.WordTrace tailWord_901942 prefixEnd_901942 411670905313435894646267 := by
  unfold tailWord_901942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2056032956151603017187755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21931018198950432183336053 2056032956151603017187755)
  ·
    refine ⟨3084049434227404525781633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2056032956151603017187755 3084049434227404525781633)
    ·
      refine ⟨2313037075670553394336225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3084049434227404525781633 2313037075670553394336225)
      ·
        refine ⟨1734777806752915045752169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2313037075670553394336225 1734777806752915045752169)
        ·
          refine ⟨1301083355064686284314127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1734777806752915045752169 1301083355064686284314127)
          ·
            refine ⟨1951625032597029426471191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301083355064686284314127 1951625032597029426471191)
            ·
              refine ⟨2927437548895544139706787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951625032597029426471191 2927437548895544139706787)
              ·
                refine ⟨4391156323343316209560181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927437548895544139706787 4391156323343316209560181)
                ·
                  refine ⟨411670905313435894646267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4391156323343316209560181 411670905313435894646267)
                  ·
                    rfl

theorem cell20_901942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_901942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901942 prefixEnd_901942 := by exact prefixLift 901942
  have htrace : WordTrace (prefixWord ++ tailWord_901942) baseStart_901942 baseEnd_901942 := by
    simpa [prefixWord, tailWord_901942, baseEnd_901942] using wordTrace_append hprefix tailTrace_901942
  have hstable : (prefixWord ++ tailWord_901942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901942).length < 2 ^ (prefixWord ++ tailWord_901942).sum := by decide
  have hdescent : baseEnd_901942 < baseStart_901942 := by decide
  rcases family_descends (prefixWord ++ tailWord_901942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901949 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 4]
def baseStart_901949 : Nat := 118140960795 + 901949 * 2 ^ 59
def prefixEnd_901949 : Nat := 4983230072969 + 3 ^ 40 * 901949 * 2
def baseEnd_901949 : Nat := 411674100304174981412905

theorem tailTrace_901949 : CollatzResearch.WordTrace tailWord_901949 prefixEnd_901949 411674100304174981412905 := by
  unfold tailWord_901949
  simp only [CollatzResearch.WordTrace]
  refine ⟨32896782609400288470508901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21931188406266858980339267 32896782609400288470508901)
  ·
    refine ⟨6168146739262554088220419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32896782609400288470508901 6168146739262554088220419)
    ·
      refine ⟨9252220108893831132330629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6168146739262554088220419 9252220108893831132330629)
      ·
        refine ⟨1734791270417593337311993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9252220108893831132330629 1734791270417593337311993)
        ·
          refine ⟨1301093452813195002983995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1734791270417593337311993 1301093452813195002983995)
          ·
            refine ⟨1951640179219792504475993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301093452813195002983995 1951640179219792504475993)
            ·
              refine ⟨1463730134414844378356995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951640179219792504475993 1463730134414844378356995)
              ·
                refine ⟨2195595201622266567535493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463730134414844378356995 2195595201622266567535493)
                ·
                  refine ⟨411674100304174981412905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2195595201622266567535493 411674100304174981412905)
                  ·
                    rfl

theorem cell20_901949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_901949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901949 prefixEnd_901949 := by exact prefixLift 901949
  have htrace : WordTrace (prefixWord ++ tailWord_901949) baseStart_901949 baseEnd_901949 := by
    simpa [prefixWord, tailWord_901949, baseEnd_901949] using wordTrace_append hprefix tailTrace_901949
  have hstable : (prefixWord ++ tailWord_901949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901949).length < 2 ^ (prefixWord ++ tailWord_901949).sum := by decide
  have hdescent : baseEnd_901949 < baseStart_901949 := by decide
  rcases family_descends (prefixWord ++ tailWord_901949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901960 : List Nat := [2, 1, 3, 1, 1, 3, 2, 7]
def baseStart_901960 : Nat := 118140960795 + 901960 * 2 ^ 59
def prefixEnd_901960 : Nat := 4983230072969 + 3 ^ 40 * 901960 * 2
def baseEnd_901960 : Nat := 137226373667969277348731

theorem tailTrace_901960 : CollatzResearch.WordTrace tailWord_901960 prefixEnd_901960 137226373667969277348731 := by
  unfold tailWord_901960
  simp only [CollatzResearch.WordTrace]
  refine ⟨16448591906180218674579667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21931455874906958232772889 16448591906180218674579667)
  ·
    refine ⟨24672887859270328011869501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16448591906180218674579667 24672887859270328011869501)
    ·
      refine ⟨9252332947226373004451063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24672887859270328011869501 9252332947226373004451063)
      ·
        refine ⟨13878499420839559506676595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9252332947226373004451063 13878499420839559506676595)
        ·
          refine ⟨20817749131259339260014893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13878499420839559506676595 20817749131259339260014893)
          ·
            refine ⟨7806655924222252222505585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20817749131259339260014893 7806655924222252222505585)
            ·
              refine ⟨5854991943166689166879189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7806655924222252222505585 5854991943166689166879189)
              ·
                refine ⟨137226373667969277348731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5854991943166689166879189 137226373667969277348731)
                ·
                  rfl

theorem cell20_901960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_901960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901960 prefixEnd_901960 := by exact prefixLift 901960
  have htrace : WordTrace (prefixWord ++ tailWord_901960) baseStart_901960 baseEnd_901960 := by
    simpa [prefixWord, tailWord_901960, baseEnd_901960] using wordTrace_append hprefix tailTrace_901960
  have hstable : (prefixWord ++ tailWord_901960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901960).length < 2 ^ (prefixWord ++ tailWord_901960).sum := by decide
  have hdescent : baseEnd_901960 < baseStart_901960 := by decide
  rcases family_descends (prefixWord ++ tailWord_901960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901977 : List Nat := [1, 2, 1, 2, 2, 4, 4, 4]
def baseStart_901977 : Nat := 118140960795 + 901977 * 2 ^ 59
def prefixEnd_901977 : Nat := 4983230072969 + 3 ^ 40 * 901977 * 2
def baseEnd_901977 : Nat := 137228960089043776159819

theorem tailTrace_901977 : CollatzResearch.WordTrace tailWord_901977 prefixEnd_901977 137228960089043776159819 := by
  unfold tailWord_901977
  simp only [CollatzResearch.WordTrace]
  refine ⟨32897803853298849252528185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21931869235532566168352123 32897803853298849252528185)
  ·
    refine ⟨24673352889974136939396139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32897803853298849252528185 24673352889974136939396139)
    ·
      refine ⟨37010029334961205409094209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24673352889974136939396139 37010029334961205409094209)
      ·
        refine ⟨27757522001220904056820657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37010029334961205409094209 27757522001220904056820657)
        ·
          refine ⟨20818141500915678042615493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27757522001220904056820657 20818141500915678042615493)
          ·
            refine ⟨3903401531421689632990405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20818141500915678042615493 3903401531421689632990405)
            ·
              refine ⟨731887787141566806185701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3903401531421689632990405 731887787141566806185701)
              ·
                refine ⟨137228960089043776159819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 731887787141566806185701 137228960089043776159819)
                ·
                  rfl

theorem cell20_901977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 4].length) (baseStart_901977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901977 prefixEnd_901977 := by exact prefixLift 901977
  have htrace : WordTrace (prefixWord ++ tailWord_901977) baseStart_901977 baseEnd_901977 := by
    simpa [prefixWord, tailWord_901977, baseEnd_901977] using wordTrace_append hprefix tailTrace_901977
  have hstable : (prefixWord ++ tailWord_901977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901977).length < 2 ^ (prefixWord ++ tailWord_901977).sum := by decide
  have hdescent : baseEnd_901977 < baseStart_901977 := by decide
  rcases family_descends (prefixWord ++ tailWord_901977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901987 : List Nat := [1, 1, 1, 5, 3, 1, 3, 3, 2]
def baseStart_901987 : Nat := 118140960795 + 901987 * 2 ^ 59
def prefixEnd_901987 : Nat := 4983230072969 + 3 ^ 40 * 901987 * 2
def baseEnd_901987 : Nat := 411691444539615738146083

theorem tailTrace_901987 : CollatzResearch.WordTrace tailWord_901987 prefixEnd_901987 411691444539615738146083 := by
  unfold tailWord_901987
  simp only [CollatzResearch.WordTrace]
  refine ⟨32898168583262620960392215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21932112388841747306928143 32898168583262620960392215)
  ·
    refine ⟨49347252874893931440588323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32898168583262620960392215 49347252874893931440588323)
    ·
      refine ⟨74020879312340897160882485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49347252874893931440588323 74020879312340897160882485)
      ·
        refine ⟨6939457435531959108832733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74020879312340897160882485 6939457435531959108832733)
        ·
          refine ⟨2602296538324484665812275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6939457435531959108832733 2602296538324484665812275)
          ·
            refine ⟨3903444807486726998718413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602296538324484665812275 3903444807486726998718413)
            ·
              refine ⟨1463791802807522624519405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3903444807486726998718413 1463791802807522624519405)
              ·
                refine ⟨548921926052820984194777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1463791802807522624519405 548921926052820984194777)
                ·
                  refine ⟨411691444539615738146083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548921926052820984194777 411691444539615738146083)
                  ·
                    rfl

theorem cell20_901987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 2].length) (baseStart_901987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_901987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_901987 prefixEnd_901987 := by exact prefixLift 901987
  have htrace : WordTrace (prefixWord ++ tailWord_901987) baseStart_901987 baseEnd_901987 := by
    simpa [prefixWord, tailWord_901987, baseEnd_901987] using wordTrace_append hprefix tailTrace_901987
  have hstable : (prefixWord ++ tailWord_901987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901987).length < 2 ^ (prefixWord ++ tailWord_901987).sum := by decide
  have hdescent : baseEnd_901987 < baseStart_901987 := by decide
  rcases family_descends (prefixWord ++ tailWord_901987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902014 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_902014 : Nat := 118140960795 + 902014 * 2 ^ 59
def prefixEnd_902014 : Nat := 4983230072969 + 3 ^ 40 * 902014 * 2
def baseEnd_902014 : Nat := 411703768075323644245973

theorem tailTrace_902014 : CollatzResearch.WordTrace tailWord_902014 prefixEnd_902014 411703768075323644245973 := by
  unfold tailWord_902014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4112394169270600571453137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21932768902776536381083397 4112394169270600571453137)
  ·
    refine ⟨3084295626952950428589853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4112394169270600571453137 3084295626952950428589853)
    ·
      refine ⟨1156610860107356410721195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3084295626952950428589853 1156610860107356410721195)
      ·
        refine ⟨1734916290161034616081793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156610860107356410721195 1734916290161034616081793)
        ·
          refine ⟨1301187217620775962061345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1734916290161034616081793 1301187217620775962061345)
          ·
            refine ⟨975890413215581971546009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301187217620775962061345 975890413215581971546009)
            ·
              refine ⟨731917809911686478659507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975890413215581971546009 731917809911686478659507)
              ·
                refine ⟨1097876714867529717989261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731917809911686478659507 1097876714867529717989261)
                ·
                  refine ⟨411703768075323644245973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1097876714867529717989261 411703768075323644245973)
                  ·
                    rfl

theorem cell20_902014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_902014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902014 prefixEnd_902014 := by exact prefixLift 902014
  have htrace : WordTrace (prefixWord ++ tailWord_902014) baseStart_902014 baseEnd_902014 := by
    simpa [prefixWord, tailWord_902014, baseEnd_902014] using wordTrace_append hprefix tailTrace_902014
  have hstable : (prefixWord ++ tailWord_902014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902014).length < 2 ^ (prefixWord ++ tailWord_902014).sum := by decide
  have hdescent : baseEnd_902014 < baseStart_902014 := by decide
  rcases family_descends (prefixWord ++ tailWord_902014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902091 : List Nat := [1, 1, 1, 1, 3, 6, 3, 4]
def baseStart_902091 : Nat := 118140960795 + 902091 * 2 ^ 59
def prefixEnd_902091 : Nat := 4983230072969 + 3 ^ 40 * 902091 * 2
def baseEnd_902091 : Nat := 137246304324484532892997

theorem tailTrace_902091 : CollatzResearch.WordTrace tailWord_902091 prefixEnd_902091 137246304324484532892997 := by
  unfold tailWord_902091
  simp only [CollatzResearch.WordTrace]
  refine ⟨32901961774885846722178127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21934641183257231148118751 32901961774885846722178127)
  ·
    refine ⟨49352942662328770083267191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32901961774885846722178127 49352942662328770083267191)
    ·
      refine ⟨74029413993493155124900787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49352942662328770083267191 74029413993493155124900787)
      ·
        refine ⟨111044120990239732687351181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74029413993493155124900787 111044120990239732687351181)
        ·
          refine ⟨41641545371339899757756693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111044120990239732687351181 41641545371339899757756693)
          ·
            refine ⟨1951947439281557801144845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41641545371339899757756693 1951947439281557801144845)
            ·
              refine ⟨731980289730584175429317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1951947439281557801144845 731980289730584175429317)
              ·
                refine ⟨137246304324484532892997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 731980289730584175429317 137246304324484532892997)
                ·
                  rfl

theorem cell20_902091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 4].length) (baseStart_902091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902091 prefixEnd_902091 := by exact prefixLift 902091
  have htrace : WordTrace (prefixWord ++ tailWord_902091) baseStart_902091 baseEnd_902091 := by
    simpa [prefixWord, tailWord_902091, baseEnd_902091] using wordTrace_append hprefix tailTrace_902091
  have hstable : (prefixWord ++ tailWord_902091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902091).length < 2 ^ (prefixWord ++ tailWord_902091).sum := by decide
  have hdescent : baseEnd_902091 < baseStart_902091 := by decide
  rcases family_descends (prefixWord ++ tailWord_902091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902122 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_902122 : Nat := 118140960795 + 902122 * 2 ^ 59
def prefixEnd_902122 : Nat := 4983230072969 + 3 ^ 40 * 902122 * 2
def baseEnd_902122 : Nat := 411753062218155268645531

theorem tailTrace_902122 : CollatzResearch.WordTrace tailWord_902122 prefixEnd_902122 411753062218155268645531 := by
  unfold tailWord_902122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8225773109443384754139155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21935394958515692677704413 8225773109443384754139155)
  ·
    refine ⟨12338659664165077131208733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8225773109443384754139155 12338659664165077131208733)
    ·
      refine ⟨4626997374061903924203275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12338659664165077131208733 4626997374061903924203275)
      ·
        refine ⟨6940496061092855886304913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4626997374061903924203275 6940496061092855886304913)
        ·
          refine ⟨5205372045819641914728685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6940496061092855886304913 5205372045819641914728685)
          ·
            refine ⟨1952014517182365718023257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5205372045819641914728685 1952014517182365718023257)
            ·
              refine ⟨1464010887886774288517443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1952014517182365718023257 1464010887886774288517443)
              ·
                refine ⟨2196016331830161432776165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464010887886774288517443 2196016331830161432776165)
                ·
                  refine ⟨411753062218155268645531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2196016331830161432776165 411753062218155268645531)
                  ·
                    rfl

theorem cell20_902122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_902122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902122 prefixEnd_902122 := by exact prefixLift 902122
  have htrace : WordTrace (prefixWord ++ tailWord_902122) baseStart_902122 baseEnd_902122 := by
    simpa [prefixWord, tailWord_902122, baseEnd_902122] using wordTrace_append hprefix tailTrace_902122
  have hstable : (prefixWord ++ tailWord_902122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902122).length < 2 ^ (prefixWord ++ tailWord_902122).sum := by decide
  have hdescent : baseEnd_902122 < baseStart_902122 := by decide
  rcases family_descends (prefixWord ++ tailWord_902122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902142 : List Nat := [4, 2, 2, 2, 3, 1, 2, 4]
def baseStart_902142 : Nat := 118140960795 + 902142 * 2 ^ 59
def prefixEnd_902142 : Nat := 4983230072969 + 3 ^ 40 * 902142 * 2
def baseEnd_902142 : Nat := 137254063587708029326261

theorem tailTrace_902142 : CollatzResearch.WordTrace tailWord_902142 prefixEnd_902142 137254063587708029326261 := by
  unfold tailWord_902142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4112977737212635304035585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21935881265134054954856453 4112977737212635304035585)
  ·
    refine ⟨3084733302909476478026689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4112977737212635304035585 3084733302909476478026689)
    ·
      refine ⟨2313549977182107358520017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3084733302909476478026689 2313549977182107358520017)
      ·
        refine ⟨1735162482886580518890013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2313549977182107358520017 1735162482886580518890013)
        ·
          refine ⟨650685931082467694583755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1735162482886580518890013 650685931082467694583755)
          ·
            refine ⟨976028896623701541875633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650685931082467694583755 976028896623701541875633)
            ·
              refine ⟨732021672467776156406725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976028896623701541875633 732021672467776156406725)
              ·
                refine ⟨137254063587708029326261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 732021672467776156406725 137254063587708029326261)
                ·
                  rfl

theorem cell20_902142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_902142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902142 prefixEnd_902142 := by exact prefixLift 902142
  have htrace : WordTrace (prefixWord ++ tailWord_902142) baseStart_902142 baseEnd_902142 := by
    simpa [prefixWord, tailWord_902142, baseEnd_902142] using wordTrace_append hprefix tailTrace_902142
  have hstable : (prefixWord ++ tailWord_902142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902142).length < 2 ^ (prefixWord ++ tailWord_902142).sum := by decide
  have hdescent : baseEnd_902142 < baseStart_902142 := by decide
  rcases family_descends (prefixWord ++ tailWord_902142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902167 : List Nat := [1, 1, 3, 5, 1, 3, 6]
def baseStart_902167 : Nat := 118140960795 + 902167 * 2 ^ 59
def prefixEnd_902167 : Nat := 4983230072969 + 3 ^ 40 * 902167 * 2
def baseEnd_902167 : Nat := 45752622382703901349483

theorem tailTrace_902167 : CollatzResearch.WordTrace tailWord_902167 prefixEnd_902167 45752622382703901349483 := by
  unfold tailWord_902167
  simp only [CollatzResearch.WordTrace]
  refine ⟨32904733722610511701944755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21936489148407007801296503 32904733722610511701944755)
  ·
    refine ⟨49357100583915767552917133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32904733722610511701944755 49357100583915767552917133)
    ·
      refine ⟨18508912718968412832343925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49357100583915767552917133 18508912718968412832343925)
      ·
        refine ⟨1735210567403288703032243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18508912718968412832343925 1735210567403288703032243)
        ·
          refine ⟨2602815851104933054548365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735210567403288703032243 2602815851104933054548365)
          ·
            refine ⟨976055944164349895455637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2602815851104933054548365 976055944164349895455637)
            ·
              refine ⟨45752622382703901349483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 976055944164349895455637 45752622382703901349483)
              ·
                rfl

theorem cell20_902167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 6].length) (baseStart_902167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902167 prefixEnd_902167 := by exact prefixLift 902167
  have htrace : WordTrace (prefixWord ++ tailWord_902167) baseStart_902167 baseEnd_902167 := by
    simpa [prefixWord, tailWord_902167, baseEnd_902167] using wordTrace_append hprefix tailTrace_902167
  have hstable : (prefixWord ++ tailWord_902167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902167).length < 2 ^ (prefixWord ++ tailWord_902167).sum := by decide
  have hdescent : baseEnd_902167 < baseStart_902167 := by decide
  rcases family_descends (prefixWord ++ tailWord_902167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902188 : List Nat := [2, 2, 1, 1, 1, 2, 6, 5]
def baseStart_902188 : Nat := 118140960795 + 902188 * 2 ^ 59
def prefixEnd_902188 : Nat := 4983230072969 + 3 ^ 40 * 902188 * 2
def baseEnd_902188 : Nat := 137261062138850790815087

theorem tailTrace_902188 : CollatzResearch.WordTrace tailWord_902188 prefixEnd_902188 137261062138850790815087 := by
  unfold tailWord_902188
  simp only [CollatzResearch.WordTrace]
  refine ⟨16452749827767216144229609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21936999770356288192306145 16452749827767216144229609)
  ·
    refine ⟨12339562370825412108172207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16452749827767216144229609 12339562370825412108172207)
    ·
      refine ⟨18509343556238118162258311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12339562370825412108172207 18509343556238118162258311)
      ·
        refine ⟨27764015334357177243387467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18509343556238118162258311 27764015334357177243387467)
        ·
          refine ⟨41646023001535765865081201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27764015334357177243387467 41646023001535765865081201)
          ·
            refine ⟨31234517251151824398810901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41646023001535765865081201 31234517251151824398810901)
            ·
              refine ⟨1464117996147741768694261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31234517251151824398810901 1464117996147741768694261)
              ·
                refine ⟨137261062138850790815087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1464117996147741768694261 137261062138850790815087)
                ·
                  rfl

theorem cell20_902188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_902188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902188 prefixEnd_902188 := by exact prefixLift 902188
  have htrace : WordTrace (prefixWord ++ tailWord_902188) baseStart_902188 baseEnd_902188 := by
    simpa [prefixWord, tailWord_902188, baseEnd_902188] using wordTrace_append hprefix tailTrace_902188
  have hstable : (prefixWord ++ tailWord_902188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902188).length < 2 ^ (prefixWord ++ tailWord_902188).sum := by decide
  have hdescent : baseEnd_902188 < baseStart_902188 := by decide
  rcases family_descends (prefixWord ++ tailWord_902188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902226 : List Nat := [3, 2, 2, 1, 3, 9]
def baseStart_902226 : Nat := 118140960795 + 902226 * 2 ^ 59
def prefixEnd_902226 : Nat := 4983230072969 + 3 ^ 40 * 902226 * 2
def baseEnd_902226 : Nat := 15251871505629375154757

theorem tailTrace_902226 : CollatzResearch.WordTrace tailWord_902226 prefixEnd_902226 15251871505629375154757 := by
  unfold tailWord_902226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226721407349191194585633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21937923752931176518895021 8226721407349191194585633)
  ·
    refine ⟨6170041055511893395939225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8226721407349191194585633 6170041055511893395939225)
    ·
      refine ⟨4627530791633920046954419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6170041055511893395939225 4627530791633920046954419)
      ·
        refine ⟨6941296187450880070431629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4627530791633920046954419 6941296187450880070431629)
        ·
          refine ⟨2602986070294080026411861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6941296187450880070431629 2602986070294080026411861)
          ·
            refine ⟨15251871505629375154757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2602986070294080026411861 15251871505629375154757)
            ·
              rfl

theorem cell20_902226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 9].length) (baseStart_902226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902226 prefixEnd_902226 := by exact prefixLift 902226
  have htrace : WordTrace (prefixWord ++ tailWord_902226) baseStart_902226 baseEnd_902226 := by
    simpa [prefixWord, tailWord_902226, baseEnd_902226] using wordTrace_append hprefix tailTrace_902226
  have hstable : (prefixWord ++ tailWord_902226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902226).length < 2 ^ (prefixWord ++ tailWord_902226).sum := by decide
  have hdescent : baseEnd_902226 < baseStart_902226 := by decide
  rcases family_descends (prefixWord ++ tailWord_902226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902295 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_902295 : Nat := 118140960795 + 902295 * 2 ^ 59
def prefixEnd_902295 : Nat := 4983230072969 + 3 ^ 40 * 902295 * 2
def baseEnd_902295 : Nat := 411832024132135555878157

theorem tailTrace_902295 : CollatzResearch.WordTrace tailWord_902295 prefixEnd_902295 411832024132135555878157 := by
  unfold tailWord_902295
  simp only [CollatzResearch.WordTrace]
  refine ⟨32909402266146789562604339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21939601510764526375069559 32909402266146789562604339)
  ·
    refine ⟨49364103399220184343906509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32909402266146789562604339 49364103399220184343906509)
    ·
      refine ⟨18511538774707569128964941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49364103399220184343906509 18511538774707569128964941)
      ·
        refine ⟨6941827040515338423361853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18511538774707569128964941 6941827040515338423361853)
        ·
          refine ⟨2603185140193251908760695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6941827040515338423361853 2603185140193251908760695)
          ·
            refine ⟨3904777710289877863141043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603185140193251908760695 3904777710289877863141043)
            ·
              refine ⟨5857166565434816794711565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904777710289877863141043 5857166565434816794711565)
              ·
                refine ⟨2196437462038056298016837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5857166565434816794711565 2196437462038056298016837)
                ·
                  refine ⟨411832024132135555878157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2196437462038056298016837 411832024132135555878157)
                  ·
                    rfl

theorem cell20_902295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_902295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902295 prefixEnd_902295 := by exact prefixLift 902295
  have htrace : WordTrace (prefixWord ++ tailWord_902295) baseStart_902295 baseEnd_902295 := by
    simpa [prefixWord, tailWord_902295, baseEnd_902295] using wordTrace_append hprefix tailTrace_902295
  have hstable : (prefixWord ++ tailWord_902295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902295).length < 2 ^ (prefixWord ++ tailWord_902295).sum := by decide
  have hdescent : baseEnd_902295 < baseStart_902295 := by decide
  rcases family_descends (prefixWord ++ tailWord_902295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902305 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 3]
def baseStart_902305 : Nat := 118140960795 + 902305 * 2 ^ 59
def prefixEnd_902305 : Nat := 4983230072969 + 3 ^ 40 * 902305 * 2
def baseEnd_902305 : Nat := 411836588404619965544783

theorem tailTrace_902305 : CollatzResearch.WordTrace tailWord_902305 prefixEnd_902305 411836588404619965544783 := by
  unfold tailWord_902305
  simp only [CollatzResearch.WordTrace]
  refine ⟨32909766996110561270468369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21939844664073707513645579 32909766996110561270468369)
  ·
    refine ⟨24682325247082920952851277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32909766996110561270468369 24682325247082920952851277)
    ·
      refine ⟨9255871967656095357319229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24682325247082920952851277 9255871967656095357319229)
      ·
        refine ⟨3470951987871035758994711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9255871967656095357319229 3470951987871035758994711)
        ·
          refine ⟨5206427981806553638492067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3470951987871035758994711 5206427981806553638492067)
          ·
            refine ⟨7809641972709830457738101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206427981806553638492067 7809641972709830457738101)
            ·
              refine ⟨732153934941546605412947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7809641972709830457738101 732153934941546605412947)
              ·
                refine ⟨1098230902412319908119421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732153934941546605412947 1098230902412319908119421)
                ·
                  refine ⟨411836588404619965544783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098230902412319908119421 411836588404619965544783)
                  ·
                    rfl

theorem cell20_902305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_902305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902305 prefixEnd_902305 := by exact prefixLift 902305
  have htrace : WordTrace (prefixWord ++ tailWord_902305) baseStart_902305 baseEnd_902305 := by
    simpa [prefixWord, tailWord_902305, baseEnd_902305] using wordTrace_append hprefix tailTrace_902305
  have hstable : (prefixWord ++ tailWord_902305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902305).length < 2 ^ (prefixWord ++ tailWord_902305).sum := by decide
  have hdescent : baseEnd_902305 < baseStart_902305 := by decide
  rcases family_descends (prefixWord ++ tailWord_902305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902316 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_902316 : Nat := 118140960795 + 902316 * 2 ^ 59
def prefixEnd_902316 : Nat := 4983230072969 + 3 ^ 40 * 902316 * 2
def baseEnd_902316 : Nat := 411841609104352816178071

theorem tailTrace_902316 : CollatzResearch.WordTrace tailWord_902316 prefixEnd_902316 411841609104352816178071 := by
  unfold tailWord_902316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16455084099535355074559401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21940112132713806766079201 16455084099535355074559401)
  ·
    refine ⟨12341313074651516305919551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16455084099535355074559401 12341313074651516305919551)
    ·
      refine ⟨18511969611977274458879327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12341313074651516305919551 18511969611977274458879327)
      ·
        refine ⟨27767954417965911688318991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18511969611977274458879327 27767954417965911688318991)
        ·
          refine ⟨41651931626948867532478487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27767954417965911688318991 41651931626948867532478487)
          ·
            refine ⟨62477897440423301298717731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41651931626948867532478487 62477897440423301298717731)
            ·
              refine ⟨93716846160634951948076597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62477897440423301298717731 93716846160634951948076597)
              ·
                refine ⟨8785954327559526745132181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93716846160634951948076597 8785954327559526745132181)
                ·
                  refine ⟨411841609104352816178071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8785954327559526745132181 411841609104352816178071)
                  ·
                    rfl

theorem cell20_902316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_902316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902316 prefixEnd_902316 := by exact prefixLift 902316
  have htrace : WordTrace (prefixWord ++ tailWord_902316) baseStart_902316 baseEnd_902316 := by
    simpa [prefixWord, tailWord_902316, baseEnd_902316] using wordTrace_append hprefix tailTrace_902316
  have hstable : (prefixWord ++ tailWord_902316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902316).length < 2 ^ (prefixWord ++ tailWord_902316).sum := by decide
  have hdescent : baseEnd_902316 < baseStart_902316 := by decide
  rcases family_descends (prefixWord ++ tailWord_902316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902329 : List Nat := [1, 2, 1, 4, 1, 5, 1, 3, 2]
def baseStart_902329 : Nat := 118140960795 + 902329 * 2 ^ 59
def prefixEnd_902329 : Nat := 4983230072969 + 3 ^ 40 * 902329 * 2
def baseEnd_902329 : Nat := 411847542658582548744685

theorem tailTrace_902329 : CollatzResearch.WordTrace tailWord_902329 prefixEnd_902329 411847542658582548744685 := by
  unfold tailWord_902329
  simp only [CollatzResearch.WordTrace]
  refine ⟨32910642348023613369342041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21940428232015742246228027 32910642348023613369342041)
  ·
    refine ⟨24682981761017710027006531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32910642348023613369342041 24682981761017710027006531)
    ·
      refine ⟨37024472641526565040509797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24682981761017710027006531 37024472641526565040509797)
      ·
        refine ⟨6942088620286230945095587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37024472641526565040509797 6942088620286230945095587)
        ·
          refine ⟨10413132930429346417643381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6942088620286230945095587 10413132930429346417643381)
          ·
            refine ⟨976231212227751226654067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10413132930429346417643381 976231212227751226654067)
            ·
              refine ⟨1464346818341626839981101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976231212227751226654067 1464346818341626839981101)
              ·
                refine ⟨549130056878110064992913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1464346818341626839981101 549130056878110064992913)
                ·
                  refine ⟨411847542658582548744685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549130056878110064992913 411847542658582548744685)
                  ·
                    rfl

theorem cell20_902329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_902329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902329 prefixEnd_902329 := by exact prefixLift 902329
  have htrace : WordTrace (prefixWord ++ tailWord_902329) baseStart_902329 baseEnd_902329 := by
    simpa [prefixWord, tailWord_902329, baseEnd_902329] using wordTrace_append hprefix tailTrace_902329
  have hstable : (prefixWord ++ tailWord_902329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902329).length < 2 ^ (prefixWord ++ tailWord_902329).sum := by decide
  have hdescent : baseEnd_902329 < baseStart_902329 := by decide
  rcases family_descends (prefixWord ++ tailWord_902329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902342 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_902342 : Nat := 118140960795 + 902342 * 2 ^ 59
def prefixEnd_902342 : Nat := 4983230072969 + 3 ^ 40 * 902342 * 2
def baseEnd_902342 : Nat := 411853476212812281311299

theorem tailTrace_902342 : CollatzResearch.WordTrace tailWord_902342 prefixEnd_902342 411853476212812281311299 := by
  unfold tailWord_902342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028472390530516143423915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21940744331317677726376853 1028472390530516143423915)
  ·
    refine ⟨1542708585795774215135873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1028472390530516143423915 1542708585795774215135873)
    ·
      refine ⟨1157031439346830661351905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1542708585795774215135873 1157031439346830661351905)
      ·
        refine ⟨867773579510122996013929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1157031439346830661351905 867773579510122996013929)
        ·
          refine ⟨650830184632592247010447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 867773579510122996013929 650830184632592247010447)
          ·
            refine ⟨976245276948888370515671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650830184632592247010447 976245276948888370515671)
            ·
              refine ⟨1464367915423332555773507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976245276948888370515671 1464367915423332555773507)
              ·
                refine ⟨2196551873134998833660261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464367915423332555773507 2196551873134998833660261)
                ·
                  refine ⟨411853476212812281311299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2196551873134998833660261 411853476212812281311299)
                  ·
                    rfl

theorem cell20_902342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_902342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902342 prefixEnd_902342 := by exact prefixLift 902342
  have htrace : WordTrace (prefixWord ++ tailWord_902342) baseStart_902342 baseEnd_902342 := by
    simpa [prefixWord, tailWord_902342, baseEnd_902342] using wordTrace_append hprefix tailTrace_902342
  have hstable : (prefixWord ++ tailWord_902342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902342).length < 2 ^ (prefixWord ++ tailWord_902342).sum := by decide
  have hdescent : baseEnd_902342 < baseStart_902342 := by decide
  rcases family_descends (prefixWord ++ tailWord_902342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902356 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 3]
def baseStart_902356 : Nat := 118140960795 + 902356 * 2 ^ 59
def prefixEnd_902356 : Nat := 4983230072969 + 3 ^ 40 * 902356 * 2
def baseEnd_902356 : Nat := 411859866194290454844575

theorem tailTrace_902356 : CollatzResearch.WordTrace tailWord_902356 prefixEnd_902356 411859866194290454844575 := by
  unfold tailWord_902356
  simp only [CollatzResearch.WordTrace]
  refine ⟨16455813559462898490287461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21941084745950531320383281 16455813559462898490287461)
  ·
    refine ⟨3085465042399293466928899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16455813559462898490287461 3085465042399293466928899)
    ·
      refine ⟨4628197563598940200393349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3085465042399293466928899 4628197563598940200393349)
      ·
        refine ⟨867787043174801287573753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4628197563598940200393349 867787043174801287573753)
        ·
          refine ⟨650840282381100965680315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 867787043174801287573753 650840282381100965680315)
          ·
            refine ⟨976260423571651448520473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650840282381100965680315 976260423571651448520473)
            ·
              refine ⟨732195317678738586390355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976260423571651448520473 732195317678738586390355)
              ·
                refine ⟨1098292976518107879585533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732195317678738586390355 1098292976518107879585533)
                ·
                  refine ⟨411859866194290454844575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098292976518107879585533 411859866194290454844575)
                  ·
                    rfl

theorem cell20_902356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_902356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902356 prefixEnd_902356 := by exact prefixLift 902356
  have htrace : WordTrace (prefixWord ++ tailWord_902356) baseStart_902356 baseEnd_902356 := by
    simpa [prefixWord, tailWord_902356, baseEnd_902356] using wordTrace_append hprefix tailTrace_902356
  have hstable : (prefixWord ++ tailWord_902356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902356).length < 2 ^ (prefixWord ++ tailWord_902356).sum := by decide
  have hdescent : baseEnd_902356 < baseStart_902356 := by decide
  rcases family_descends (prefixWord ++ tailWord_902356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902357 : List Nat := [1, 3, 2, 4, 1, 2, 2, 5]
def baseStart_902357 : Nat := 118140960795 + 902357 * 2 ^ 59
def prefixEnd_902357 : Nat := 4983230072969 + 3 ^ 40 * 902357 * 2
def baseEnd_902357 : Nat := 137286774207179631937079

theorem tailTrace_902357 : CollatzResearch.WordTrace tailWord_902357 prefixEnd_902357 137286774207179631937079 := by
  unfold tailWord_902357
  simp only [CollatzResearch.WordTrace]
  refine ⟨32911663591922174151361325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21941109061281449434240883 32911663591922174151361325)
  ·
    refine ⟨12341873846970815306760497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32911663591922174151361325 12341873846970815306760497)
    ·
      refine ⟨9256405385228111480070373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12341873846970815306760497 9256405385228111480070373)
      ·
        refine ⟨1735576009730270902513195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9256405385228111480070373 1735576009730270902513195)
        ·
          refine ⟨2603364014595406353769793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735576009730270902513195 2603364014595406353769793)
          ·
            refine ⟨1952523010946554765327345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2603364014595406353769793 1952523010946554765327345)
            ·
              refine ⟨1464392258209916073995509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1952523010946554765327345 1464392258209916073995509)
              ·
                refine ⟨137286774207179631937079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1464392258209916073995509 137286774207179631937079)
                ·
                  rfl

theorem cell20_902357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_902357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902357 prefixEnd_902357 := by exact prefixLift 902357
  have htrace : WordTrace (prefixWord ++ tailWord_902357) baseStart_902357 baseEnd_902357 := by
    simpa [prefixWord, tailWord_902357, baseEnd_902357] using wordTrace_append hprefix tailTrace_902357
  have hstable : (prefixWord ++ tailWord_902357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902357).length < 2 ^ (prefixWord ++ tailWord_902357).sum := by decide
  have hdescent : baseEnd_902357 < baseStart_902357 := by decide
  rcases family_descends (prefixWord ++ tailWord_902357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902360 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 3]
def baseStart_902360 : Nat := 118140960795 + 902360 * 2 ^ 59
def prefixEnd_902360 : Nat := 4983230072969 + 3 ^ 40 * 902360 * 2
def baseEnd_902360 : Nat := 411861691903284218711225

theorem tailTrace_902360 : CollatzResearch.WordTrace tailWord_902360 prefixEnd_902360 411861691903284218711225 := by
  unfold tailWord_902360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16455886505455652831860267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21941182007274203775813689 16455886505455652831860267)
  ·
    refine ⟨24683829758183479247790401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16455886505455652831860267 24683829758183479247790401)
    ·
      refine ⟨18512872318637609435842801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24683829758183479247790401 18512872318637609435842801)
      ·
        refine ⟨13884654238978207076882101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18512872318637609435842801 13884654238978207076882101)
        ·
          refine ⟨1301686334904206913457697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13884654238978207076882101 1301686334904206913457697)
          ·
            refine ⟨976264751178155185093273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301686334904206913457697 976264751178155185093273)
            ·
              refine ⟨732198563383616388819955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976264751178155185093273 732198563383616388819955)
              ·
                refine ⟨1098297845075424583229933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732198563383616388819955 1098297845075424583229933)
                ·
                  refine ⟨411861691903284218711225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098297845075424583229933 411861691903284218711225)
                  ·
                    rfl

theorem cell20_902360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_902360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902360 prefixEnd_902360 := by exact prefixLift 902360
  have htrace : WordTrace (prefixWord ++ tailWord_902360) baseStart_902360 baseEnd_902360 := by
    simpa [prefixWord, tailWord_902360, baseEnd_902360] using wordTrace_append hprefix tailTrace_902360
  have hstable : (prefixWord ++ tailWord_902360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902360).length < 2 ^ (prefixWord ++ tailWord_902360).sum := by decide
  have hdescent : baseEnd_902360 < baseStart_902360 := by decide
  rcases family_descends (prefixWord ++ tailWord_902360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902378 : List Nat := [3, 1, 3, 1, 1, 3, 2, 6]
def baseStart_902378 : Nat := 118140960795 + 902378 * 2 ^ 59
def prefixEnd_902378 : Nat := 4983230072969 + 3 ^ 40 * 902378 * 2
def baseEnd_902378 : Nat := 137289969197918718703717

theorem tailTrace_902378 : CollatzResearch.WordTrace tailWord_902378 prefixEnd_902378 137289969197918718703717 := by
  unfold tailWord_902378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8228107381211523684468947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21941619683230729825250525 8228107381211523684468947)
  ·
    refine ⟨12342161071817285526703421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8228107381211523684468947 12342161071817285526703421)
    ·
      refine ⟨4628310401931482072513783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12342161071817285526703421 4628310401931482072513783)
      ·
        refine ⟨6942465602897223108770675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628310401931482072513783 6942465602897223108770675)
        ·
          refine ⟨10413698404345834663156013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6942465602897223108770675 10413698404345834663156013)
          ·
            refine ⟨3905136901629687998683505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10413698404345834663156013 3905136901629687998683505)
            ·
              refine ⟨2928852676222265999012629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3905136901629687998683505 2928852676222265999012629)
              ·
                refine ⟨137289969197918718703717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2928852676222265999012629 137289969197918718703717)
                ·
                  rfl

theorem cell20_902378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_902378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902378 prefixEnd_902378 := by exact prefixLift 902378
  have htrace : WordTrace (prefixWord ++ tailWord_902378) baseStart_902378 baseEnd_902378 := by
    simpa [prefixWord, tailWord_902378, baseEnd_902378] using wordTrace_append hprefix tailTrace_902378
  have hstable : (prefixWord ++ tailWord_902378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902378).length < 2 ^ (prefixWord ++ tailWord_902378).sum := by decide
  have hdescent : baseEnd_902378 < baseStart_902378 := by decide
  rcases family_descends (prefixWord ++ tailWord_902378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902399 : List Nat := [1, 1, 2, 2, 1, 13]
def baseStart_902399 : Nat := 118140960795 + 902399 * 2 ^ 59
def prefixEnd_902399 : Nat := 4983230072969 + 3 ^ 40 * 902399 * 2
def baseEnd_902399 : Nat := 15254796020961978385595

theorem tailTrace_902399 : CollatzResearch.WordTrace tailWord_902399 prefixEnd_902399 15254796020961978385595 := by
  unfold tailWord_902399
  simp only [CollatzResearch.WordTrace]
  refine ⟨32913195457770015324390251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21942130305180010216260167 32913195457770015324390251)
  ·
    refine ⟨49369793186655022986585377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32913195457770015324390251 49369793186655022986585377)
    ·
      refine ⟨37027344889991267239939033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49369793186655022986585377 37027344889991267239939033)
      ·
        refine ⟨27770508667493450429954275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37027344889991267239939033 27770508667493450429954275)
        ·
          refine ⟨41655763001240175644931413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27770508667493450429954275 41655763001240175644931413)
          ·
            refine ⟨15254796020961978385595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 41655763001240175644931413 15254796020961978385595)
            ·
              rfl

theorem cell20_902399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 13].length) (baseStart_902399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902399 prefixEnd_902399 := by exact prefixLift 902399
  have htrace : WordTrace (prefixWord ++ tailWord_902399) baseStart_902399 baseEnd_902399 := by
    simpa [prefixWord, tailWord_902399, baseEnd_902399] using wordTrace_append hprefix tailTrace_902399
  have hstable : (prefixWord ++ tailWord_902399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902399).length < 2 ^ (prefixWord ++ tailWord_902399).sum := by decide
  have hdescent : baseEnd_902399 < baseStart_902399 := by decide
  rcases family_descends (prefixWord ++ tailWord_902399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902470 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_902470 : Nat := 118140960795 + 902470 * 2 ^ 59
def prefixEnd_902470 : Nat := 4983230072969 + 3 ^ 40 * 902470 * 2
def baseEnd_902470 : Nat := 411911898900612725044109

theorem tailTrace_902470 : CollatzResearch.WordTrace tailWord_902470 prefixEnd_902470 411911898900612725044109 := by
  unfold tailWord_902470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028618282516024826569527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21943856693675196300149909 1028618282516024826569527)
  ·
    refine ⟨1542927423774037239854291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1028618282516024826569527 1542927423774037239854291)
    ·
      refine ⟨2314391135661055859781437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1542927423774037239854291 2314391135661055859781437)
      ·
        refine ⟨867896675872895947418039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2314391135661055859781437 867896675872895947418039)
        ·
          refine ⟨1301845013809343921127059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867896675872895947418039 1301845013809343921127059)
          ·
            refine ⟨1952767520714015881690589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301845013809343921127059 1952767520714015881690589)
            ·
              refine ⟨732287820267755955633971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1952767520714015881690589 732287820267755955633971)
              ·
                refine ⟨1098431730401633933450957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732287820267755955633971 1098431730401633933450957)
                ·
                  refine ⟨411911898900612725044109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098431730401633933450957 411911898900612725044109)
                  ·
                    rfl

theorem cell20_902470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_902470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902470 prefixEnd_902470 := by exact prefixLift 902470
  have htrace : WordTrace (prefixWord ++ tailWord_902470) baseStart_902470 baseEnd_902470 := by
    simpa [prefixWord, tailWord_902470, baseEnd_902470] using wordTrace_append hprefix tailTrace_902470
  have hstable : (prefixWord ++ tailWord_902470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902470).length < 2 ^ (prefixWord ++ tailWord_902470).sum := by decide
  have hdescent : baseEnd_902470 < baseStart_902470 := by decide
  rcases family_descends (prefixWord ++ tailWord_902470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902485 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_902485 : Nat := 118140960795 + 902485 * 2 ^ 59
def prefixEnd_902485 : Nat := 4983230072969 + 3 ^ 40 * 902485 * 2
def baseEnd_902485 : Nat := 411918745309339339544047

theorem tailTrace_902485 : CollatzResearch.WordTrace tailWord_902485 prefixEnd_902485 411918745309339339544047 := by
  unfold tailWord_902485
  simp only [CollatzResearch.WordTrace]
  refine ⟨32916332135458452012020909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21944221423638968008013939 32916332135458452012020909)
  ·
    refine ⟨12343624550796919504507841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32916332135458452012020909 12343624550796919504507841)
    ·
      refine ⟨9257718413097689628380881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12343624550796919504507841 9257718413097689628380881)
      ·
        refine ⟨6943288809823267221285661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9257718413097689628380881 6943288809823267221285661)
        ·
          refine ⟨2603733303683725207982123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6943288809823267221285661 2603733303683725207982123)
          ·
            refine ⟨3905599955525587811973185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603733303683725207982123 3905599955525587811973185)
            ·
              refine ⟨2929199966644190858979889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3905599955525587811973185 2929199966644190858979889)
              ·
                refine ⟨2196899974983143144234917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2929199966644190858979889 2196899974983143144234917)
                ·
                  refine ⟨411918745309339339544047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2196899974983143144234917 411918745309339339544047)
                  ·
                    rfl

theorem cell20_902485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_902485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902485 prefixEnd_902485 := by exact prefixLift 902485
  have htrace : WordTrace (prefixWord ++ tailWord_902485) baseStart_902485 baseEnd_902485 := by
    simpa [prefixWord, tailWord_902485, baseEnd_902485] using wordTrace_append hprefix tailTrace_902485
  have hstable : (prefixWord ++ tailWord_902485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902485).length < 2 ^ (prefixWord ++ tailWord_902485).sum := by decide
  have hdescent : baseEnd_902485 < baseStart_902485 := by decide
  rcases family_descends (prefixWord ++ tailWord_902485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902499 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_902499 : Nat := 118140960795 + 902499 * 2 ^ 59
def prefixEnd_902499 : Nat := 4983230072969 + 3 ^ 40 * 902499 * 2
def baseEnd_902499 : Nat := 411925135290817513077323

theorem tailTrace_902499 : CollatzResearch.WordTrace tailWord_902499 prefixEnd_902499 411925135290817513077323 := by
  unfold tailWord_902499
  simp only [CollatzResearch.WordTrace]
  refine ⟨32916842757407732403030551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21944561838271821602020367 32916842757407732403030551)
  ·
    refine ⟨49375264136111598604545827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32916842757407732403030551 49375264136111598604545827)
    ·
      refine ⟨74062896204167397906818741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49375264136111598604545827 74062896204167397906818741)
      ·
        refine ⟨6943396519140693553764257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74062896204167397906818741 6943396519140693553764257)
        ·
          refine ⟨5207547389355520165323193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6943396519140693553764257 5207547389355520165323193)
          ·
            refine ⟨3905660542016640123992395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5207547389355520165323193 3905660542016640123992395)
            ·
              refine ⟨5858490813024960185988593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3905660542016640123992395 5858490813024960185988593)
              ·
                refine ⟨4393868109768720139491445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5858490813024960185988593 4393868109768720139491445)
                ·
                  refine ⟨411925135290817513077323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4393868109768720139491445 411925135290817513077323)
                  ·
                    rfl

theorem cell20_902499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_902499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902499 prefixEnd_902499 := by exact prefixLift 902499
  have htrace : WordTrace (prefixWord ++ tailWord_902499) baseStart_902499 baseEnd_902499 := by
    simpa [prefixWord, tailWord_902499, baseEnd_902499] using wordTrace_append hprefix tailTrace_902499
  have hstable : (prefixWord ++ tailWord_902499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902499).length < 2 ^ (prefixWord ++ tailWord_902499).sum := by decide
  have hdescent : baseEnd_902499 < baseStart_902499 := by decide
  rcases family_descends (prefixWord ++ tailWord_902499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902513 : List Nat := [1, 2, 2, 2, 1, 2, 10]
def baseStart_902513 : Nat := 118140960795 + 902513 * 2 ^ 59
def prefixEnd_902513 : Nat := 4983230072969 + 3 ^ 40 * 902513 * 2
def baseEnd_902513 : Nat := 45770169474699520734511

theorem tailTrace_902513 : CollatzResearch.WordTrace tailWord_902513 prefixEnd_902513 45770169474699520734511 := by
  unfold tailWord_902513
  simp only [CollatzResearch.WordTrace]
  refine ⟨32917353379357012794040193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21944902252904675196026795 32917353379357012794040193)
  ·
    refine ⟨24688015034517759595530145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32917353379357012794040193 24688015034517759595530145)
    ·
      refine ⟨18516011275888319696647609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24688015034517759595530145 18516011275888319696647609)
      ·
        refine ⟨13887008456916239772485707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18516011275888319696647609 13887008456916239772485707)
        ·
          refine ⟨20830512685374359658728561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13887008456916239772485707 20830512685374359658728561)
          ·
            refine ⟨15622884514030769744046421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20830512685374359658728561 15622884514030769744046421)
            ·
              refine ⟨45770169474699520734511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15622884514030769744046421 45770169474699520734511)
              ·
                rfl

theorem cell20_902513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 10].length) (baseStart_902513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902513 prefixEnd_902513 := by exact prefixLift 902513
  have htrace : WordTrace (prefixWord ++ tailWord_902513) baseStart_902513 baseEnd_902513 := by
    simpa [prefixWord, tailWord_902513, baseEnd_902513] using wordTrace_append hprefix tailTrace_902513
  have hstable : (prefixWord ++ tailWord_902513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902513).length < 2 ^ (prefixWord ++ tailWord_902513).sum := by decide
  have hdescent : baseEnd_902513 < baseStart_902513 := by decide
  rcases family_descends (prefixWord ++ tailWord_902513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902529 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 3]
def baseStart_902529 : Nat := 118140960795 + 902529 * 2 ^ 59
def prefixEnd_902529 : Nat := 4983230072969 + 3 ^ 40 * 902529 * 2
def baseEnd_902529 : Nat := 411938828108270742077201

theorem tailTrace_902529 : CollatzResearch.WordTrace tailWord_902529 prefixEnd_902529 411938828108270742077201 := by
  unfold tailWord_902529
  simp only [CollatzResearch.WordTrace]
  refine ⟨32917936947299047526622641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21945291298199365017748427 32917936947299047526622641)
  ·
    refine ⟨24688452710474285644966981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32917936947299047526622641 24688452710474285644966981)
    ·
      refine ⟨4629084883213928558431309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24688452710474285644966981 4629084883213928558431309)
      ·
        refine ⟨1735906831205223209411741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4629084883213928558431309 1735906831205223209411741)
        ·
          refine ⟨650965061701958703529403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1735906831205223209411741 650965061701958703529403)
          ·
            refine ⟨976447592552938055294105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650965061701958703529403 976447592552938055294105)
            ·
              refine ⟨732335694414703541470579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976447592552938055294105 732335694414703541470579)
              ·
                refine ⟨1098503541622055312205869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732335694414703541470579 1098503541622055312205869)
                ·
                  refine ⟨411938828108270742077201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098503541622055312205869 411938828108270742077201)
                  ·
                    rfl

theorem cell20_902529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_902529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902529 prefixEnd_902529 := by exact prefixLift 902529
  have htrace : WordTrace (prefixWord ++ tailWord_902529) baseStart_902529 baseEnd_902529 := by
    simpa [prefixWord, tailWord_902529, baseEnd_902529] using wordTrace_append hprefix tailTrace_902529
  have hstable : (prefixWord ++ tailWord_902529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902529).length < 2 ^ (prefixWord ++ tailWord_902529).sum := by decide
  have hdescent : baseEnd_902529 < baseStart_902529 := by decide
  rcases family_descends (prefixWord ++ tailWord_902529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902568 : List Nat := [2, 1, 6, 1, 10]
def baseStart_902568 : Nat := 118140960795 + 902568 * 2 ^ 59
def prefixEnd_902568 : Nat := 4983230072969 + 3 ^ 40 * 902568 * 2
def baseEnd_902568 : Nat := 5085884305814320244161

theorem tailTrace_902568 : CollatzResearch.WordTrace tailWord_902568 prefixEnd_902568 5085884305814320244161 := by
  unfold tailWord_902568
  simp only [CollatzResearch.WordTrace]
  refine ⟨16459679697078878593646179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21946239596105171458194905 16459679697078878593646179)
  ·
    refine ⟨24689519545618317890469269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16459679697078878593646179 24689519545618317890469269)
    ·
      refine ⟨1157321228700858651115747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24689519545618317890469269 1157321228700858651115747)
      ·
        refine ⟨1735981843051287976673621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1157321228700858651115747 1735981843051287976673621)
        ·
          refine ⟨5085884305814320244161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1735981843051287976673621 5085884305814320244161)
          ·
            rfl

theorem cell20_902568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 10].length) (baseStart_902568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902568 prefixEnd_902568 := by exact prefixLift 902568
  have htrace : WordTrace (prefixWord ++ tailWord_902568) baseStart_902568 baseEnd_902568 := by
    simpa [prefixWord, tailWord_902568, baseEnd_902568] using wordTrace_append hprefix tailTrace_902568
  have hstable : (prefixWord ++ tailWord_902568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902568).length < 2 ^ (prefixWord ++ tailWord_902568).sum := by decide
  have hdescent : baseEnd_902568 < baseStart_902568 := by decide
  rcases family_descends (prefixWord ++ tailWord_902568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902585 : List Nat := [1, 2, 1, 4, 4, 2, 1, 5]
def baseStart_902585 : Nat := 118140960795 + 902585 * 2 ^ 59
def prefixEnd_902585 : Nat := 4983230072969 + 3 ^ 40 * 902585 * 2
def baseEnd_902585 : Nat := 137321462678061145403435

theorem tailTrace_902585 : CollatzResearch.WordTrace tailWord_902585 prefixEnd_902585 137321462678061145403435 := by
  unfold tailWord_902585
  simp only [CollatzResearch.WordTrace]
  refine ⟨32919979435096169090661209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21946652956730779393774139 32919979435096169090661209)
  ·
    refine ⟨24689984576322126817995907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32919979435096169090661209 24689984576322126817995907)
    ·
      refine ⟨37034976864483190226993861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24689984576322126817995907 37034976864483190226993861)
      ·
        refine ⟨6944058162090598167561349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37034976864483190226993861 6944058162090598167561349)
        ·
          refine ⟨1302010905391987156417753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6944058162090598167561349 1302010905391987156417753)
          ·
            refine ⟨976508179043990367313315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1302010905391987156417753 976508179043990367313315)
            ·
              refine ⟨1464762268565985550969973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976508179043990367313315 1464762268565985550969973)
              ·
                refine ⟨137321462678061145403435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1464762268565985550969973 137321462678061145403435)
                ·
                  rfl

theorem cell20_902585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 5].length) (baseStart_902585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902585 prefixEnd_902585 := by exact prefixLift 902585
  have htrace : WordTrace (prefixWord ++ tailWord_902585) baseStart_902585 baseEnd_902585 := by
    simpa [prefixWord, tailWord_902585, baseEnd_902585] using wordTrace_append hprefix tailTrace_902585
  have hstable : (prefixWord ++ tailWord_902585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902585).length < 2 ^ (prefixWord ++ tailWord_902585).sum := by decide
  have hdescent : baseEnd_902585 < baseStart_902585 := by decide
  rcases family_descends (prefixWord ++ tailWord_902585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902613 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_902613 : Nat := 118140960795 + 902613 * 2 ^ 59
def prefixEnd_902613 : Nat := 4983230072969 + 3 ^ 40 * 902613 * 2
def baseEnd_902613 : Nat := 411977167997139783276857

theorem tailTrace_902613 : CollatzResearch.WordTrace tailWord_902613 prefixEnd_902613 411977167997139783276857 := by
  unfold tailWord_902613
  simp only [CollatzResearch.WordTrace]
  refine ⟨32921000678994729872680493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21947333785996486581786995 32921000678994729872680493)
  ·
    refine ⟨12345375254623023702255185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32921000678994729872680493 12345375254623023702255185)
    ·
      refine ⟨9259031440967267776691389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12345375254623023702255185 9259031440967267776691389)
      ·
        refine ⟨3472136790362725416259271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9259031440967267776691389 3472136790362725416259271)
        ·
          refine ⟨5208205185544088124388907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3472136790362725416259271 5208205185544088124388907)
          ·
            refine ⟨7812307778316132186583361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5208205185544088124388907 7812307778316132186583361)
            ·
              refine ⟨5859230833737099139937521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7812307778316132186583361 5859230833737099139937521)
              ·
                refine ⟨4394423125302824354953141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5859230833737099139937521 4394423125302824354953141)
                ·
                  refine ⟨411977167997139783276857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4394423125302824354953141 411977167997139783276857)
                  ·
                    rfl

theorem cell20_902613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_902613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902613 prefixEnd_902613 := by exact prefixLift 902613
  have htrace : WordTrace (prefixWord ++ tailWord_902613) baseStart_902613 baseEnd_902613 := by
    simpa [prefixWord, tailWord_902613, baseEnd_902613] using wordTrace_append hprefix tailTrace_902613
  have hstable : (prefixWord ++ tailWord_902613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902613).length < 2 ^ (prefixWord ++ tailWord_902613).sum := by decide
  have hdescent : baseEnd_902613 < baseStart_902613 := by decide
  rcases family_descends (prefixWord ++ tailWord_902613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902665 : List Nat := [1, 2, 1, 1, 3, 1, 5, 6]
def baseStart_902665 : Nat := 118140960795 + 902665 * 2 ^ 59
def prefixEnd_902665 : Nat := 4983230072969 + 3 ^ 40 * 902665 * 2
def baseEnd_902665 : Nat := 137333634071352904514437

theorem tailTrace_902665 : CollatzResearch.WordTrace tailWord_902665 prefixEnd_902665 137333634071352904514437 := by
  unfold tailWord_902665
  simp only [CollatzResearch.WordTrace]
  refine ⟨32922897274806342753573449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21948598183204228502382299 32922897274806342753573449)
  ·
    refine ⟨24692172956104757065180087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32922897274806342753573449 24692172956104757065180087)
    ·
      refine ⟨37038259434157135597770131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24692172956104757065180087 37038259434157135597770131)
      ·
        refine ⟨55557389151235703396655197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37038259434157135597770131 55557389151235703396655197)
        ·
          refine ⟨20834020931713388773745699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55557389151235703396655197 20834020931713388773745699)
          ·
            refine ⟨31251031397570083160618549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20834020931713388773745699 31251031397570083160618549)
            ·
              refine ⟨2929784193522195296307989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31251031397570083160618549 2929784193522195296307989)
              ·
                refine ⟨137333634071352904514437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2929784193522195296307989 137333634071352904514437)
                ·
                  rfl

theorem cell20_902665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_902665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902665 prefixEnd_902665 := by exact prefixLift 902665
  have htrace : WordTrace (prefixWord ++ tailWord_902665) baseStart_902665 baseEnd_902665 := by
    simpa [prefixWord, tailWord_902665, baseEnd_902665] using wordTrace_append hprefix tailTrace_902665
  have hstable : (prefixWord ++ tailWord_902665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902665).length < 2 ^ (prefixWord ++ tailWord_902665).sum := by decide
  have hdescent : baseEnd_902665 < baseStart_902665 := by decide
  rcases family_descends (prefixWord ++ tailWord_902665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902689 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_902689 : Nat := 118140960795 + 902689 * 2 ^ 59
def prefixEnd_902689 : Nat := 4983230072969 + 3 ^ 40 * 902689 * 2
def baseEnd_902689 : Nat := 412011856468021296743213

theorem tailTrace_902689 : CollatzResearch.WordTrace tailWord_902689 prefixEnd_902689 412011856468021296743213 := by
  unfold tailWord_902689
  simp only [CollatzResearch.WordTrace]
  refine ⟨32923772626719394852447121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21949181751146263234964747 32923772626719394852447121)
  ·
    refine ⟨24692829470039546139335341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32923772626719394852447121 24692829470039546139335341)
    ·
      refine ⟨9259811051264829802250753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24692829470039546139335341 9259811051264829802250753)
      ·
        refine ⟨6944858288448622351688065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9259811051264829802250753 6944858288448622351688065)
        ·
          refine ⟨5208643716336466763766049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6944858288448622351688065 5208643716336466763766049)
          ·
            refine ⟨3906482787252350072824537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5208643716336466763766049 3906482787252350072824537)
            ·
              refine ⟨2929862090439262554618403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3906482787252350072824537 2929862090439262554618403)
              ·
                refine ⟨4394793135658893831927605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929862090439262554618403 4394793135658893831927605)
                ·
                  refine ⟨412011856468021296743213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4394793135658893831927605 412011856468021296743213)
                  ·
                    rfl

theorem cell20_902689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_902689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902689 prefixEnd_902689 := by exact prefixLift 902689
  have htrace : WordTrace (prefixWord ++ tailWord_902689) baseStart_902689 baseEnd_902689 := by
    simpa [prefixWord, tailWord_902689, baseEnd_902689] using wordTrace_append hprefix tailTrace_902689
  have hstable : (prefixWord ++ tailWord_902689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902689).length < 2 ^ (prefixWord ++ tailWord_902689).sum := by decide
  have hdescent : baseEnd_902689 < baseStart_902689 := by decide
  rcases family_descends (prefixWord ++ tailWord_902689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902702 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_902702 : Nat := 118140960795 + 902702 * 2 ^ 59
def prefixEnd_902702 : Nat := 4983230072969 + 3 ^ 40 * 902702 * 2
def baseEnd_902702 : Nat := 412017790022251029309827

theorem tailTrace_902702 : CollatzResearch.WordTrace tailWord_902702 prefixEnd_902702 412017790022251029309827 := by
  unfold tailWord_902702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4115530846959037259083795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21949497850448198715113573 4115530846959037259083795)
  ·
    refine ⟨6173296270438555888625693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4115530846959037259083795 6173296270438555888625693)
    ·
      refine ⟨2314986101414458458234635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6173296270438555888625693 2314986101414458458234635)
      ·
        refine ⟨3472479152121687687351953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2314986101414458458234635 3472479152121687687351953)
        ·
          refine ⟨2604359364091265765513965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3472479152121687687351953 2604359364091265765513965)
          ·
            refine ⟨976634761534224662067737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2604359364091265765513965 976634761534224662067737)
            ·
              refine ⟨732476071150668496550803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976634761534224662067737 732476071150668496550803)
              ·
                refine ⟨1098714106726002744826205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732476071150668496550803 1098714106726002744826205)
                ·
                  refine ⟨412017790022251029309827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098714106726002744826205 412017790022251029309827)
                  ·
                    rfl

theorem cell20_902702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_902702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902702 prefixEnd_902702 := by exact prefixLift 902702
  have htrace : WordTrace (prefixWord ++ tailWord_902702) baseStart_902702 baseEnd_902702 := by
    simpa [prefixWord, tailWord_902702, baseEnd_902702] using wordTrace_append hprefix tailTrace_902702
  have hstable : (prefixWord ++ tailWord_902702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902702).length < 2 ^ (prefixWord ++ tailWord_902702).sum := by decide
  have hdescent : baseEnd_902702 < baseStart_902702 := by decide
  rcases family_descends (prefixWord ++ tailWord_902702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902834 : List Nat := [3, 2, 1, 1, 1, 2, 6, 4]
def baseStart_902834 : Nat := 118140960795 + 902834 * 2 ^ 59
def prefixEnd_902834 : Nat := 4983230072969 + 3 ^ 40 * 902834 * 2
def baseEnd_902834 : Nat := 137359346139681745636429

theorem tailTrace_902834 : CollatzResearch.WordTrace tailWord_902834 prefixEnd_902834 137359346139681745636429 := by
  unfold tailWord_902834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8232265302798521154118889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21952707474129389744317037 8232265302798521154118889)
  ·
    refine ⟨6174198977098890865589167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8232265302798521154118889 6174198977098890865589167)
    ·
      refine ⟨9261298465648336298383751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6174198977098890865589167 9261298465648336298383751)
      ·
        refine ⟨13891947698472504447575627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9261298465648336298383751 13891947698472504447575627)
        ·
          refine ⟨20837921547708756671363441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13891947698472504447575627 20837921547708756671363441)
          ·
            refine ⟨15628441160781567503522581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20837921547708756671363441 15628441160781567503522581)
            ·
              refine ⟨732583179411635976727621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15628441160781567503522581 732583179411635976727621)
              ·
                refine ⟨137359346139681745636429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 732583179411635976727621 137359346139681745636429)
                ·
                  rfl

theorem cell20_902834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_902834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902834 prefixEnd_902834 := by exact prefixLift 902834
  have htrace : WordTrace (prefixWord ++ tailWord_902834) baseStart_902834 baseEnd_902834 := by
    simpa [prefixWord, tailWord_902834, baseEnd_902834] using wordTrace_append hprefix tailTrace_902834
  have hstable : (prefixWord ++ tailWord_902834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902834).length < 2 ^ (prefixWord ++ tailWord_902834).sum := by decide
  have hdescent : baseEnd_902834 < baseStart_902834 := by decide
  rcases family_descends (prefixWord ++ tailWord_902834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902844 : List Nat := [2, 2, 2, 3, 1, 2, 3, 3, 2]
def baseStart_902844 : Nat := 118140960795 + 902844 * 2 ^ 59
def prefixEnd_902844 : Nat := 4983230072969 + 3 ^ 40 * 902844 * 2
def baseEnd_902844 : Nat := 412082602691529646575913

theorem tailTrace_902844 : CollatzResearch.WordTrace tailWord_902844 prefixEnd_902844 412082602691529646575913 := by
  unfold tailWord_902844
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464712970578928162169793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21952950627438570882893057 16464712970578928162169793)
  ·
    refine ⟨12348534727934196121627345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16464712970578928162169793 12348534727934196121627345)
    ·
      refine ⟨9261401045950647091220509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12348534727934196121627345 9261401045950647091220509)
      ·
        refine ⟨3473025392231492659207691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9261401045950647091220509 3473025392231492659207691)
        ·
          refine ⟨5209538088347238988811537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3473025392231492659207691 5209538088347238988811537)
          ·
            refine ⟨3907153566260429241608653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5209538088347238988811537 3907153566260429241608653)
            ·
              refine ⟨1465182587347660965603245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3907153566260429241608653 1465182587347660965603245)
              ·
                refine ⟨549443470255372862101217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1465182587347660965603245 549443470255372862101217)
                ·
                  refine ⟨412082602691529646575913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549443470255372862101217 412082602691529646575913)
                  ·
                    rfl

theorem cell20_902844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_902844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902844 prefixEnd_902844 := by exact prefixLift 902844
  have htrace : WordTrace (prefixWord ++ tailWord_902844) baseStart_902844 baseEnd_902844 := by
    simpa [prefixWord, tailWord_902844, baseEnd_902844] using wordTrace_append hprefix tailTrace_902844
  have hstable : (prefixWord ++ tailWord_902844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902844).length < 2 ^ (prefixWord ++ tailWord_902844).sum := by decide
  have hdescent : baseEnd_902844 < baseStart_902844 := by decide
  rcases family_descends (prefixWord ++ tailWord_902844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902861 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 4]
def baseStart_902861 : Nat := 118140960795 + 902861 * 2 ^ 59
def prefixEnd_902861 : Nat := 4983230072969 + 3 ^ 40 * 902861 * 2
def baseEnd_902861 : Nat := 412090361954753143009177

theorem tailTrace_902861 : CollatzResearch.WordTrace tailWord_902861 prefixEnd_902861 412090361954753143009177 := by
  unfold tailWord_902861
  simp only [CollatzResearch.WordTrace]
  refine ⟨32930045982096268227708437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21953363988064178818472291 32930045982096268227708437)
  ·
    refine ⟨1543595905410762573173833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32930045982096268227708437 1543595905410762573173833)
    ·
      refine ⟨1157696929058071929880375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1543595905410762573173833 1157696929058071929880375)
      ·
        refine ⟨1736545393587107894820563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1157696929058071929880375 1736545393587107894820563)
        ·
          refine ⟨2604818090380661842230845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736545393587107894820563 2604818090380661842230845)
          ·
            refine ⟨976806783892748190836567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2604818090380661842230845 976806783892748190836567)
            ·
              refine ⟨1465210175839122286254851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976806783892748190836567 1465210175839122286254851)
              ·
                refine ⟨2197815263758683429382277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465210175839122286254851 2197815263758683429382277)
                ·
                  refine ⟨412090361954753143009177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2197815263758683429382277 412090361954753143009177)
                  ·
                    rfl

theorem cell20_902861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_902861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902861 prefixEnd_902861 := by exact prefixLift 902861
  have htrace : WordTrace (prefixWord ++ tailWord_902861) baseStart_902861 baseEnd_902861 := by
    simpa [prefixWord, tailWord_902861, baseEnd_902861] using wordTrace_append hprefix tailTrace_902861
  have hstable : (prefixWord ++ tailWord_902861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902861).length < 2 ^ (prefixWord ++ tailWord_902861).sum := by decide
  have hdescent : baseEnd_902861 < baseStart_902861 := by decide
  rcases family_descends (prefixWord ++ tailWord_902861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902865 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 4]
def baseStart_902865 : Nat := 118140960795 + 902865 * 2 ^ 59
def prefixEnd_902865 : Nat := 4983230072969 + 3 ^ 40 * 902865 * 2
def baseEnd_902865 : Nat := 412092187663746906875827

theorem tailTrace_902865 : CollatzResearch.WordTrace tailWord_902865 prefixEnd_902865 412092187663746906875827 := by
  unfold tailWord_902865
  simp only [CollatzResearch.WordTrace]
  refine ⟨32930191874081776910854049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21953461249387851273902699 32930191874081776910854049)
  ·
    refine ⟨24697643905561332683140537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32930191874081776910854049 24697643905561332683140537)
    ·
      refine ⟨18523232929170999512355403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24697643905561332683140537 18523232929170999512355403)
      ·
        refine ⟨27784849393756499268533105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18523232929170999512355403 27784849393756499268533105)
        ·
          refine ⟨20838637045317374451399829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27784849393756499268533105 20838637045317374451399829)
          ·
            refine ⟨976811111499251927409367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20838637045317374451399829 976811111499251927409367)
            ·
              refine ⟨1465216667248877891114051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976811111499251927409367 1465216667248877891114051)
              ·
                refine ⟨2197825000873316836671077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465216667248877891114051 2197825000873316836671077)
                ·
                  refine ⟨412092187663746906875827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2197825000873316836671077 412092187663746906875827)
                  ·
                    rfl

theorem cell20_902865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_902865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902865 prefixEnd_902865 := by exact prefixLift 902865
  have htrace : WordTrace (prefixWord ++ tailWord_902865) baseStart_902865 baseEnd_902865 := by
    simpa [prefixWord, tailWord_902865, baseEnd_902865] using wordTrace_append hprefix tailTrace_902865
  have hstable : (prefixWord ++ tailWord_902865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902865).length < 2 ^ (prefixWord ++ tailWord_902865).sum := by decide
  have hdescent : baseEnd_902865 < baseStart_902865 := by decide
  rcases family_descends (prefixWord ++ tailWord_902865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902879 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 3]
def baseStart_902879 : Nat := 118140960795 + 902879 * 2 ^ 59
def prefixEnd_902879 : Nat := 4983230072969 + 3 ^ 40 * 902879 * 2
def baseEnd_902879 : Nat := 412098577645225080409103

theorem tailTrace_902879 : CollatzResearch.WordTrace tailWord_902879 prefixEnd_902879 412098577645225080409103 := by
  unfold tailWord_902879
  simp only [CollatzResearch.WordTrace]
  refine ⟨32930702496031057301863691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21953801664020704867909127 32930702496031057301863691)
  ·
    refine ⟨49396053744046585952795537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32930702496031057301863691 49396053744046585952795537)
    ·
      refine ⟨37047040308034939464596653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49396053744046585952795537 37047040308034939464596653)
      ·
        refine ⟨13892640115513102299223745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37047040308034939464596653 13892640115513102299223745)
        ·
          refine ⟨10419480086634826724417809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13892640115513102299223745 10419480086634826724417809)
          ·
            refine ⟨7814610064976120043313357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10419480086634826724417809 7814610064976120043313357)
            ·
              refine ⟨2930478774366045016242509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7814610064976120043313357 2930478774366045016242509)
              ·
                refine ⟨1098929540387266881090941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2930478774366045016242509 1098929540387266881090941)
                ·
                  refine ⟨412098577645225080409103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098929540387266881090941 412098577645225080409103)
                  ·
                    rfl

theorem cell20_902879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 3].length) (baseStart_902879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902879 prefixEnd_902879 := by exact prefixLift 902879
  have htrace : WordTrace (prefixWord ++ tailWord_902879) baseStart_902879 baseEnd_902879 := by
    simpa [prefixWord, tailWord_902879, baseEnd_902879] using wordTrace_append hprefix tailTrace_902879
  have hstable : (prefixWord ++ tailWord_902879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902879).length < 2 ^ (prefixWord ++ tailWord_902879).sum := by decide
  have hdescent : baseEnd_902879 < baseStart_902879 := by decide
  rcases family_descends (prefixWord ++ tailWord_902879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902907 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_902907 : Nat := 118140960795 + 902907 * 2 ^ 59
def prefixEnd_902907 : Nat := 4983230072969 + 3 ^ 40 * 902907 * 2
def baseEnd_902907 : Nat := 412111357608181427475655

theorem tailTrace_902907 : CollatzResearch.WordTrace tailWord_902907 prefixEnd_902907 412111357608181427475655 := by
  unfold tailWord_902907
  simp only [CollatzResearch.WordTrace]
  refine ⟨32931723739929618083882975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21954482493286412055921983 32931723739929618083882975)
  ·
    refine ⟨49397585609894427125824463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32931723739929618083882975 49397585609894427125824463)
    ·
      refine ⟨74096378414841640688736695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49397585609894427125824463 74096378414841640688736695)
      ·
        refine ⟨111144567622262461033105043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74096378414841640688736695 111144567622262461033105043)
        ·
          refine ⟨166716851433393691549657565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111144567622262461033105043 166716851433393691549657565)
          ·
            refine ⟨62518819287522634331121587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166716851433393691549657565 62518819287522634331121587)
            ·
              refine ⟨93778228931283951496682381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62518819287522634331121587 93778228931283951496682381)
              ·
                refine ⟨35166835849231481811255893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93778228931283951496682381 35166835849231481811255893)
                ·
                  refine ⟨412111357608181427475655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35166835849231481811255893 412111357608181427475655)
                  ·
                    rfl

theorem cell20_902907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_902907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902907 prefixEnd_902907 := by exact prefixLift 902907
  have htrace : WordTrace (prefixWord ++ tailWord_902907) baseStart_902907 baseEnd_902907 := by
    simpa [prefixWord, tailWord_902907, baseEnd_902907] using wordTrace_append hprefix tailTrace_902907
  have hstable : (prefixWord ++ tailWord_902907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902907).length < 2 ^ (prefixWord ++ tailWord_902907).sum := by decide
  have hdescent : baseEnd_902907 < baseStart_902907 := by decide
  rcases family_descends (prefixWord ++ tailWord_902907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902910 : List Nat := [4, 2, 2, 1, 3, 8]
def baseStart_902910 : Nat := 118140960795 + 902910 * 2 ^ 59
def prefixEnd_902910 : Nat := 4983230072969 + 3 ^ 40 * 902910 * 2
def baseEnd_902910 : Nat := 15263434329256546310209

theorem tailTrace_902910 : CollatzResearch.WordTrace tailWord_902910 prefixEnd_902910 15263434329256546310209 := by
  unfold tailWord_902910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116479144864843699530273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21954555439279166397494789 4116479144864843699530273)
  ·
    refine ⟨3087359358648632774647705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4116479144864843699530273 3087359358648632774647705)
    ·
      refine ⟨2315519518986474580985779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3087359358648632774647705 2315519518986474580985779)
      ·
        refine ⟨3473279278479711871478669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2315519518986474580985779 3473279278479711871478669)
        ·
          refine ⟨1302479729429891951804501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3473279278479711871478669 1302479729429891951804501)
          ·
            refine ⟨15263434329256546310209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1302479729429891951804501 15263434329256546310209)
            ·
              rfl

theorem cell20_902910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 8].length) (baseStart_902910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902910 prefixEnd_902910 := by exact prefixLift 902910
  have htrace : WordTrace (prefixWord ++ tailWord_902910) baseStart_902910 baseEnd_902910 := by
    simpa [prefixWord, tailWord_902910, baseEnd_902910] using wordTrace_append hprefix tailTrace_902910
  have hstable : (prefixWord ++ tailWord_902910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902910).length < 2 ^ (prefixWord ++ tailWord_902910).sum := by decide
  have hdescent : baseEnd_902910 < baseStart_902910 := by decide
  rcases family_descends (prefixWord ++ tailWord_902910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902979 : List Nat := [1, 1, 1, 3, 1, 5, 2, 4, 2]
def baseStart_902979 : Nat := 118140960795 + 902979 * 2 ^ 59
def prefixEnd_902979 : Nat := 4983230072969 + 3 ^ 40 * 902979 * 2
def baseEnd_902979 : Nat := 412144220370069177075361

theorem tailTrace_902979 : CollatzResearch.WordTrace tailWord_902979 prefixEnd_902979 412144220370069177075361 := by
  unfold tailWord_902979
  simp only [CollatzResearch.WordTrace]
  refine ⟨32934349795668774380503991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21956233197112516253669327 32934349795668774380503991)
  ·
    refine ⟨49401524693503161570755987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32934349795668774380503991 49401524693503161570755987)
    ·
      refine ⟨74102287040254742356133981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49401524693503161570755987 74102287040254742356133981)
      ·
        refine ⟨27788357640095528383550243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74102287040254742356133981 27788357640095528383550243)
        ·
          refine ⟨41682536460143292575325365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27788357640095528383550243 41682536460143292575325365)
          ·
            refine ⟨3907737793138433678936753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41682536460143292575325365 3907737793138433678936753)
            ·
              refine ⟨2930803344853825259202565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3907737793138433678936753 2930803344853825259202565)
              ·
                refine ⟨549525627160092236100481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2930803344853825259202565 549525627160092236100481)
                ·
                  refine ⟨412144220370069177075361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549525627160092236100481 412144220370069177075361)
                  ·
                    rfl

theorem cell20_902979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 2].length) (baseStart_902979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_902979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_902979 prefixEnd_902979 := by exact prefixLift 902979
  have htrace : WordTrace (prefixWord ++ tailWord_902979) baseStart_902979 baseEnd_902979 := by
    simpa [prefixWord, tailWord_902979, baseEnd_902979] using wordTrace_append hprefix tailTrace_902979
  have hstable : (prefixWord ++ tailWord_902979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902979).length < 2 ^ (prefixWord ++ tailWord_902979).sum := by decide
  have hdescent : baseEnd_902979 < baseStart_902979 := by decide
  rcases family_descends (prefixWord ++ tailWord_902979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903007 : List Nat := [1, 1, 2, 3, 1, 5, 1, 6]
def baseStart_903007 : Nat := 118140960795 + 903007 * 2 ^ 59
def prefixEnd_903007 : Nat := 4983230072969 + 3 ^ 40 * 903007 * 2
def baseEnd_903007 : Nat := 137385666777675174713971

theorem tailTrace_903007 : CollatzResearch.WordTrace tailWord_903007 prefixEnd_903007 137385666777675174713971 := by
  unfold tailWord_903007
  simp only [CollatzResearch.WordTrace]
  refine ⟨32935371039567335162523275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21956914026378223441682183 32935371039567335162523275)
  ·
    refine ⟨49403056559351002743784913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32935371039567335162523275 49403056559351002743784913)
    ·
      refine ⟨37052292419513252057838685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49403056559351002743784913 37052292419513252057838685)
      ·
        refine ⟨13894609657317469521689507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37052292419513252057838685 13894609657317469521689507)
        ·
          refine ⟨20841914485976204282534261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13894609657317469521689507 20841914485976204282534261)
          ·
            refine ⟨1953929483060269151487587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20841914485976204282534261 1953929483060269151487587)
            ·
              refine ⟨2930894224590403727231381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953929483060269151487587 2930894224590403727231381)
              ·
                refine ⟨137385666777675174713971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2930894224590403727231381 137385666777675174713971)
                ·
                  rfl

theorem cell20_903007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_903007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903007 prefixEnd_903007 := by exact prefixLift 903007
  have htrace : WordTrace (prefixWord ++ tailWord_903007) baseStart_903007 baseEnd_903007 := by
    simpa [prefixWord, tailWord_903007, baseEnd_903007] using wordTrace_append hprefix tailTrace_903007
  have hstable : (prefixWord ++ tailWord_903007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903007).length < 2 ^ (prefixWord ++ tailWord_903007).sum := by decide
  have hdescent : baseEnd_903007 < baseStart_903007 := by decide
  rcases family_descends (prefixWord ++ tailWord_903007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903030 : List Nat := [5, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_903030 : Nat := 118140960795 + 903030 * 2 ^ 59
def prefixEnd_903030 : Nat := 4983230072969 + 3 ^ 40 * 903030 * 2
def baseEnd_903030 : Nat := 412167498159739666375153

theorem tailTrace_903030 : CollatzResearch.WordTrace tailWord_903030 prefixEnd_903030 412167498159739666375153 := by
  unfold tailWord_903030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2058513119905250630663159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21957473278989340060407029 2058513119905250630663159)
  ·
    refine ⟨3087769679857875945994739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2058513119905250630663159 3087769679857875945994739)
    ·
      refine ⟨4631654519786813918992109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3087769679857875945994739 4631654519786813918992109)
      ·
        refine ⟨1736870444920055219622041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4631654519786813918992109 1736870444920055219622041)
        ·
          refine ⟨1302652833690041414716531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1736870444920055219622041 1302652833690041414716531)
          ·
            refine ⟨1953979250535062122074797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302652833690041414716531 1953979250535062122074797)
            ·
              refine ⟨732742218950648295778049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1953979250535062122074797 732742218950648295778049)
              ·
                refine ⟨549556664212986221833537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 732742218950648295778049 549556664212986221833537)
                ·
                  refine ⟨412167498159739666375153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549556664212986221833537 412167498159739666375153)
                  ·
                    rfl

theorem cell20_903030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_903030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903030 prefixEnd_903030 := by exact prefixLift 903030
  have htrace : WordTrace (prefixWord ++ tailWord_903030) baseStart_903030 baseEnd_903030 := by
    simpa [prefixWord, tailWord_903030, baseEnd_903030] using wordTrace_append hprefix tailTrace_903030
  have hstable : (prefixWord ++ tailWord_903030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903030).length < 2 ^ (prefixWord ++ tailWord_903030).sum := by decide
  have hdescent : baseEnd_903030 < baseStart_903030 := by decide
  rcases family_descends (prefixWord ++ tailWord_903030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903041 : List Nat := [1, 2, 4, 4, 1, 1, 2, 5]
def baseStart_903041 : Nat := 118140960795 + 903041 * 2 ^ 59
def prefixEnd_903041 : Nat := 4983230072969 + 3 ^ 40 * 903041 * 2
def baseEnd_903041 : Nat := 137390839619824172336147

theorem tailTrace_903041 : CollatzResearch.WordTrace tailWord_903041 prefixEnd_903041 137390839619824172336147 := by
  unfold tailWord_903041
  simp only [CollatzResearch.WordTrace]
  refine ⟨32936611121444158969260977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21957740747629439312840651 32936611121444158969260977)
  ·
    refine ⟨24702458341083119226945733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32936611121444158969260977 24702458341083119226945733)
    ·
      refine ⟨4631710938953084855052325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24702458341083119226945733 4631710938953084855052325)
      ·
        refine ⟨868445801053703410322311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4631710938953084855052325 868445801053703410322311)
        ·
          refine ⟨1302668701580555115483467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868445801053703410322311 1302668701580555115483467)
          ·
            refine ⟨1954003052370832673225201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302668701580555115483467 1954003052370832673225201)
            ·
              refine ⟨1465502289278124504918901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954003052370832673225201 1465502289278124504918901)
              ·
                refine ⟨137390839619824172336147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1465502289278124504918901 137390839619824172336147)
                ·
                  rfl

theorem cell20_903041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 5].length) (baseStart_903041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903041 prefixEnd_903041 := by exact prefixLift 903041
  have htrace : WordTrace (prefixWord ++ tailWord_903041) baseStart_903041 baseEnd_903041 := by
    simpa [prefixWord, tailWord_903041, baseEnd_903041] using wordTrace_append hprefix tailTrace_903041
  have hstable : (prefixWord ++ tailWord_903041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903041).length < 2 ^ (prefixWord ++ tailWord_903041).sum := by decide
  have hdescent : baseEnd_903041 < baseStart_903041 := by decide
  rcases family_descends (prefixWord ++ tailWord_903041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903045 : List Nat := [1, 3, 1, 1, 3, 2, 4, 5]
def baseStart_903045 : Nat := 118140960795 + 903045 * 2 ^ 59
def prefixEnd_903045 : Nat := 4983230072969 + 3 ^ 40 * 903045 * 2
def baseEnd_903045 : Nat := 137391448189488760291697

theorem tailTrace_903045 : CollatzResearch.WordTrace tailWord_903045 prefixEnd_903045 137391448189488760291697 := by
  unfold tailWord_903045
  simp only [CollatzResearch.WordTrace]
  refine ⟨32936757013429667652406589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21957838008953111768271059 32936757013429667652406589)
  ·
    refine ⟨12351283880036125369652471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32936757013429667652406589 12351283880036125369652471)
    ·
      refine ⟨18526925820054188054478707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12351283880036125369652471 18526925820054188054478707)
      ·
        refine ⟨27790388730081282081718061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18526925820054188054478707 27790388730081282081718061)
        ·
          refine ⟨10421395773780480780644273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27790388730081282081718061 10421395773780480780644273)
          ·
            refine ⟨7816046830335360585483205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10421395773780480780644273 7816046830335360585483205)
            ·
              refine ⟨1465508780687880109778101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7816046830335360585483205 1465508780687880109778101)
              ·
                refine ⟨137391448189488760291697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1465508780687880109778101 137391448189488760291697)
                ·
                  rfl

theorem cell20_903045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_903045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903045 prefixEnd_903045 := by exact prefixLift 903045
  have htrace : WordTrace (prefixWord ++ tailWord_903045) baseStart_903045 baseEnd_903045 := by
    simpa [prefixWord, tailWord_903045, baseEnd_903045] using wordTrace_append hprefix tailTrace_903045
  have hstable : (prefixWord ++ tailWord_903045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903045).length < 2 ^ (prefixWord ++ tailWord_903045).sum := by decide
  have hdescent : baseEnd_903045 < baseStart_903045 := by decide
  rcases family_descends (prefixWord ++ tailWord_903045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903048 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 3]
def baseStart_903048 : Nat := 118140960795 + 903048 * 2 ^ 59
def prefixEnd_903048 : Nat := 4983230072969 + 3 ^ 40 * 903048 * 2
def baseEnd_903048 : Nat := 412175713850211603775079

theorem tailTrace_903048 : CollatzResearch.WordTrace tailWord_903048 prefixEnd_903048 412175713850211603775079 := by
  unfold tailWord_903048
  simp only [CollatzResearch.WordTrace]
  refine ⟨16468433216209399582382899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21957910954945866109843865 16468433216209399582382899)
  ·
    refine ⟨24702649824314099373574349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16468433216209399582382899 24702649824314099373574349)
    ·
      refine ⟨9263493684117787265090381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24702649824314099373574349 9263493684117787265090381)
      ·
        refine ⟨3473810131544170224408893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9263493684117787265090381 3473810131544170224408893)
        ·
          refine ⟨1302678799329063834153335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3473810131544170224408893 1302678799329063834153335)
          ·
            refine ⟨1954018198993595751230003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302678799329063834153335 1954018198993595751230003)
            ·
              refine ⟨2931027298490393626845005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954018198993595751230003 2931027298490393626845005)
              ·
                refine ⟨1099135236933897610066877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2931027298490393626845005 1099135236933897610066877)
                ·
                  refine ⟨412175713850211603775079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099135236933897610066877 412175713850211603775079)
                  ·
                    rfl

theorem cell20_903048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_903048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903048 prefixEnd_903048 := by exact prefixLift 903048
  have htrace : WordTrace (prefixWord ++ tailWord_903048) baseStart_903048 baseEnd_903048 := by
    simpa [prefixWord, tailWord_903048, baseEnd_903048] using wordTrace_append hprefix tailTrace_903048
  have hstable : (prefixWord ++ tailWord_903048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903048).length < 2 ^ (prefixWord ++ tailWord_903048).sum := by decide
  have hdescent : baseEnd_903048 < baseStart_903048 := by decide
  rcases family_descends (prefixWord ++ tailWord_903048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903089 : List Nat := [1, 2, 2, 4, 2, 3, 2, 2, 2]
def baseStart_903089 : Nat := 118140960795 + 903089 * 2 ^ 59
def prefixEnd_903089 : Nat := 4983230072969 + 3 ^ 40 * 903089 * 2
def baseEnd_903089 : Nat := 412194427367397683408245

theorem tailTrace_903089 : CollatzResearch.WordTrace tailWord_903089 prefixEnd_903089 412194427367397683408245 := by
  unfold tailWord_903089
  simp only [CollatzResearch.WordTrace]
  refine ⟨32938361825270263167008321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21958907883513508778005547 32938361825270263167008321)
  ·
    refine ⟨24703771368952697375256241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32938361825270263167008321 24703771368952697375256241)
    ·
      refine ⟨18527828526714523031442181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24703771368952697375256241 18527828526714523031442181)
      ·
        refine ⟨3473967848758973068395409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18527828526714523031442181 3473967848758973068395409)
        ·
          refine ⟨2605475886569229801296557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3473967848758973068395409 2605475886569229801296557)
          ·
            refine ⟨977053457463461175486209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2605475886569229801296557 977053457463461175486209)
            ·
              refine ⟨732790093097595881614657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977053457463461175486209 732790093097595881614657)
              ·
                refine ⟨549592569823196911210993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 732790093097595881614657 549592569823196911210993)
                ·
                  refine ⟨412194427367397683408245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549592569823196911210993 412194427367397683408245)
                  ·
                    rfl

theorem cell20_903089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_903089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903089 prefixEnd_903089 := by exact prefixLift 903089
  have htrace : WordTrace (prefixWord ++ tailWord_903089) baseStart_903089 baseEnd_903089 := by
    simpa [prefixWord, tailWord_903089, baseEnd_903089] using wordTrace_append hprefix tailTrace_903089
  have hstable : (prefixWord ++ tailWord_903089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903089).length < 2 ^ (prefixWord ++ tailWord_903089).sum := by decide
  have hdescent : baseEnd_903089 < baseStart_903089 := by decide
  rcases family_descends (prefixWord ++ tailWord_903089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903090 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_903090 : Nat := 118140960795 + 903090 * 2 ^ 59
def prefixEnd_903090 : Nat := 4983230072969 + 3 ^ 40 * 903090 * 2
def baseEnd_903090 : Nat := 412194883794646124374907

theorem tailTrace_903090 : CollatzResearch.WordTrace tailWord_903090 prefixEnd_903090 412194883794646124374907 := by
  unfold tailWord_903090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8234599574566660084448681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21958932198844426891863149 8234599574566660084448681)
  ·
    refine ⟨6175949680924995063336511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8234599574566660084448681 6175949680924995063336511)
    ·
      refine ⟨9263924521387492595004767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175949680924995063336511 9263924521387492595004767)
      ·
        refine ⟨13895886782081238892507151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9263924521387492595004767 13895886782081238892507151)
        ·
          refine ⟨20843830173121858338760727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13895886782081238892507151 20843830173121858338760727)
          ·
            refine ⟨31265745259682787508141091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20843830173121858338760727 31265745259682787508141091)
            ·
              refine ⟨46898617889524181262211637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31265745259682787508141091 46898617889524181262211637)
              ·
                refine ⟨4396745427142891993332341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46898617889524181262211637 4396745427142891993332341)
                ·
                  refine ⟨412194883794646124374907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4396745427142891993332341 412194883794646124374907)
                  ·
                    rfl

theorem cell20_903090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_903090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903090 prefixEnd_903090 := by exact prefixLift 903090
  have htrace : WordTrace (prefixWord ++ tailWord_903090) baseStart_903090 baseEnd_903090 := by
    simpa [prefixWord, tailWord_903090, baseEnd_903090] using wordTrace_append hprefix tailTrace_903090
  have hstable : (prefixWord ++ tailWord_903090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903090).length < 2 ^ (prefixWord ++ tailWord_903090).sum := by decide
  have hdescent : baseEnd_903090 < baseStart_903090 := by decide
  rcases family_descends (prefixWord ++ tailWord_903090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903128 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_903128 : Nat := 118140960795 + 903128 * 2 ^ 59
def prefixEnd_903128 : Nat := 4983230072969 + 3 ^ 40 * 903128 * 2
def baseEnd_903128 : Nat := 412212228030086881108085

theorem tailTrace_903128 : CollatzResearch.WordTrace tailWord_903128 prefixEnd_903128 412212228030086881108085 := by
  unfold tailWord_903128
  simp only [CollatzResearch.WordTrace]
  refine ⟨16469892136064486413839019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21959856181419315218452025 16469892136064486413839019)
  ·
    refine ⟨24704838204096729620758529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16469892136064486413839019 24704838204096729620758529)
    ·
      refine ⟨18528628653072547215568897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24704838204096729620758529 18528628653072547215568897)
      ·
        refine ⟨13896471489804410411676673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18528628653072547215568897 13896471489804410411676673)
        ·
          refine ⟨10422353617353307808757505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13896471489804410411676673 10422353617353307808757505)
          ·
            refine ⟨7816765213014980856568129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10422353617353307808757505 7816765213014980856568129)
            ·
              refine ⟨5862573909761235642426097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7816765213014980856568129 5862573909761235642426097)
              ·
                refine ⟨4396930432320926731819573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5862573909761235642426097 4396930432320926731819573)
                ·
                  refine ⟨412212228030086881108085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4396930432320926731819573 412212228030086881108085)
                  ·
                    rfl

theorem cell20_903128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_903128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903128 prefixEnd_903128 := by exact prefixLift 903128
  have htrace : WordTrace (prefixWord ++ tailWord_903128) baseStart_903128 baseEnd_903128 := by
    simpa [prefixWord, tailWord_903128, baseEnd_903128] using wordTrace_append hprefix tailTrace_903128
  have hstable : (prefixWord ++ tailWord_903128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903128).length < 2 ^ (prefixWord ++ tailWord_903128).sum := by decide
  have hdescent : baseEnd_903128 < baseStart_903128 := by decide
  rcases family_descends (prefixWord ++ tailWord_903128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903172 : List Nat := [2, 3, 2, 4, 1, 2, 2, 4]
def baseStart_903172 : Nat := 118140960795 + 903172 * 2 ^ 59
def prefixEnd_903172 : Nat := 4983230072969 + 3 ^ 40 * 903172 * 2
def baseEnd_903172 : Nat := 137410770276339427880413

theorem tailTrace_903172 : CollatzResearch.WordTrace tailWord_903172 prefixEnd_903172 137410770276339427880413 := by
  unfold tailWord_903172
  simp only [CollatzResearch.WordTrace]
  refine ⟨16470694541984784171139885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21960926055979712228186513 16470694541984784171139885)
  ·
    refine ⟨6176510453244294064177457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16470694541984784171139885 6176510453244294064177457)
    ·
      refine ⟨4632382839933220548133093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6176510453244294064177457 4632382839933220548133093)
      ·
        refine ⟨868571782487478852774955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4632382839933220548133093 868571782487478852774955)
        ·
          refine ⟨1302857673731218279162433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868571782487478852774955 1302857673731218279162433)
          ·
            refine ⟨977143255298413709371825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1302857673731218279162433 977143255298413709371825)
            ·
              refine ⟨732857441473810282028869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977143255298413709371825 732857441473810282028869)
              ·
                refine ⟨137410770276339427880413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 732857441473810282028869 137410770276339427880413)
                ·
                  rfl

theorem cell20_903172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_903172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903172 prefixEnd_903172 := by exact prefixLift 903172
  have htrace : WordTrace (prefixWord ++ tailWord_903172) baseStart_903172 baseEnd_903172 := by
    simpa [prefixWord, tailWord_903172, baseEnd_903172] using wordTrace_append hprefix tailTrace_903172
  have hstable : (prefixWord ++ tailWord_903172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903172).length < 2 ^ (prefixWord ++ tailWord_903172).sum := by decide
  have hdescent : baseEnd_903172 < baseStart_903172 := by decide
  rcases family_descends (prefixWord ++ tailWord_903172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903197 : List Nat := [1, 4, 2, 2, 2, 1, 8]
def baseStart_903197 : Nat := 118140960795 + 903197 * 2 ^ 59
def prefixEnd_903197 : Nat := 4983230072969 + 3 ^ 40 * 903197 * 2
def baseEnd_903197 : Nat := 45804857945581034200867

theorem tailTrace_903197 : CollatzResearch.WordTrace tailWord_903197 prefixEnd_903197 45804857945581034200867 := by
  unfold tailWord_903197
  simp only [CollatzResearch.WordTrace]
  refine ⟨32942300908878997611939845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21961533939252665074626563 32942300908878997611939845)
  ·
    refine ⟨6176681420414812052238721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32942300908878997611939845 6176681420414812052238721)
    ·
      refine ⟨4632511065311109039179041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6176681420414812052238721 4632511065311109039179041)
      ·
        refine ⟨3474383298983331779384281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4632511065311109039179041 3474383298983331779384281)
        ·
          refine ⟨2605787474237498834538211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3474383298983331779384281 2605787474237498834538211)
          ·
            refine ⟨3908681211356248251807317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605787474237498834538211 3908681211356248251807317)
            ·
              refine ⟨45804857945581034200867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3908681211356248251807317 45804857945581034200867)
              ·
                rfl

theorem cell20_903197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 8].length) (baseStart_903197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903197 prefixEnd_903197 := by exact prefixLift 903197
  have htrace : WordTrace (prefixWord ++ tailWord_903197) baseStart_903197 baseEnd_903197 := by
    simpa [prefixWord, tailWord_903197, baseEnd_903197] using wordTrace_append hprefix tailTrace_903197
  have hstable : (prefixWord ++ tailWord_903197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903197).length < 2 ^ (prefixWord ++ tailWord_903197).sum := by decide
  have hdescent : baseEnd_903197 < baseStart_903197 := by decide
  rcases family_descends (prefixWord ++ tailWord_903197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903211 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_903211 : Nat := 118140960795 + 903211 * 2 ^ 59
def prefixEnd_903211 : Nat := 4983230072969 + 3 ^ 40 * 903211 * 2
def baseEnd_903211 : Nat := 412250111491707481341079

theorem tailTrace_903211 : CollatzResearch.WordTrace tailWord_903211 prefixEnd_903211 412250111491707481341079 := by
  unfold tailWord_903211
  simp only [CollatzResearch.WordTrace]
  refine ⟨32942811530828278002949487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21961874353885518668632991 32942811530828278002949487)
  ·
    refine ⟨49414217296242417004424231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32942811530828278002949487 49414217296242417004424231)
    ·
      refine ⟨74121325944363625506636347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49414217296242417004424231 74121325944363625506636347)
      ·
        refine ⟨111181988916545438259954521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74121325944363625506636347 111181988916545438259954521)
        ·
          refine ⟨83386491687409078694965891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111181988916545438259954521 83386491687409078694965891)
          ·
            refine ⟨125079737531113618042448837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83386491687409078694965891 125079737531113618042448837)
            ·
              refine ⟨23452450787083803382959157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125079737531113618042448837 23452450787083803382959157)
              ·
                refine ⟨2198667261289106567152421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23452450787083803382959157 2198667261289106567152421)
                ·
                  refine ⟨412250111491707481341079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2198667261289106567152421 412250111491707481341079)
                  ·
                    rfl

theorem cell20_903211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_903211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903211 prefixEnd_903211 := by exact prefixLift 903211
  have htrace : WordTrace (prefixWord ++ tailWord_903211) baseStart_903211 baseEnd_903211 := by
    simpa [prefixWord, tailWord_903211, baseEnd_903211] using wordTrace_append hprefix tailTrace_903211
  have hstable : (prefixWord ++ tailWord_903211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903211).length < 2 ^ (prefixWord ++ tailWord_903211).sum := by decide
  have hdescent : baseEnd_903211 < baseStart_903211 := by decide
  rcases family_descends (prefixWord ++ tailWord_903211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903214 : List Nat := [4, 1, 3, 1, 1, 3, 2, 5]
def baseStart_903214 : Nat := 118140960795 + 903214 * 2 ^ 59
def prefixEnd_903214 : Nat := 4983230072969 + 3 ^ 40 * 903214 * 2
def baseEnd_903214 : Nat := 137417160257817601413689

theorem tailTrace_903214 : CollatzResearch.WordTrace tailWord_903214 prefixEnd_903214 137417160257817601413689 := by
  unfold tailWord_903214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117865118727176189413587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21961947299878273010205797 4117865118727176189413587)
  ·
    refine ⟨6176797678090764284120381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4117865118727176189413587 6176797678090764284120381)
    ·
      refine ⟨2316299129284036606545143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6176797678090764284120381 2316299129284036606545143)
      ·
        refine ⟨3474448693926054909817715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316299129284036606545143 3474448693926054909817715)
        ·
          refine ⟨5211673040889082364726573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474448693926054909817715 5211673040889082364726573)
          ·
            refine ⟨1954377390333405886772465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5211673040889082364726573 1954377390333405886772465)
            ·
              refine ⟨1465783042750054415079349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954377390333405886772465 1465783042750054415079349)
              ·
                refine ⟨137417160257817601413689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1465783042750054415079349 137417160257817601413689)
                ·
                  rfl

theorem cell20_903214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_903214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903214 prefixEnd_903214 := by exact prefixLift 903214
  have htrace : WordTrace (prefixWord ++ tailWord_903214) baseStart_903214 baseEnd_903214 := by
    simpa [prefixWord, tailWord_903214, baseEnd_903214] using wordTrace_append hprefix tailTrace_903214
  have hstable : (prefixWord ++ tailWord_903214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903214).length < 2 ^ (prefixWord ++ tailWord_903214).sum := by decide
  have hdescent : baseEnd_903214 < baseStart_903214 := by decide
  rcases family_descends (prefixWord ++ tailWord_903214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903256 : List Nat := [2, 1, 2, 2, 1, 12]
def baseStart_903256 : Nat := 118140960795 + 903256 * 2 ^ 59
def prefixEnd_903256 : Nat := 4983230072969 + 3 ^ 40 * 903256 * 2
def baseEnd_903256 : Nat := 15269283359921752771885

theorem tailTrace_903256 : CollatzResearch.WordTrace tailWord_903256 prefixEnd_903256 15269283359921752771885 := by
  unfold tailWord_903256
  simp only [CollatzResearch.WordTrace]
  refine ⟨16472226407832625344168811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21962968543776833792225081 16472226407832625344168811)
  ·
    refine ⟨24708339611748938016253217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16472226407832625344168811 24708339611748938016253217)
    ·
      refine ⟨18531254708811703512189913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24708339611748938016253217 18531254708811703512189913)
      ·
        refine ⟨13898441031608777634142435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18531254708811703512189913 13898441031608777634142435)
        ·
          refine ⟨20847661547413166451213653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13898441031608777634142435 20847661547413166451213653)
          ·
            refine ⟨15269283359921752771885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20847661547413166451213653 15269283359921752771885)
            ·
              rfl

theorem cell20_903256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 12].length) (baseStart_903256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903256 prefixEnd_903256 := by exact prefixLift 903256
  have htrace : WordTrace (prefixWord ++ tailWord_903256) baseStart_903256 baseEnd_903256 := by
    simpa [prefixWord, tailWord_903256, baseEnd_903256] using wordTrace_append hprefix tailTrace_903256
  have hstable : (prefixWord ++ tailWord_903256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903256).length < 2 ^ (prefixWord ++ tailWord_903256).sum := by decide
  have hdescent : baseEnd_903256 < baseStart_903256 := by decide
  rcases family_descends (prefixWord ++ tailWord_903256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903287 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_903287 : Nat := 118140960795 + 903287 * 2 ^ 59
def prefixEnd_903287 : Nat := 4983230072969 + 3 ^ 40 * 903287 * 2
def baseEnd_903287 : Nat := 412284799962588994807435

theorem tailTrace_903287 : CollatzResearch.WordTrace tailWord_903287 prefixEnd_903287 412284799962588994807435 := by
  unfold tailWord_903287
  simp only [CollatzResearch.WordTrace]
  refine ⟨32945583478552942982716115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21963722319035295321810743 32945583478552942982716115)
  ·
    refine ⟨49418375217829414474074173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32945583478552942982716115 49418375217829414474074173)
    ·
      refine ⟨18531890706686030427777815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49418375217829414474074173 18531890706686030427777815)
      ·
        refine ⟨27797836060029045641666723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18531890706686030427777815 27797836060029045641666723)
        ·
          refine ⟨41696754090043568462500085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27797836060029045641666723 41696754090043568462500085)
          ·
            refine ⟨3909070695941584543359383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41696754090043568462500085 3909070695941584543359383)
            ·
              refine ⟨5863606043912376815039075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909070695941584543359383 5863606043912376815039075)
              ·
                refine ⟨8795409065868565222558613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5863606043912376815039075 8795409065868565222558613)
                ·
                  refine ⟨412284799962588994807435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8795409065868565222558613 412284799962588994807435)
                  ·
                    rfl

theorem cell20_903287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_903287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903287 prefixEnd_903287 := by exact prefixLift 903287
  have htrace : WordTrace (prefixWord ++ tailWord_903287) baseStart_903287 baseEnd_903287 := by
    simpa [prefixWord, tailWord_903287, baseEnd_903287] using wordTrace_append hprefix tailTrace_903287
  have hstable : (prefixWord ++ tailWord_903287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903287).length < 2 ^ (prefixWord ++ tailWord_903287).sum := by decide
  have hdescent : baseEnd_903287 < baseStart_903287 := by decide
  rcases family_descends (prefixWord ++ tailWord_903287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903345 : List Nat := [1, 2, 2, 5, 2, 2, 2, 4]
def baseStart_903345 : Nat := 118140960795 + 903345 * 2 ^ 59
def prefixEnd_903345 : Nat := 4983230072969 + 3 ^ 40 * 903345 * 2
def baseEnd_903345 : Nat := 137437090914332856957955

theorem tailTrace_903345 : CollatzResearch.WordTrace tailWord_903345 prefixEnd_903345 137437090914332856957955 := by
  unfold tailWord_903345
  simp only [CollatzResearch.WordTrace]
  refine ⟨32947698912342818888327489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21965132608228545925551659 32947698912342818888327489)
  ·
    refine ⟨24710774184257114166245617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32947698912342818888327489 24710774184257114166245617)
    ·
      refine ⟨18533080638192835624684213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24710774184257114166245617 18533080638192835624684213)
      ·
        refine ⟨1737476309830578339814145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18533080638192835624684213 1737476309830578339814145)
        ·
          refine ⟨1303107232372933754860609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1737476309830578339814145 1303107232372933754860609)
          ·
            refine ⟨977330424279700316145457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1303107232372933754860609 977330424279700316145457)
            ·
              refine ⟨732997818209775237109093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977330424279700316145457 732997818209775237109093)
              ·
                refine ⟨137437090914332856957955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 732997818209775237109093 137437090914332856957955)
                ·
                  rfl

theorem cell20_903345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 4].length) (baseStart_903345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903345 prefixEnd_903345 := by exact prefixLift 903345
  have htrace : WordTrace (prefixWord ++ tailWord_903345) baseStart_903345 baseEnd_903345 := by
    simpa [prefixWord, tailWord_903345, baseEnd_903345] using wordTrace_append hprefix tailTrace_903345
  have hstable : (prefixWord ++ tailWord_903345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903345).length < 2 ^ (prefixWord ++ tailWord_903345).sum := by decide
  have hdescent : baseEnd_903345 < baseStart_903345 := by decide
  rcases family_descends (prefixWord ++ tailWord_903345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903428 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 3]
def baseStart_903428 : Nat := 118140960795 + 903428 * 2 ^ 59
def prefixEnd_903428 : Nat := 4983230072969 + 3 ^ 40 * 903428 * 2
def baseEnd_903428 : Nat := 412349156204619171106859

theorem tailTrace_903428 : CollatzResearch.WordTrace tailWord_903428 prefixEnd_903428 412349156204619171106859 := by
  unfold tailWord_903428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475363085521062031799469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21967150780694749375732625 16475363085521062031799469)
  ·
    refine ⟨6178261157070398261924801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16475363085521062031799469 6178261157070398261924801)
    ·
      refine ⟨4633695867802798696443601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6178261157070398261924801 4633695867802798696443601)
      ·
        refine ⟨3475271900852099022332701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4633695867802798696443601 3475271900852099022332701)
        ·
          refine ⟨1303226962819537133374763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3475271900852099022332701 1303226962819537133374763)
          ·
            refine ⟨1954840444229305700062145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303226962819537133374763 1954840444229305700062145)
            ·
              refine ⟨1466130333171979275046609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954840444229305700062145 1466130333171979275046609)
              ·
                refine ⟨1099597749878984456284957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466130333171979275046609 1099597749878984456284957)
                ·
                  refine ⟨412349156204619171106859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099597749878984456284957 412349156204619171106859)
                  ·
                    rfl

theorem cell20_903428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_903428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903428 prefixEnd_903428 := by exact prefixLift 903428
  have htrace : WordTrace (prefixWord ++ tailWord_903428) baseStart_903428 baseEnd_903428 := by
    simpa [prefixWord, tailWord_903428, baseEnd_903428] using wordTrace_append hprefix tailTrace_903428
  have hstable : (prefixWord ++ tailWord_903428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903428).length < 2 ^ (prefixWord ++ tailWord_903428).sum := by decide
  have hdescent : baseEnd_903428 < baseStart_903428 := by decide
  rcases family_descends (prefixWord ++ tailWord_903428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903456 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_903456 : Nat := 118140960795 + 903456 * 2 ^ 59
def prefixEnd_903456 : Nat := 4983230072969 + 3 ^ 40 * 903456 * 2
def baseEnd_903456 : Nat := 412361936167575518173411

theorem tailTrace_903456 : CollatzResearch.WordTrace tailWord_903456 prefixEnd_903456 412361936167575518173411 := by
  unfold tailWord_903456
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475873707470342422809111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21967831609960456563745481 16475873707470342422809111)
  ·
    refine ⟨24713810561205513634213667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16475873707470342422809111 24713810561205513634213667)
    ·
      refine ⟨37070715841808270451320501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24713810561205513634213667 37070715841808270451320501)
      ·
        refine ⟨3475379610169525354811297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37070715841808270451320501 3475379610169525354811297)
        ·
          refine ⟨2606534707627144016108473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3475379610169525354811297 2606534707627144016108473)
          ·
            refine ⟨1954901030720358012081355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2606534707627144016108473 1954901030720358012081355)
            ·
              refine ⟨2932351546080537018122033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954901030720358012081355 2932351546080537018122033)
              ·
                refine ⟨2199263659560402763591525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2932351546080537018122033 2199263659560402763591525)
                ·
                  refine ⟨412361936167575518173411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199263659560402763591525 412361936167575518173411)
                  ·
                    rfl

theorem cell20_903456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_903456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903456 prefixEnd_903456 := by exact prefixLift 903456
  have htrace : WordTrace (prefixWord ++ tailWord_903456) baseStart_903456 baseEnd_903456 := by
    simpa [prefixWord, tailWord_903456, baseEnd_903456] using wordTrace_append hprefix tailTrace_903456
  have hstable : (prefixWord ++ tailWord_903456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903456).length < 2 ^ (prefixWord ++ tailWord_903456).sum := by decide
  have hdescent : baseEnd_903456 < baseStart_903456 := by decide
  rcases family_descends (prefixWord ++ tailWord_903456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903469 : List Nat := [1, 5, 3, 1, 2, 1, 2, 3, 2]
def baseStart_903469 : Nat := 118140960795 + 903469 * 2 ^ 59
def prefixEnd_903469 : Nat := 4983230072969 + 3 ^ 40 * 903469 * 2
def baseEnd_903469 : Nat := 412367869721805250740025

theorem tailTrace_903469 : CollatzResearch.WordTrace tailWord_903469 prefixEnd_903469 412367869721805250740025 := by
  unfold tailWord_903469
  simp only [CollatzResearch.WordTrace]
  refine ⟨32952221563893588065841461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21968147709262392043894307 32952221563893588065841461)
  ·
    refine ⟨3089270771615023881172637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32952221563893588065841461 3089270771615023881172637)
    ·
      refine ⟨1158476539355633955439739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3089270771615023881172637 1158476539355633955439739)
      ·
        refine ⟨1737714809033450933159609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158476539355633955439739 1737714809033450933159609)
        ·
          refine ⟨1303286106775088199869707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1737714809033450933159609 1303286106775088199869707)
          ·
            refine ⟨1954929160162632299804561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303286106775088199869707 1954929160162632299804561)
            ·
              refine ⟨1466196870121974224853421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954929160162632299804561 1466196870121974224853421)
              ·
                refine ⟨549823826295740334320033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1466196870121974224853421 549823826295740334320033)
                ·
                  refine ⟨412367869721805250740025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549823826295740334320033 412367869721805250740025)
                  ·
                    rfl

theorem cell20_903469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_903469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903469 prefixEnd_903469 := by exact prefixLift 903469
  have htrace : WordTrace (prefixWord ++ tailWord_903469) baseStart_903469 baseEnd_903469 := by
    simpa [prefixWord, tailWord_903469, baseEnd_903469] using wordTrace_append hprefix tailTrace_903469
  have hstable : (prefixWord ++ tailWord_903469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903469).length < 2 ^ (prefixWord ++ tailWord_903469).sum := by decide
  have hdescent : baseEnd_903469 < baseStart_903469 := by decide
  rcases family_descends (prefixWord ++ tailWord_903469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903477 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_903477 : Nat := 118140960795 + 903477 * 2 ^ 59
def prefixEnd_903477 : Nat := 4983230072969 + 3 ^ 40 * 903477 * 2
def baseEnd_903477 : Nat := 412371521139792778473325

theorem tailTrace_903477 : CollatzResearch.WordTrace tailWord_903477 prefixEnd_903477 412371521139792778473325 := by
  unfold tailWord_903477
  simp only [CollatzResearch.WordTrace]
  refine ⟨32952513347864605432132685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21968342231909736954755123 32952513347864605432132685)
  ·
    refine ⟨12357192505449227037049757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32952513347864605432132685 12357192505449227037049757)
    ·
      refine ⟨4633947189543460138893659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12357192505449227037049757 4633947189543460138893659)
      ·
        refine ⟨6950920784315190208340489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4633947189543460138893659 6950920784315190208340489)
        ·
          refine ⟨5213190588236392656255367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6950920784315190208340489 5213190588236392656255367)
          ·
            refine ⟨7819785882354588984383051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213190588236392656255367 7819785882354588984383051)
            ·
              refine ⟨11729678823531883476574577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819785882354588984383051 11729678823531883476574577)
              ·
                refine ⟨8797259117648912607430933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11729678823531883476574577 8797259117648912607430933)
                ·
                  refine ⟨412371521139792778473325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8797259117648912607430933 412371521139792778473325)
                  ·
                    rfl

theorem cell20_903477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_903477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903477 prefixEnd_903477 := by exact prefixLift 903477
  have htrace : WordTrace (prefixWord ++ tailWord_903477) baseStart_903477 baseEnd_903477 := by
    simpa [prefixWord, tailWord_903477, baseEnd_903477] using wordTrace_append hprefix tailTrace_903477
  have hstable : (prefixWord ++ tailWord_903477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903477).length < 2 ^ (prefixWord ++ tailWord_903477).sum := by decide
  have hdescent : baseEnd_903477 < baseStart_903477 := by decide
  rcases family_descends (prefixWord ++ tailWord_903477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903484 : List Nat := [2, 2, 2, 2, 1, 2, 9]
def baseStart_903484 : Nat := 118140960795 + 903484 * 2 ^ 59
def prefixEnd_903484 : Nat := 4983230072969 + 3 ^ 40 * 903484 * 2
def baseEnd_903484 : Nat := 45819412903392429471107

theorem tailTrace_903484 : CollatzResearch.WordTrace tailWord_903484 prefixEnd_903484 45819412903392429471107 := by
  unfold tailWord_903484
  simp only [CollatzResearch.WordTrace]
  refine ⟨16476384329419622813818753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21968512439226163751758337 16476384329419622813818753)
  ·
    refine ⟨12357288247064717110364065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16476384329419622813818753 12357288247064717110364065)
    ·
      refine ⟨9267966185298537832773049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12357288247064717110364065 9267966185298537832773049)
      ·
        refine ⟨6950974638973903374579787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9267966185298537832773049 6950974638973903374579787)
        ·
          refine ⟨10426461958460855061869681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950974638973903374579787 10426461958460855061869681)
          ·
            refine ⟨7819846468845641296402261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10426461958460855061869681 7819846468845641296402261)
            ·
              refine ⟨45819412903392429471107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7819846468845641296402261 45819412903392429471107)
              ·
                rfl

theorem cell20_903484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 9].length) (baseStart_903484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903484 prefixEnd_903484 := by exact prefixLift 903484
  have htrace : WordTrace (prefixWord ++ tailWord_903484) baseStart_903484 baseEnd_903484 := by
    simpa [prefixWord, tailWord_903484, baseEnd_903484] using wordTrace_append hprefix tailTrace_903484
  have hstable : (prefixWord ++ tailWord_903484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903484).length < 2 ^ (prefixWord ++ tailWord_903484).sum := by decide
  have hdescent : baseEnd_903484 < baseStart_903484 := by decide
  rcases family_descends (prefixWord ++ tailWord_903484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903528 : List Nat := [2, 1, 4, 2, 2, 3, 1, 3, 2]
def baseStart_903528 : Nat := 118140960795 + 903528 * 2 ^ 59
def prefixEnd_903528 : Nat := 4983230072969 + 3 ^ 40 * 903528 * 2
def baseEnd_903528 : Nat := 412394798929463267773117

theorem tailTrace_903528 : CollatzResearch.WordTrace tailWord_903528 prefixEnd_903528 412394798929463267773117 := by
  unfold tailWord_903528
  simp only [CollatzResearch.WordTrace]
  refine ⟨16477186735339920571119619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21969582313786560761492825 16477186735339920571119619)
  ·
    refine ⟨24715780103009880856679429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16477186735339920571119619 24715780103009880856679429)
    ·
      refine ⟨4634208769314352660627393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24715780103009880856679429 4634208769314352660627393)
      ·
        refine ⟨3475656576985764495470545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4634208769314352660627393 3475656576985764495470545)
        ·
          refine ⟨2606742432739323371602909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3475656576985764495470545 2606742432739323371602909)
          ·
            refine ⟨977528412277246264351091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2606742432739323371602909 977528412277246264351091)
            ·
              refine ⟨1466292618415869396526637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977528412277246264351091 1466292618415869396526637)
              ·
                refine ⟨549859731905951023697489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1466292618415869396526637 549859731905951023697489)
                ·
                  refine ⟨412394798929463267773117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549859731905951023697489 412394798929463267773117)
                  ·
                    rfl

theorem cell20_903528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_903528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903528 prefixEnd_903528 := by exact prefixLift 903528
  have htrace : WordTrace (prefixWord ++ tailWord_903528) baseStart_903528 baseEnd_903528 := by
    simpa [prefixWord, tailWord_903528, baseEnd_903528] using wordTrace_append hprefix tailTrace_903528
  have hstable : (prefixWord ++ tailWord_903528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903528).length < 2 ^ (prefixWord ++ tailWord_903528).sum := by decide
  have hdescent : baseEnd_903528 < baseStart_903528 := by decide
  rcases family_descends (prefixWord ++ tailWord_903528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903529 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_903529 : Nat := 118140960795 + 903529 * 2 ^ 59
def prefixEnd_903529 : Nat := 4983230072969 + 3 ^ 40 * 903529 * 2
def baseEnd_903529 : Nat := 412395255356711708739779

theorem tailTrace_903529 : CollatzResearch.WordTrace tailWord_903529 prefixEnd_903529 412395255356711708739779 := by
  unfold tailWord_903529
  simp only [CollatzResearch.WordTrace]
  refine ⟨32954409943676218313025641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21969606629117478875350427 32954409943676218313025641)
  ·
    refine ⟨24715807457757163734769231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32954409943676218313025641 24715807457757163734769231)
    ·
      refine ⟨37073711186635745602153847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24715807457757163734769231 37073711186635745602153847)
      ·
        refine ⟨55610566779953618403230771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37073711186635745602153847 55610566779953618403230771)
        ·
          refine ⟨83415850169930427604846157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55610566779953618403230771 83415850169930427604846157)
          ·
            refine ⟨31280943813723910351817309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83415850169930427604846157 31280943813723910351817309)
            ·
              refine ⟨11730353930146466381931491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31280943813723910351817309 11730353930146466381931491)
              ·
                refine ⟨17595530895219699572897237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11730353930146466381931491 17595530895219699572897237)
                ·
                  refine ⟨412395255356711708739779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17595530895219699572897237 412395255356711708739779)
                  ·
                    rfl

theorem cell20_903529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_903529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903529 prefixEnd_903529 := by exact prefixLift 903529
  have htrace : WordTrace (prefixWord ++ tailWord_903529) baseStart_903529 baseEnd_903529 := by
    simpa [prefixWord, tailWord_903529, baseEnd_903529] using wordTrace_append hprefix tailTrace_903529
  have hstable : (prefixWord ++ tailWord_903529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903529).length < 2 ^ (prefixWord ++ tailWord_903529).sum := by decide
  have hdescent : baseEnd_903529 < baseStart_903529 := by decide
  rcases family_descends (prefixWord ++ tailWord_903529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903563 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 3]
def baseStart_903563 : Nat := 118140960795 + 903563 * 2 ^ 59
def prefixEnd_903563 : Nat := 4983230072969 + 3 ^ 40 * 903563 * 2
def baseEnd_903563 : Nat := 412410773883158701606307

theorem tailTrace_903563 : CollatzResearch.WordTrace tailWord_903563 prefixEnd_903563 412410773883158701606307 := by
  unfold tailWord_903563
  simp only [CollatzResearch.WordTrace]
  refine ⟨32955650025553042119763343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21970433350368694746508895 32955650025553042119763343)
  ·
    refine ⟨49433475038329563179645015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32955650025553042119763343 49433475038329563179645015)
    ·
      refine ⟨74150212557494344769467523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49433475038329563179645015 74150212557494344769467523)
      ·
        refine ⟨111225318836241517154201285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74150212557494344769467523 111225318836241517154201285)
        ·
          refine ⟨20854747281795284466412741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111225318836241517154201285 20854747281795284466412741)
          ·
            refine ⟨3910265115336615837452389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20854747281795284466412741 3910265115336615837452389)
            ·
              refine ⟨733174709125615469522323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3910265115336615837452389 733174709125615469522323)
              ·
                refine ⟨1099762063688423204283485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733174709125615469522323 1099762063688423204283485)
                ·
                  refine ⟨412410773883158701606307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099762063688423204283485 412410773883158701606307)
                  ·
                    rfl

theorem cell20_903563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 3].length) (baseStart_903563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903563 prefixEnd_903563 := by exact prefixLift 903563
  have htrace : WordTrace (prefixWord ++ tailWord_903563) baseStart_903563 baseEnd_903563 := by
    simpa [prefixWord, tailWord_903563, baseEnd_903563] using wordTrace_append hprefix tailTrace_903563
  have hstable : (prefixWord ++ tailWord_903563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903563).length < 2 ^ (prefixWord ++ tailWord_903563).sum := by decide
  have hdescent : baseEnd_903563 < baseStart_903563 := by decide
  rcases family_descends (prefixWord ++ tailWord_903563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903594 : List Nat := [3, 1, 6, 1, 9]
def baseStart_903594 : Nat := 118140960795 + 903594 * 2 ^ 59
def prefixEnd_903594 : Nat := 4983230072969 + 3 ^ 40 * 903594 * 2
def baseEnd_903594 : Nat := 5091665717627905821887

theorem tailTrace_903594 : CollatzResearch.WordTrace tailWord_903594 prefixEnd_903594 5091665717627905821887 := by
  unfold tailWord_903594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8239195172110183603535459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21971187125627156276094557 8239195172110183603535459)
  ·
    refine ⟨12358792758165275405303189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8239195172110183603535459 12358792758165275405303189)
    ·
      refine ⟨579318410538997284623587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12358792758165275405303189 579318410538997284623587)
      ·
        refine ⟨868977615808495926935381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579318410538997284623587 868977615808495926935381)
        ·
          refine ⟨5091665717627905821887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 868977615808495926935381 5091665717627905821887)
          ·
            rfl

theorem cell20_903594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 9].length) (baseStart_903594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903594 prefixEnd_903594 := by exact prefixLift 903594
  have htrace : WordTrace (prefixWord ++ tailWord_903594) baseStart_903594 baseEnd_903594 := by
    simpa [prefixWord, tailWord_903594, baseEnd_903594] using wordTrace_append hprefix tailTrace_903594
  have hstable : (prefixWord ++ tailWord_903594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903594).length < 2 ^ (prefixWord ++ tailWord_903594).sum := by decide
  have hdescent : baseEnd_903594 < baseStart_903594 := by decide
  rcases family_descends (prefixWord ++ tailWord_903594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903601 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 3]
def baseStart_903601 : Nat := 118140960795 + 903601 * 2 ^ 59
def prefixEnd_903601 : Nat := 4983230072969 + 3 ^ 40 * 903601 * 2
def baseEnd_903601 : Nat := 412428118118599458339485

theorem tailTrace_903601 : CollatzResearch.WordTrace tailWord_903601 prefixEnd_903601 412428118118599458339485 := by
  unfold tailWord_903601
  simp only [CollatzResearch.WordTrace]
  refine ⟨32957035999415374609646657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21971357332943583073097771 32957035999415374609646657)
  ·
    refine ⟨24717776999561530957234993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32957035999415374609646657 24717776999561530957234993)
    ·
      refine ⟨18538332749671148217926245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24717776999561530957234993 18538332749671148217926245)
      ·
        refine ⟨3475937390563340290861171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18538332749671148217926245 3475937390563340290861171)
        ·
          refine ⟨5213906085845010436291757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3475937390563340290861171 5213906085845010436291757)
          ·
            refine ⟨1955214782191878913609409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5213906085845010436291757 1955214782191878913609409)
            ·
              refine ⟨1466411086643909185207057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955214782191878913609409 1466411086643909185207057)
              ·
                refine ⟨1099808314982931888905293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466411086643909185207057 1099808314982931888905293)
                ·
                  refine ⟨412428118118599458339485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099808314982931888905293 412428118118599458339485)
                  ·
                    rfl

theorem cell20_903601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_903601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903601 prefixEnd_903601 := by exact prefixLift 903601
  have htrace : WordTrace (prefixWord ++ tailWord_903601) baseStart_903601 baseEnd_903601 := by
    simpa [prefixWord, tailWord_903601, baseEnd_903601] using wordTrace_append hprefix tailTrace_903601
  have hstable : (prefixWord ++ tailWord_903601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903601).length < 2 ^ (prefixWord ++ tailWord_903601).sum := by decide
  have hdescent : baseEnd_903601 < baseStart_903601 := by decide
  rcases family_descends (prefixWord ++ tailWord_903601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903653 : List Nat := [1, 3, 1, 5, 2, 1, 7]
def baseStart_903653 : Nat := 118140960795 + 903653 * 2 ^ 59
def prefixEnd_903653 : Nat := 4983230072969 + 3 ^ 40 * 903653 * 2
def baseEnd_903653 : Nat := 45827983592835376511771

theorem tailTrace_903653 : CollatzResearch.WordTrace tailWord_903653 prefixEnd_903653 45827983592835376511771 := by
  unfold tailWord_903653
  simp only [CollatzResearch.WordTrace]
  refine ⟨32958932595226987490539613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21972621730151324993693075 32958932595226987490539613)
  ·
    refine ⟨12359599723210120308952355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32958932595226987490539613 12359599723210120308952355)
    ·
      refine ⟨18539399584815180463428533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12359599723210120308952355 18539399584815180463428533)
      ·
        refine ⟨1738068711076423168446425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18539399584815180463428533 1738068711076423168446425)
        ·
          refine ⟨1303551533307317376334819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1738068711076423168446425 1303551533307317376334819)
          ·
            refine ⟨1955327299960976064502229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303551533307317376334819 1955327299960976064502229)
            ·
              refine ⟨45827983592835376511771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1955327299960976064502229 45827983592835376511771)
              ·
                rfl

theorem cell20_903653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 7].length) (baseStart_903653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903653 prefixEnd_903653 := by exact prefixLift 903653
  have htrace : WordTrace (prefixWord ++ tailWord_903653) baseStart_903653 baseEnd_903653 := by
    simpa [prefixWord, tailWord_903653, baseEnd_903653] using wordTrace_append hprefix tailTrace_903653
  have hstable : (prefixWord ++ tailWord_903653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903653).length < 2 ^ (prefixWord ++ tailWord_903653).sum := by decide
  have hdescent : baseEnd_903653 < baseStart_903653 := by decide
  rcases family_descends (prefixWord ++ tailWord_903653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903667 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 4]
def baseStart_903667 : Nat := 118140960795 + 903667 * 2 ^ 59
def prefixEnd_903667 : Nat := 4983230072969 + 3 ^ 40 * 903667 * 2
def baseEnd_903667 : Nat := 412458242316996562139215

theorem tailTrace_903667 : CollatzResearch.WordTrace tailWord_903667 prefixEnd_903667 412458242316996562139215 := by
  unfold tailWord_903667
  simp only [CollatzResearch.WordTrace]
  refine ⟨32959443217176267881549255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21972962144784178587699503 32959443217176267881549255)
  ·
    refine ⟨49439164825764401822323883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32959443217176267881549255 49439164825764401822323883)
    ·
      refine ⟨74158747238646602733485825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49439164825764401822323883 74158747238646602733485825)
      ·
        refine ⟨55619060428984952050114369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74158747238646602733485825 55619060428984952050114369)
        ·
          refine ⟨41714295321738714037585777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55619060428984952050114369 41714295321738714037585777)
          ·
            refine ⟨31285721491304035528189333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41714295321738714037585777 31285721491304035528189333)
            ·
              refine ⟨1466518194904876665383875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31285721491304035528189333 1466518194904876665383875)
              ·
                refine ⟨2199777292357314998075813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466518194904876665383875 2199777292357314998075813)
                ·
                  refine ⟨412458242316996562139215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199777292357314998075813 412458242316996562139215)
                  ·
                    rfl

theorem cell20_903667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_903667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903667 prefixEnd_903667 := by exact prefixLift 903667
  have htrace : WordTrace (prefixWord ++ tailWord_903667) baseStart_903667 baseEnd_903667 := by
    simpa [prefixWord, tailWord_903667, baseEnd_903667] using wordTrace_append hprefix tailTrace_903667
  have hstable : (prefixWord ++ tailWord_903667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903667).length < 2 ^ (prefixWord ++ tailWord_903667).sum := by decide
  have hdescent : baseEnd_903667 < baseStart_903667 := by decide
  rcases family_descends (prefixWord ++ tailWord_903667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903677 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 3]
def baseStart_903677 : Nat := 118140960795 + 903677 * 2 ^ 59
def prefixEnd_903677 : Nat := 4983230072969 + 3 ^ 40 * 903677 * 2
def baseEnd_903677 : Nat := 412462806589480971805841

theorem tailTrace_903677 : CollatzResearch.WordTrace tailWord_903677 prefixEnd_903677 412462806589480971805841 := by
  unfold tailWord_903677
  simp only [CollatzResearch.WordTrace]
  refine ⟨32959807947140039589413285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21973205298093359726275523 32959807947140039589413285)
  ·
    refine ⟨6179963990088757423014991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32959807947140039589413285 6179963990088757423014991)
    ·
      refine ⟨9269945985133136134522487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6179963990088757423014991 9269945985133136134522487)
      ·
        refine ⟨13904918977699704201783731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9269945985133136134522487 13904918977699704201783731)
        ·
          refine ⟨20857378466549556302675597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13904918977699704201783731 20857378466549556302675597)
          ·
            refine ⟨7821516924956083613503349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20857378466549556302675597 7821516924956083613503349)
            ·
              refine ⟨733267211714632838765939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7821516924956083613503349 733267211714632838765939)
              ·
                refine ⟨1099900817571949258148909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733267211714632838765939 1099900817571949258148909)
                ·
                  refine ⟨412462806589480971805841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099900817571949258148909 412462806589480971805841)
                  ·
                    rfl

theorem cell20_903677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_903677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903677 prefixEnd_903677 := by exact prefixLift 903677
  have htrace : WordTrace (prefixWord ++ tailWord_903677) baseStart_903677 baseEnd_903677 := by
    simpa [prefixWord, tailWord_903677, baseEnd_903677] using wordTrace_append hprefix tailTrace_903677
  have hstable : (prefixWord ++ tailWord_903677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903677).length < 2 ^ (prefixWord ++ tailWord_903677).sum := by decide
  have hdescent : baseEnd_903677 < baseStart_903677 := by decide
  rcases family_descends (prefixWord ++ tailWord_903677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903684 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_903684 : Nat := 118140960795 + 903684 * 2 ^ 59
def prefixEnd_903684 : Nat := 4983230072969 + 3 ^ 40 * 903684 * 2
def baseEnd_903684 : Nat := 412466001580220058572479

theorem tailTrace_903684 : CollatzResearch.WordTrace tailWord_903684 prefixEnd_903684 412466001580220058572479 := by
  unfold tailWord_903684
  simp only [CollatzResearch.WordTrace]
  refine ⟨16480031629057339892459053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21973375505409786523278737 16480031629057339892459053)
  ·
    refine ⟨6180011860896502459672145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16480031629057339892459053 6180011860896502459672145)
    ·
      refine ⟨4635008895672376844754109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6180011860896502459672145 4635008895672376844754109)
      ·
        refine ⟨1738128335877141316782791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4635008895672376844754109 1738128335877141316782791)
        ·
          refine ⟨2607192503815711975174187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738128335877141316782791 2607192503815711975174187)
          ·
            refine ⟨3910788755723567962761281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607192503815711975174187 3910788755723567962761281)
            ·
              refine ⟨2933091566792675972070961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3910788755723567962761281 2933091566792675972070961)
              ·
                refine ⟨2199818675094506979053221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933091566792675972070961 2199818675094506979053221)
                ·
                  refine ⟨412466001580220058572479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199818675094506979053221 412466001580220058572479)
                  ·
                    rfl

theorem cell20_903684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_903684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903684 prefixEnd_903684 := by exact prefixLift 903684
  have htrace : WordTrace (prefixWord ++ tailWord_903684) baseStart_903684 baseEnd_903684 := by
    simpa [prefixWord, tailWord_903684, baseEnd_903684] using wordTrace_append hprefix tailTrace_903684
  have hstable : (prefixWord ++ tailWord_903684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903684).length < 2 ^ (prefixWord ++ tailWord_903684).sum := by decide
  have hdescent : baseEnd_903684 < baseStart_903684 := by decide
  rcases family_descends (prefixWord ++ tailWord_903684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903687 : List Nat := [1, 1, 4, 3, 4, 1, 2, 4]
def baseStart_903687 : Nat := 118140960795 + 903687 * 2 ^ 59
def prefixEnd_903687 : Nat := 4983230072969 + 3 ^ 40 * 903687 * 2
def baseEnd_903687 : Nat := 137489123620655127157489

theorem tailTrace_903687 : CollatzResearch.WordTrace tailWord_903687 prefixEnd_903687 137489123620655127157489 := by
  unfold tailWord_903687
  simp only [CollatzResearch.WordTrace]
  refine ⟨32960172677103811297277315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21973448451402540864851543 32960172677103811297277315)
  ·
    refine ⟨49440259015655716945915973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32960172677103811297277315 49440259015655716945915973)
    ·
      refine ⟨9270048565435446927359245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49440259015655716945915973 9270048565435446927359245)
      ·
        refine ⟨3476268212038292597759717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9270048565435446927359245 3476268212038292597759717)
        ·
          refine ⟨651800289757179862079947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3476268212038292597759717 651800289757179862079947)
          ·
            refine ⟨977700434635769793119921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651800289757179862079947 977700434635769793119921)
            ·
              refine ⟨733275325976827344839941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977700434635769793119921 733275325976827344839941)
              ·
                refine ⟨137489123620655127157489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 733275325976827344839941 137489123620655127157489)
                ·
                  rfl

theorem cell20_903687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 4].length) (baseStart_903687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903687 prefixEnd_903687 := by exact prefixLift 903687
  have htrace : WordTrace (prefixWord ++ tailWord_903687) baseStart_903687 baseEnd_903687 := by
    simpa [prefixWord, tailWord_903687, baseEnd_903687] using wordTrace_append hprefix tailTrace_903687
  have hstable : (prefixWord ++ tailWord_903687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903687).length < 2 ^ (prefixWord ++ tailWord_903687).sum := by decide
  have hdescent : baseEnd_903687 < baseStart_903687 := by decide
  rcases family_descends (prefixWord ++ tailWord_903687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903691 : List Nat := [1, 1, 1, 1, 7, 1, 4, 4]
def baseStart_903691 : Nat := 118140960795 + 903691 * 2 ^ 59
def prefixEnd_903691 : Nat := 4983230072969 + 3 ^ 40 * 903691 * 2
def baseEnd_903691 : Nat := 137489732190319715113039

theorem tailTrace_903691 : CollatzResearch.WordTrace tailWord_903691 prefixEnd_903691 137489732190319715113039 := by
  unfold tailWord_903691
  simp only [CollatzResearch.WordTrace]
  refine ⟨32960318569089319980422927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21973545712726213320281951 32960318569089319980422927)
  ·
    refine ⟨49440477853633979970634391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32960318569089319980422927 49440477853633979970634391)
    ·
      refine ⟨74160716780450969955951587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49440477853633979970634391 74160716780450969955951587)
      ·
        refine ⟨111241075170676454933927381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74160716780450969955951587 111241075170676454933927381)
        ·
          refine ⟨2607212699312729412513923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 111241075170676454933927381 2607212699312729412513923)
          ·
            refine ⟨3910819048969094118770885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607212699312729412513923 3910819048969094118770885)
            ·
              refine ⟨733278571681705147269541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3910819048969094118770885 733278571681705147269541)
              ·
                refine ⟨137489732190319715113039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 733278571681705147269541 137489732190319715113039)
                ·
                  rfl

theorem cell20_903691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 4].length) (baseStart_903691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903691 prefixEnd_903691 := by exact prefixLift 903691
  have htrace : WordTrace (prefixWord ++ tailWord_903691) baseStart_903691 baseEnd_903691 := by
    simpa [prefixWord, tailWord_903691, baseEnd_903691] using wordTrace_append hprefix tailTrace_903691
  have hstable : (prefixWord ++ tailWord_903691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903691).length < 2 ^ (prefixWord ++ tailWord_903691).sum := by decide
  have hdescent : baseEnd_903691 < baseStart_903691 := by decide
  rcases family_descends (prefixWord ++ tailWord_903691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903722 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_903722 : Nat := 118140960795 + 903722 * 2 ^ 59
def prefixEnd_903722 : Nat := 4983230072969 + 3 ^ 40 * 903722 * 2
def baseEnd_903722 : Nat := 412483345815660815305657

theorem tailTrace_903722 : CollatzResearch.WordTrace tailWord_903722 prefixEnd_903722 412483345815660815305657 := by
  unfold tailWord_903722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8240362307994253068700355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21974299487984674849867613 8240362307994253068700355)
  ·
    refine ⟨12360543461991379603050533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8240362307994253068700355 12360543461991379603050533)
    ·
      refine ⟨2317601899123383675571975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12360543461991379603050533 2317601899123383675571975)
      ·
        refine ⟨3476402848685075513357963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2317601899123383675571975 3476402848685075513357963)
        ·
          refine ⟨5214604273027613270036945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476402848685075513357963 5214604273027613270036945)
          ·
            refine ⟨3910953204770709952527709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5214604273027613270036945 3910953204770709952527709)
            ·
              refine ⟨1466607451789016232197891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3910953204770709952527709 1466607451789016232197891)
              ·
                refine ⟨2199911177683524348296837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466607451789016232197891 2199911177683524348296837)
                ·
                  refine ⟨412483345815660815305657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199911177683524348296837 412483345815660815305657)
                  ·
                    rfl

theorem cell20_903722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_903722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903722 prefixEnd_903722 := by exact prefixLift 903722
  have htrace : WordTrace (prefixWord ++ tailWord_903722) baseStart_903722 baseEnd_903722 := by
    simpa [prefixWord, tailWord_903722, baseEnd_903722] using wordTrace_append hprefix tailTrace_903722
  have hstable : (prefixWord ++ tailWord_903722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903722).length < 2 ^ (prefixWord ++ tailWord_903722).sum := by decide
  have hdescent : baseEnd_903722 < baseStart_903722 := by decide
  rcases family_descends (prefixWord ++ tailWord_903722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903736 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 3]
def baseStart_903736 : Nat := 118140960795 + 903736 * 2 ^ 59
def prefixEnd_903736 : Nat := 4983230072969 + 3 ^ 40 * 903736 * 2
def baseEnd_903736 : Nat := 412489735797138988838933

theorem tailTrace_903736 : CollatzResearch.WordTrace tailWord_903736 prefixEnd_903736 412489735797138988838933 := by
  unfold tailWord_903736
  simp only [CollatzResearch.WordTrace]
  refine ⟨16480979926963146332905531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21974639902617528443874041 16480979926963146332905531)
  ·
    refine ⟨24721469890444719499358297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16480979926963146332905531 24721469890444719499358297)
    ·
      refine ⟨18541102417833539624518723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24721469890444719499358297 18541102417833539624518723)
      ·
        refine ⟨27811653626750309436778085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18541102417833539624518723 27811653626750309436778085)
        ·
          refine ⟨5214685055015683019395891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27811653626750309436778085 5214685055015683019395891)
          ·
            refine ⟨7822027582523524529093837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214685055015683019395891 7822027582523524529093837)
            ·
              refine ⟨2933260343446321698410189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7822027582523524529093837 2933260343446321698410189)
              ·
                refine ⟨1099972628792370636903821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2933260343446321698410189 1099972628792370636903821)
                ·
                  refine ⟨412489735797138988838933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099972628792370636903821 412489735797138988838933)
                  ·
                    rfl

theorem cell20_903736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_903736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903736 prefixEnd_903736 := by exact prefixLift 903736
  have htrace : WordTrace (prefixWord ++ tailWord_903736) baseStart_903736 baseEnd_903736 := by
    simpa [prefixWord, tailWord_903736, baseEnd_903736] using wordTrace_append hprefix tailTrace_903736
  have hstable : (prefixWord ++ tailWord_903736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903736).length < 2 ^ (prefixWord ++ tailWord_903736).sum := by decide
  have hdescent : baseEnd_903736 < baseStart_903736 := by decide
  rcases family_descends (prefixWord ++ tailWord_903736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903777 : List Nat := [1, 2, 3, 1, 1, 4, 4, 2, 2]
def baseStart_903777 : Nat := 118140960795 + 903777 * 2 ^ 59
def prefixEnd_903777 : Nat := 4983230072969 + 3 ^ 40 * 903777 * 2
def baseEnd_903777 : Nat := 412508449314325068472099

theorem tailTrace_903777 : CollatzResearch.WordTrace tailWord_903777 prefixEnd_903777 412508449314325068472099 := by
  unfold tailWord_903777
  simp only [CollatzResearch.WordTrace]
  refine ⟨32963455246777756668053585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21975636831185171112035723 32963455246777756668053585)
  ·
    refine ⟨24722591435083317501040189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32963455246777756668053585 24722591435083317501040189)
    ·
      refine ⟨9270971788156244062890071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24722591435083317501040189 9270971788156244062890071)
      ·
        refine ⟨13906457682234366094335107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270971788156244062890071 13906457682234366094335107)
        ·
          refine ⟨20859686523351549141502661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13906457682234366094335107 20859686523351549141502661)
          ·
            refine ⟨3911191223128415464031749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20859686523351549141502661 3911191223128415464031749)
            ·
              refine ⟨733348354336577899505953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3911191223128415464031749 733348354336577899505953)
              ·
                refine ⟨550011265752433424629465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733348354336577899505953 550011265752433424629465)
                ·
                  refine ⟨412508449314325068472099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550011265752433424629465 412508449314325068472099)
                  ·
                    rfl

theorem cell20_903777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_903777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903777 prefixEnd_903777 := by exact prefixLift 903777
  have htrace : WordTrace (prefixWord ++ tailWord_903777) baseStart_903777 baseEnd_903777 := by
    simpa [prefixWord, tailWord_903777, baseEnd_903777] using wordTrace_append hprefix tailTrace_903777
  have hstable : (prefixWord ++ tailWord_903777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903777).length < 2 ^ (prefixWord ++ tailWord_903777).sum := by decide
  have hdescent : baseEnd_903777 < baseStart_903777 := by decide
  rcases family_descends (prefixWord ++ tailWord_903777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903784 : List Nat := [2, 1, 4, 3, 2, 2, 1, 5]
def baseStart_903784 : Nat := 118140960795 + 903784 * 2 ^ 59
def prefixEnd_903784 : Nat := 4983230072969 + 3 ^ 40 * 903784 * 2
def baseEnd_903784 : Nat := 137503881435021385079579

theorem tailTrace_903784 : CollatzResearch.WordTrace tailWord_903784 prefixEnd_903784 137503881435021385079579 := by
  unfold tailWord_903784
  simp only [CollatzResearch.WordTrace]
  refine ⟨16481855278876198431779203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21975807038501597909038937 16481855278876198431779203)
  ·
    refine ⟨24722782918314297647668805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16481855278876198431779203 24722782918314297647668805)
    ·
      refine ⟨4635521797183930808937901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24722782918314297647668805 4635521797183930808937901)
      ·
        refine ⟨1738320673943974053351713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4635521797183930808937901 1738320673943974053351713)
        ·
          refine ⟨1303740505457980540013785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1738320673943974053351713 1303740505457980540013785)
          ·
            refine ⟨977805379093485405010339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1303740505457980540013785 977805379093485405010339)
            ·
              refine ⟨1466708068640228107515509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977805379093485405010339 1466708068640228107515509)
              ·
                refine ⟨137503881435021385079579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1466708068640228107515509 137503881435021385079579)
                ·
                  rfl

theorem cell20_903784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_903784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903784 prefixEnd_903784 := by exact prefixLift 903784
  have htrace : WordTrace (prefixWord ++ tailWord_903784) baseStart_903784 baseEnd_903784 := by
    simpa [prefixWord, tailWord_903784, baseEnd_903784] using wordTrace_append hprefix tailTrace_903784
  have hstable : (prefixWord ++ tailWord_903784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903784).length < 2 ^ (prefixWord ++ tailWord_903784).sum := by decide
  have hdescent : baseEnd_903784 < baseStart_903784 := by decide
  rcases family_descends (prefixWord ++ tailWord_903784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903788 : List Nat := [2, 2, 1, 1, 3, 1, 5, 5]
def baseStart_903788 : Nat := 118140960795 + 903788 * 2 ^ 59
def prefixEnd_903788 : Nat := 4983230072969 + 3 ^ 40 * 903788 * 2
def baseEnd_903788 : Nat := 137504490004685973035129

theorem tailTrace_903788 : CollatzResearch.WordTrace tailWord_903788 prefixEnd_903788 137504490004685973035129 := by
  unfold tailWord_903788
  simp only [CollatzResearch.WordTrace]
  refine ⟨16481928224868952773352009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21975904299825270364469345 16481928224868952773352009)
  ·
    refine ⟨12361446168651714580014007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16481928224868952773352009 12361446168651714580014007)
    ·
      refine ⟨18542169252977571870021011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12361446168651714580014007 18542169252977571870021011)
      ·
        refine ⟨27813253879466357805031517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18542169252977571870021011 27813253879466357805031517)
        ·
          refine ⟨10429970204799884176886819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27813253879466357805031517 10429970204799884176886819)
          ·
            refine ⟨15644955307199826265330229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10429970204799884176886819 15644955307199826265330229)
            ·
              refine ⟨1466714560049983712374709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15644955307199826265330229 1466714560049983712374709)
              ·
                refine ⟨137504490004685973035129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1466714560049983712374709 137504490004685973035129)
                ·
                  rfl

theorem cell20_903788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_903788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903788 prefixEnd_903788 := by exact prefixLift 903788
  have htrace : WordTrace (prefixWord ++ tailWord_903788) baseStart_903788 baseEnd_903788 := by
    simpa [prefixWord, tailWord_903788, baseEnd_903788] using wordTrace_append hprefix tailTrace_903788
  have hstable : (prefixWord ++ tailWord_903788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903788).length < 2 ^ (prefixWord ++ tailWord_903788).sum := by decide
  have hdescent : baseEnd_903788 < baseStart_903788 := by decide
  rcases family_descends (prefixWord ++ tailWord_903788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903833 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_903833 : Nat := 118140960795 + 903833 * 2 ^ 59
def prefixEnd_903833 : Nat := 4983230072969 + 3 ^ 40 * 903833 * 2
def baseEnd_903833 : Nat := 412534009240237762605203

theorem tailTrace_903833 : CollatzResearch.WordTrace tailWord_903833 prefixEnd_903833 412534009240237762605203 := by
  unfold tailWord_903833
  simp only [CollatzResearch.WordTrace]
  refine ⟨32965497734574878232092153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21976998489716585488061435 32965497734574878232092153)
  ·
    refine ⟨24724123300931158674069115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32965497734574878232092153 24724123300931158674069115)
    ·
      refine ⟨37086184951396738011103673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24724123300931158674069115 37086184951396738011103673)
      ·
        refine ⟨27814638713547553508327755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37086184951396738011103673 27814638713547553508327755)
        ·
          refine ⟨41721958070321330262491633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27814638713547553508327755 41721958070321330262491633)
          ·
            refine ⟨31291468552740997696868725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41721958070321330262491633 31291468552740997696868725)
            ·
              refine ⟨2933575176819468534081443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31291468552740997696868725 2933575176819468534081443)
              ·
                refine ⟨4400362765229202801122165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933575176819468534081443 4400362765229202801122165)
                ·
                  refine ⟨412534009240237762605203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4400362765229202801122165 412534009240237762605203)
                  ·
                    rfl

theorem cell20_903833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_903833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903833 prefixEnd_903833 := by exact prefixLift 903833
  have htrace : WordTrace (prefixWord ++ tailWord_903833) baseStart_903833 baseEnd_903833 := by
    simpa [prefixWord, tailWord_903833, baseEnd_903833] using wordTrace_append hprefix tailTrace_903833
  have hstable : (prefixWord ++ tailWord_903833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903833).length < 2 ^ (prefixWord ++ tailWord_903833).sum := by decide
  have hdescent : baseEnd_903833 < baseStart_903833 := by decide
  rcases family_descends (prefixWord ++ tailWord_903833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903836 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_903836 : Nat := 118140960795 + 903836 * 2 ^ 59
def prefixEnd_903836 : Nat := 4983230072969 + 3 ^ 40 * 903836 * 2
def baseEnd_903836 : Nat := 412535378521983085505191

theorem tailTrace_903836 : CollatzResearch.WordTrace tailWord_903836 prefixEnd_903836 412535378521983085505191 := by
  unfold tailWord_903836
  simp only [CollatzResearch.WordTrace]
  refine ⟨16482803576782004872225681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21977071435709339829634241 16482803576782004872225681)
  ·
    refine ⟨12362102682586503654169261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16482803576782004872225681 12362102682586503654169261)
    ·
      refine ⟨4635788505969938870313473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12362102682586503654169261 4635788505969938870313473)
      ·
        refine ⟨3476841379477454152735105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4635788505969938870313473 3476841379477454152735105)
        ·
          refine ⟨2607631034608090614551329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3476841379477454152735105 2607631034608090614551329)
          ·
            refine ⟨1955723275956067960913497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2607631034608090614551329 1955723275956067960913497)
            ·
              refine ⟨1466792456967050970685123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955723275956067960913497 1466792456967050970685123)
              ·
                refine ⟨2200188685450576456027685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466792456967050970685123 2200188685450576456027685)
                ·
                  refine ⟨412535378521983085505191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2200188685450576456027685 412535378521983085505191)
                  ·
                    rfl

theorem cell20_903836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_903836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903836 prefixEnd_903836 := by exact prefixLift 903836
  have htrace : WordTrace (prefixWord ++ tailWord_903836) baseStart_903836 baseEnd_903836 := by
    simpa [prefixWord, tailWord_903836, baseEnd_903836] using wordTrace_append hprefix tailTrace_903836
  have hstable : (prefixWord ++ tailWord_903836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903836).length < 2 ^ (prefixWord ++ tailWord_903836).sum := by decide
  have hdescent : baseEnd_903836 < baseStart_903836 := by decide
  rcases family_descends (prefixWord ++ tailWord_903836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903871 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_903871 : Nat := 118140960795 + 903871 * 2 ^ 59
def prefixEnd_903871 : Nat := 4983230072969 + 3 ^ 40 * 903871 * 2
def baseEnd_903871 : Nat := 412551353475678519338381

theorem tailTrace_903871 : CollatzResearch.WordTrace tailWord_903871 prefixEnd_903871 412551353475678519338381 := by
  unfold tailWord_903871
  simp only [CollatzResearch.WordTrace]
  refine ⟨32966883708437210721975467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21977922472291473814650311 32966883708437210721975467)
  ·
    refine ⟨49450325562655816082963201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32966883708437210721975467 49450325562655816082963201)
    ·
      refine ⟨37087744171991862062222401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49450325562655816082963201 37087744171991862062222401)
      ·
        refine ⟨27815808128993896546666801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37087744171991862062222401 27815808128993896546666801)
        ·
          refine ⟨20861856096745422410000101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27815808128993896546666801 20861856096745422410000101)
          ·
            refine ⟨3911598018139766701875019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20861856096745422410000101 3911598018139766701875019)
            ·
              refine ⟨5867397027209650052812529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3911598018139766701875019 5867397027209650052812529)
              ·
                refine ⟨4400547770407237539609397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5867397027209650052812529 4400547770407237539609397)
                ·
                  refine ⟨412551353475678519338381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4400547770407237539609397 412551353475678519338381)
                  ·
                    rfl

theorem cell20_903871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_903871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903871 prefixEnd_903871 := by exact prefixLift 903871
  have htrace : WordTrace (prefixWord ++ tailWord_903871) baseStart_903871 baseEnd_903871 := by
    simpa [prefixWord, tailWord_903871, baseEnd_903871] using wordTrace_append hprefix tailTrace_903871
  have hstable : (prefixWord ++ tailWord_903871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903871).length < 2 ^ (prefixWord ++ tailWord_903871).sum := by decide
  have hdescent : baseEnd_903871 < baseStart_903871 := by decide
  rcases family_descends (prefixWord ++ tailWord_903871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903895 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 4]
def baseStart_903895 : Nat := 118140960795 + 903895 * 2 ^ 59
def prefixEnd_903895 : Nat := 4983230072969 + 3 ^ 40 * 903895 * 2
def baseEnd_903895 : Nat := 412562307729641102538283

theorem tailTrace_903895 : CollatzResearch.WordTrace tailWord_903895 prefixEnd_903895 412562307729641102538283 := by
  unfold tailWord_903895
  simp only [CollatzResearch.WordTrace]
  refine ⟨32967759060350262820849139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21978506040233508547232759 32967759060350262820849139)
  ·
    refine ⟨49451638590525394231273709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32967759060350262820849139 49451638590525394231273709)
    ·
      refine ⟨18544364471447022836727641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49451638590525394231273709 18544364471447022836727641)
      ·
        refine ⟨13908273353585267127545731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18544364471447022836727641 13908273353585267127545731)
        ·
          refine ⟨20862410030377900691318597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13908273353585267127545731 20862410030377900691318597)
          ·
            refine ⟨3911701880695856379622237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20862410030377900691318597 3911701880695856379622237)
            ·
              refine ⟨1466888205260946142358339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3911701880695856379622237 1466888205260946142358339)
              ·
                refine ⟨2200332307891419213537509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466888205260946142358339 2200332307891419213537509)
                ·
                  refine ⟨412562307729641102538283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2200332307891419213537509 412562307729641102538283)
                  ·
                    rfl

theorem cell20_903895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_903895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903895 prefixEnd_903895 := by exact prefixLift 903895
  have htrace : WordTrace (prefixWord ++ tailWord_903895) baseStart_903895 baseEnd_903895 := by
    simpa [prefixWord, tailWord_903895, baseEnd_903895] using wordTrace_append hprefix tailTrace_903895
  have hstable : (prefixWord ++ tailWord_903895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903895).length < 2 ^ (prefixWord ++ tailWord_903895).sum := by decide
  have hdescent : baseEnd_903895 < baseStart_903895 := by decide
  rcases family_descends (prefixWord ++ tailWord_903895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903905 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 3]
def baseStart_903905 : Nat := 118140960795 + 903905 * 2 ^ 59
def prefixEnd_903905 : Nat := 4983230072969 + 3 ^ 40 * 903905 * 2
def baseEnd_903905 : Nat := 412566872002125512204909

theorem tailTrace_903905 : CollatzResearch.WordTrace tailWord_903905 prefixEnd_903905 412566872002125512204909 := by
  unfold tailWord_903905
  simp only [CollatzResearch.WordTrace]
  refine ⟨32968123790314034528713169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21978749193542689685808779 32968123790314034528713169)
  ·
    refine ⟨24726092842735525896534877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32968123790314034528713169 24726092842735525896534877)
    ·
      refine ⟨9272284816025822211200579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24726092842735525896534877 9272284816025822211200579)
      ·
        refine ⟨13908427224038733316800869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9272284816025822211200579 13908427224038733316800869)
        ·
          refine ⟨2607830104507262496900163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13908427224038733316800869 2607830104507262496900163)
          ·
            refine ⟨3911745156760893745350245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607830104507262496900163 3911745156760893745350245)
            ·
              refine ⟨733452216892667577253171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3911745156760893745350245 733452216892667577253171)
              ·
                refine ⟨1100178325339001365879757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733452216892667577253171 1100178325339001365879757)
                ·
                  refine ⟨412566872002125512204909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100178325339001365879757 412566872002125512204909)
                  ·
                    rfl

theorem cell20_903905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_903905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903905 prefixEnd_903905 := by exact prefixLift 903905
  have htrace : WordTrace (prefixWord ++ tailWord_903905) baseStart_903905 baseEnd_903905 := by
    simpa [prefixWord, tailWord_903905, baseEnd_903905] using wordTrace_append hprefix tailTrace_903905
  have hstable : (prefixWord ++ tailWord_903905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903905).length < 2 ^ (prefixWord ++ tailWord_903905).sum := by decide
  have hdescent : baseEnd_903905 < baseStart_903905 := by decide
  rcases family_descends (prefixWord ++ tailWord_903905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903916 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_903916 : Nat := 118140960795 + 903916 * 2 ^ 59
def prefixEnd_903916 : Nat := 4983230072969 + 3 ^ 40 * 903916 * 2
def baseEnd_903916 : Nat := 412571892701858362838197

theorem tailTrace_903916 : CollatzResearch.WordTrace tailWord_903916 prefixEnd_903916 412571892701858362838197 := by
  unfold tailWord_903916
  simp only [CollatzResearch.WordTrace]
  refine ⟨16484262496637091703681801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21979016662182788938242401 16484262496637091703681801)
  ·
    refine ⟨12363196872477818777761351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16484262496637091703681801 12363196872477818777761351)
    ·
      refine ⟨18544795308716728166642027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12363196872477818777761351 18544795308716728166642027)
      ·
        refine ⟨27817192963075092249963041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18544795308716728166642027 27817192963075092249963041)
        ·
          refine ⟨20862894722306319187472281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27817192963075092249963041 20862894722306319187472281)
          ·
            refine ⟨15647171041729739390604211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20862894722306319187472281 15647171041729739390604211)
            ·
              refine ⟨23470756562594609085906317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15647171041729739390604211 23470756562594609085906317)
              ·
                refine ⟨8801533710972978407214869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23470756562594609085906317 8801533710972978407214869)
                ·
                  refine ⟨412571892701858362838197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8801533710972978407214869 412571892701858362838197)
                  ·
                    rfl

theorem cell20_903916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_903916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903916 prefixEnd_903916 := by exact prefixLift 903916
  have htrace : WordTrace (prefixWord ++ tailWord_903916) baseStart_903916 baseEnd_903916 := by
    simpa [prefixWord, tailWord_903916, baseEnd_903916] using wordTrace_append hprefix tailTrace_903916
  have hstable : (prefixWord ++ tailWord_903916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903916).length < 2 ^ (prefixWord ++ tailWord_903916).sum := by decide
  have hdescent : baseEnd_903916 < baseStart_903916 := by decide
  rcases family_descends (prefixWord ++ tailWord_903916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903943 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 3]
def baseStart_903943 : Nat := 118140960795 + 903943 * 2 ^ 59
def prefixEnd_903943 : Nat := 4983230072969 + 3 ^ 40 * 903943 * 2
def baseEnd_903943 : Nat := 412584216237566268938087

theorem tailTrace_903943 : CollatzResearch.WordTrace tailWord_903943 prefixEnd_903943 412584216237566268938087 := by
  unfold tailWord_903943
  simp only [CollatzResearch.WordTrace]
  refine ⟨32969509764176367018596483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21979673176117578012397655 32969509764176367018596483)
  ·
    refine ⟨49454264646264550527894725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32969509764176367018596483 49454264646264550527894725)
    ·
      refine ⟨9272674621174603223980261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49454264646264550527894725 9272674621174603223980261)
      ·
        refine ⟨1738626491470238104496299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9272674621174603223980261 1738626491470238104496299)
        ·
          refine ⟨2607939737205357156744449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738626491470238104496299 2607939737205357156744449)
          ·
            refine ⟨1955954802904017867558337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2607939737205357156744449 1955954802904017867558337)
            ·
              refine ⟨1466966102178013400668753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955954802904017867558337 1466966102178013400668753)
              ·
                refine ⟨1100224576633510050501565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466966102178013400668753 1100224576633510050501565)
                ·
                  refine ⟨412584216237566268938087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100224576633510050501565 412584216237566268938087)
                  ·
                    rfl

theorem cell20_903943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 3].length) (baseStart_903943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903943 prefixEnd_903943 := by exact prefixLift 903943
  have htrace : WordTrace (prefixWord ++ tailWord_903943) baseStart_903943 baseEnd_903943 := by
    simpa [prefixWord, tailWord_903943, baseEnd_903943] using wordTrace_append hprefix tailTrace_903943
  have hstable : (prefixWord ++ tailWord_903943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903943).length < 2 ^ (prefixWord ++ tailWord_903943).sum := by decide
  have hdescent : baseEnd_903943 < baseStart_903943 := by decide
  rcases family_descends (prefixWord ++ tailWord_903943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903961 : List Nat := [1, 2, 1, 2, 1, 1, 1, 11]
def baseStart_903961 : Nat := 118140960795 + 903961 * 2 ^ 59
def prefixEnd_903961 : Nat := 4983230072969 + 3 ^ 40 * 903961 * 2
def baseEnd_903961 : Nat := 137530810642679402112671

theorem tailTrace_903961 : CollatzResearch.WordTrace tailWord_903961 prefixEnd_903961 137530810642679402112671 := by
  unfold tailWord_903961
  simp only [CollatzResearch.WordTrace]
  refine ⟨32970166278111156092751737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21980110852074104061834491 32970166278111156092751737)
  ·
    refine ⟨24727624708583367069563803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32970166278111156092751737 24727624708583367069563803)
    ·
      refine ⟨37091437062875050604345705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24727624708583367069563803 37091437062875050604345705)
      ·
        refine ⟨27818577797156287953259279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37091437062875050604345705 27818577797156287953259279)
        ·
          refine ⟨41727866695734431929888919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27818577797156287953259279 41727866695734431929888919)
          ·
            refine ⟨62591800043601647894833379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41727866695734431929888919 62591800043601647894833379)
            ·
              refine ⟨93887700065402471842250069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62591800043601647894833379 93887700065402471842250069)
              ·
                refine ⟨137530810642679402112671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 93887700065402471842250069 137530810642679402112671)
                ·
                  rfl

theorem cell20_903961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_903961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903961 prefixEnd_903961 := by exact prefixLift 903961
  have htrace : WordTrace (prefixWord ++ tailWord_903961) baseStart_903961 baseEnd_903961 := by
    simpa [prefixWord, tailWord_903961, baseEnd_903961] using wordTrace_append hprefix tailTrace_903961
  have hstable : (prefixWord ++ tailWord_903961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903961).length < 2 ^ (prefixWord ++ tailWord_903961).sum := by decide
  have hdescent : baseEnd_903961 < baseStart_903961 := by decide
  rcases family_descends (prefixWord ++ tailWord_903961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903964 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 3]
def baseStart_903964 : Nat := 118140960795 + 903964 * 2 ^ 59
def prefixEnd_903964 : Nat := 4983230072969 + 3 ^ 40 * 903964 * 2
def baseEnd_903964 : Nat := 412593801209783529238001

theorem tailTrace_903964 : CollatzResearch.WordTrace tailWord_903964 prefixEnd_903964 412593801209783529238001 := by
  unfold tailWord_903964
  simp only [CollatzResearch.WordTrace]
  refine ⟨16485137848550143802555473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21980183798066858403407297 16485137848550143802555473)
  ·
    refine ⟨12363853386412607851916605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16485137848550143802555473 12363853386412607851916605)
    ·
      refine ⟨4636445019904727944468727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12363853386412607851916605 4636445019904727944468727)
      ·
        refine ⟨6954667529857091916703091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4636445019904727944468727 6954667529857091916703091)
        ·
          refine ⟨10432001294785637875054637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6954667529857091916703091 10432001294785637875054637)
          ·
            refine ⟨3912000485544614203145489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10432001294785637875054637 3912000485544614203145489)
            ·
              refine ⟨2934000364158460652359117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3912000485544614203145489 2934000364158460652359117)
              ·
                refine ⟨1100250136559422744634669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2934000364158460652359117 1100250136559422744634669)
                ·
                  refine ⟨412593801209783529238001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100250136559422744634669 412593801209783529238001)
                  ·
                    rfl

theorem cell20_903964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_903964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903964 prefixEnd_903964 := by exact prefixLift 903964
  have htrace : WordTrace (prefixWord ++ tailWord_903964) baseStart_903964 baseEnd_903964 := by
    simpa [prefixWord, tailWord_903964, baseEnd_903964] using wordTrace_append hprefix tailTrace_903964
  have hstable : (prefixWord ++ tailWord_903964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903964).length < 2 ^ (prefixWord ++ tailWord_903964).sum := by decide
  have hdescent : baseEnd_903964 < baseStart_903964 := by decide
  rcases family_descends (prefixWord ++ tailWord_903964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903985 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_903985 : Nat := 118140960795 + 903985 * 2 ^ 59
def prefixEnd_903985 : Nat := 4983230072969 + 3 ^ 40 * 903985 * 2
def baseEnd_903985 : Nat := 412603386182000789537915

theorem tailTrace_903985 : CollatzResearch.WordTrace tailWord_903985 prefixEnd_903985 412603386182000789537915 := by
  unfold tailWord_903985
  simp only [CollatzResearch.WordTrace]
  refine ⟨32971041630024208191625409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21980694420016138794416939 32971041630024208191625409)
  ·
    refine ⟨24728281222518156143719057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32971041630024208191625409 24728281222518156143719057)
    ·
      refine ⟨18546210916888617107789293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24728281222518156143719057 18546210916888617107789293)
      ·
        refine ⟨6954829093833231415420985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18546210916888617107789293 6954829093833231415420985)
        ·
          refine ⟨5216121820374923561565739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6954829093833231415420985 5216121820374923561565739)
          ·
            refine ⟨7824182730562385342348609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216121820374923561565739 7824182730562385342348609)
            ·
              refine ⟨5868137047921789006761457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7824182730562385342348609 5868137047921789006761457)
              ·
                refine ⟨4401102785941341755071093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5868137047921789006761457 4401102785941341755071093)
                ·
                  refine ⟨412603386182000789537915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4401102785941341755071093 412603386182000789537915)
                  ·
                    rfl

theorem cell20_903985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_903985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903985 prefixEnd_903985 := by exact prefixLift 903985
  have htrace : WordTrace (prefixWord ++ tailWord_903985) baseStart_903985 baseEnd_903985 := by
    simpa [prefixWord, tailWord_903985, baseEnd_903985] using wordTrace_append hprefix tailTrace_903985
  have hstable : (prefixWord ++ tailWord_903985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903985).length < 2 ^ (prefixWord ++ tailWord_903985).sum := by decide
  have hdescent : baseEnd_903985 < baseStart_903985 := by decide
  rcases family_descends (prefixWord ++ tailWord_903985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903992 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_903992 : Nat := 118140960795 + 903992 * 2 ^ 59
def prefixEnd_903992 : Nat := 4983230072969 + 3 ^ 40 * 903992 * 2
def baseEnd_903992 : Nat := 412606581172739876304553

theorem tailTrace_903992 : CollatzResearch.WordTrace tailWord_903992 prefixEnd_903992 412606581172739876304553 := by
  unfold tailWord_903992
  simp only [CollatzResearch.WordTrace]
  refine ⟨16485648470499424193565115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21980864627332565591420153 16485648470499424193565115)
  ·
    refine ⟨24728472705749136290347673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16485648470499424193565115 24728472705749136290347673)
    ·
      refine ⟨18546354529311852217760755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24728472705749136290347673 18546354529311852217760755)
      ·
        refine ⟨27819531793967778326641133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18546354529311852217760755 27819531793967778326641133)
        ·
          refine ⟨10432324422737916872490425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27819531793967778326641133 10432324422737916872490425)
          ·
            refine ⟨7824243317053437654367819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10432324422737916872490425 7824243317053437654367819)
            ·
              refine ⟨11736364975580156481551729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7824243317053437654367819 11736364975580156481551729)
              ·
                refine ⟨8802273731685117361163797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11736364975580156481551729 8802273731685117361163797)
                ·
                  refine ⟨412606581172739876304553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8802273731685117361163797 412606581172739876304553)
                  ·
                    rfl

theorem cell20_903992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_903992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903992 prefixEnd_903992 := by exact prefixLift 903992
  have htrace : WordTrace (prefixWord ++ tailWord_903992) baseStart_903992 baseEnd_903992 := by
    simpa [prefixWord, tailWord_903992, baseEnd_903992] using wordTrace_append hprefix tailTrace_903992
  have hstable : (prefixWord ++ tailWord_903992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903992).length < 2 ^ (prefixWord ++ tailWord_903992).sum := by decide
  have hdescent : baseEnd_903992 < baseStart_903992 := by decide
  rcases family_descends (prefixWord ++ tailWord_903992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903998 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_903998 : Nat := 118140960795 + 903998 * 2 ^ 59
def prefixEnd_903998 : Nat := 4983230072969 + 3 ^ 40 * 903998 * 2
def baseEnd_903998 : Nat := 412609319736230522104529

theorem tailTrace_903998 : CollatzResearch.WordTrace tailWord_903998 prefixEnd_903998 412609319736230522104529 := by
  unfold tailWord_903998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4121439472372138926481081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21981010519318074274565765 4121439472372138926481081)
  ·
    refine ⟨3091079604279104194860811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4121439472372138926481081 3091079604279104194860811)
    ·
      refine ⟨4636619406418656292291217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3091079604279104194860811 4636619406418656292291217)
      ·
        refine ⟨3477464554813992219218413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4636619406418656292291217 3477464554813992219218413)
        ·
          refine ⟨1304049208055247082206905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3477464554813992219218413 1304049208055247082206905)
          ·
            refine ⟨978036906041435311655179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1304049208055247082206905 978036906041435311655179)
            ·
              refine ⟨1467055359062152967482769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978036906041435311655179 1467055359062152967482769)
              ·
                refine ⟨1100291519296614725612077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467055359062152967482769 1100291519296614725612077)
                ·
                  refine ⟨412609319736230522104529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100291519296614725612077 412609319736230522104529)
                  ·
                    rfl

theorem cell20_903998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_903998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_903998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_903998 prefixEnd_903998 := by exact prefixLift 903998
  have htrace : WordTrace (prefixWord ++ tailWord_903998) baseStart_903998 baseEnd_903998 := by
    simpa [prefixWord, tailWord_903998, baseEnd_903998] using wordTrace_append hprefix tailTrace_903998
  have hstable : (prefixWord ++ tailWord_903998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903998).length < 2 ^ (prefixWord ++ tailWord_903998).sum := by decide
  have hdescent : baseEnd_903998 < baseStart_903998 := by decide
  rcases family_descends (prefixWord ++ tailWord_903998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904009 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 4]
def baseStart_904009 : Nat := 118140960795 + 904009 * 2 ^ 59
def prefixEnd_904009 : Nat := 4983230072969 + 3 ^ 40 * 904009 * 2
def baseEnd_904009 : Nat := 412614340435963372737817

theorem tailTrace_904009 : CollatzResearch.WordTrace tailWord_904009 prefixEnd_904009 412614340435963372737817 := by
  unfold tailWord_904009
  simp only [CollatzResearch.WordTrace]
  refine ⟨32971916981937260290499081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21981277987958173526999387 32971916981937260290499081)
  ·
    refine ⟨24728937736452945217874311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32971916981937260290499081 24728937736452945217874311)
    ·
      refine ⟨37093406604679417826811467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24728937736452945217874311 37093406604679417826811467)
      ·
        refine ⟨55640109907019126740217201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37093406604679417826811467 55640109907019126740217201)
        ·
          refine ⟨41730082430264345055162901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55640109907019126740217201 41730082430264345055162901)
          ·
            refine ⟨1956097613918641174460761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41730082430264345055162901 1956097613918641174460761)
            ·
              refine ⟨1467073210438980880845571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956097613918641174460761 1467073210438980880845571)
              ·
                refine ⟨2200609815658471321268357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467073210438980880845571 2200609815658471321268357)
                ·
                  refine ⟨412614340435963372737817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2200609815658471321268357 412614340435963372737817)
                  ·
                    rfl

theorem cell20_904009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_904009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904009 prefixEnd_904009 := by exact prefixLift 904009
  have htrace : WordTrace (prefixWord ++ tailWord_904009) baseStart_904009 baseEnd_904009 := by
    simpa [prefixWord, tailWord_904009, baseEnd_904009] using wordTrace_append hprefix tailTrace_904009
  have hstable : (prefixWord ++ tailWord_904009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904009).length < 2 ^ (prefixWord ++ tailWord_904009).sum := by decide
  have hdescent : baseEnd_904009 < baseStart_904009 := by decide
  rcases family_descends (prefixWord ++ tailWord_904009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904061 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_904061 : Nat := 118140960795 + 904061 * 2 ^ 59
def prefixEnd_904061 : Nat := 4983230072969 + 3 ^ 40 * 904061 * 2
def baseEnd_904061 : Nat := 412638074652882303004271

theorem tailTrace_904061 : CollatzResearch.WordTrace tailWord_904061 prefixEnd_904061 412638074652882303004271 := by
  unfold tailWord_904061
  simp only [CollatzResearch.WordTrace]
  refine ⟨32973813577748873171392037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21982542385165915447594691 32973813577748873171392037)
  ·
    refine ⟨6182590045827913719636007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32973813577748873171392037 6182590045827913719636007)
    ·
      refine ⟨9273885068741870579454011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6182590045827913719636007 9273885068741870579454011)
      ·
        refine ⟨13910827603112805869181017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9273885068741870579454011 13910827603112805869181017)
        ·
          refine ⟨10433120702334604401885763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13910827603112805869181017 10433120702334604401885763)
          ·
            refine ⟨15649681053501906602828645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10433120702334604401885763 15649681053501906602828645)
            ·
              refine ⟨2934315197531607488030371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15649681053501906602828645 2934315197531607488030371)
              ·
                refine ⟨4401472796297411232045557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934315197531607488030371 4401472796297411232045557)
                ·
                  refine ⟨412638074652882303004271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4401472796297411232045557 412638074652882303004271)
                  ·
                    rfl

theorem cell20_904061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_904061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904061 prefixEnd_904061 := by exact prefixLift 904061
  have htrace : WordTrace (prefixWord ++ tailWord_904061) baseStart_904061 baseEnd_904061 := by
    simpa [prefixWord, tailWord_904061, baseEnd_904061] using wordTrace_append hprefix tailTrace_904061
  have hstable : (prefixWord ++ tailWord_904061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904061).length < 2 ^ (prefixWord ++ tailWord_904061).sum := by decide
  have hdescent : baseEnd_904061 < baseStart_904061 := by decide
  rcases family_descends (prefixWord ++ tailWord_904061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904074 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_904074 : Nat := 118140960795 + 904074 * 2 ^ 59
def prefixEnd_904074 : Nat := 4983230072969 + 3 ^ 40 * 904074 * 2
def baseEnd_904074 : Nat := 412644008207112035570885

theorem tailTrace_904074 : CollatzResearch.WordTrace tailWord_904074 prefixEnd_904074 412644008207112035570885 := by
  unfold tailWord_904074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8243571931675444097903819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21982858484467850927743517 8243571931675444097903819)
  ·
    refine ⟨12365357897513166146855729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8243571931675444097903819 12365357897513166146855729)
    ·
      refine ⟨9274018423134874610141797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12365357897513166146855729 9274018423134874610141797)
      ·
        refine ⟨1738878454337788989401587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9274018423134874610141797 1738878454337788989401587)
        ·
          refine ⟨2608317681506683484102381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738878454337788989401587 2608317681506683484102381)
          ·
            refine ⟨978119130565006306538393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2608317681506683484102381 978119130565006306538393)
            ·
              refine ⟨733589347923754729903795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978119130565006306538393 733589347923754729903795)
              ·
                refine ⟨1100384021885632094855693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733589347923754729903795 1100384021885632094855693)
                ·
                  refine ⟨412644008207112035570885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100384021885632094855693 412644008207112035570885)
                  ·
                    rfl

theorem cell20_904074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_904074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904074 prefixEnd_904074 := by exact prefixLift 904074
  have htrace : WordTrace (prefixWord ++ tailWord_904074) baseStart_904074 baseEnd_904074 := by
    simpa [prefixWord, tailWord_904074, baseEnd_904074] using wordTrace_append hprefix tailTrace_904074
  have hstable : (prefixWord ++ tailWord_904074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904074).length < 2 ^ (prefixWord ++ tailWord_904074).sum := by decide
  have hdescent : baseEnd_904074 < baseStart_904074 := by decide
  rcases family_descends (prefixWord ++ tailWord_904074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904075 : List Nat := [1, 1, 1, 1, 4, 2, 3, 7]
def baseStart_904075 : Nat := 118140960795 + 904075 * 2 ^ 59
def prefixEnd_904075 : Nat := 4983230072969 + 3 ^ 40 * 904075 * 2
def baseEnd_904075 : Nat := 137548154878120158845849

theorem tailTrace_904075 : CollatzResearch.WordTrace tailWord_904075 prefixEnd_904075 137548154878120158845849 := by
  unfold tailWord_904075
  simp only [CollatzResearch.WordTrace]
  refine ⟨32974324199698153562401679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21982882799798769041601119 32974324199698153562401679)
  ·
    refine ⟨49461486299547230343602519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32974324199698153562401679 49461486299547230343602519)
    ·
      refine ⟨74192229449320845515403779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49461486299547230343602519 74192229449320845515403779)
      ·
        refine ⟨111288344173981268273105669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74192229449320845515403779 111288344173981268273105669)
        ·
          refine ⟨20866564532621487801207313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111288344173981268273105669 20866564532621487801207313)
          ·
            refine ⟨15649923399466115850905485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20866564532621487801207313 15649923399466115850905485)
            ·
              refine ⟨5868721274799793444089557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15649923399466115850905485 5868721274799793444089557)
              ·
                refine ⟨137548154878120158845849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5868721274799793444089557 137548154878120158845849)
                ·
                  rfl

theorem cell20_904075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_904075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904075 prefixEnd_904075 := by exact prefixLift 904075
  have htrace : WordTrace (prefixWord ++ tailWord_904075) baseStart_904075 baseEnd_904075 := by
    simpa [prefixWord, tailWord_904075, baseEnd_904075] using wordTrace_append hprefix tailTrace_904075
  have hstable : (prefixWord ++ tailWord_904075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904075).length < 2 ^ (prefixWord ++ tailWord_904075).sum := by decide
  have hdescent : baseEnd_904075 < baseStart_904075 := by decide
  rcases family_descends (prefixWord ++ tailWord_904075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904109 : List Nat := [1, 5, 2, 3, 1, 8]
def baseStart_904109 : Nat := 118140960795 + 904109 * 2 ^ 59
def prefixEnd_904109 : Nat := 4983230072969 + 3 ^ 40 * 904109 * 2
def baseEnd_904109 : Nat := 15283703080029906274225

theorem tailTrace_904109 : CollatzResearch.WordTrace tailWord_904109 prefixEnd_904109 15283703080029906274225 := by
  unfold tailWord_904109
  simp only [CollatzResearch.WordTrace]
  refine ⟨32975564281574977369139381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21983709521049984912759587 32975564281574977369139381)
  ·
    refine ⟨3091459151397654128356817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32975564281574977369139381 3091459151397654128356817)
    ·
      refine ⟨2318594363548240596267613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3091459151397654128356817 2318594363548240596267613)
      ·
        refine ⟨869472886330590223600355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2318594363548240596267613 869472886330590223600355)
        ·
          refine ⟨1304209329495885335400533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869472886330590223600355 1304209329495885335400533)
          ·
            refine ⟨15283703080029906274225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1304209329495885335400533 15283703080029906274225)
            ·
              rfl

theorem cell20_904109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 8].length) (baseStart_904109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904109 prefixEnd_904109 := by exact prefixLift 904109
  have htrace : WordTrace (prefixWord ++ tailWord_904109) baseStart_904109 baseEnd_904109 := by
    simpa [prefixWord, tailWord_904109, baseEnd_904109] using wordTrace_append hprefix tailTrace_904109
  have hstable : (prefixWord ++ tailWord_904109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904109).length < 2 ^ (prefixWord ++ tailWord_904109).sum := by decide
  have hdescent : baseEnd_904109 < baseStart_904109 := by decide
  rcases family_descends (prefixWord ++ tailWord_904109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904113 : List Nat := [1, 2, 2, 4, 11]
def baseStart_904113 : Nat := 118140960795 + 904113 * 2 ^ 59
def prefixEnd_904113 : Nat := 4983230072969 + 3 ^ 40 * 904113 * 2
def baseEnd_904113 : Nat := 5094590232960509052725

theorem tailTrace_904113 : CollatzResearch.WordTrace tailWord_904113 prefixEnd_904113 5094590232960509052725 := by
  unfold tailWord_904113
  simp only [CollatzResearch.WordTrace]
  refine ⟨32975710173560486052284993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21983806782373657368189995 32975710173560486052284993)
  ·
    refine ⟨24731782630170364539213745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32975710173560486052284993 24731782630170364539213745)
    ·
      refine ⟨18548836972627773404410309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24731782630170364539213745 18548836972627773404410309)
      ·
        refine ⟨3477906932367707513326933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18548836972627773404410309 3477906932367707513326933)
        ·
          refine ⟨5094590232960509052725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3477906932367707513326933 5094590232960509052725)
          ·
            rfl

theorem cell20_904113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 11].length) (baseStart_904113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904113 prefixEnd_904113 := by exact prefixLift 904113
  have htrace : WordTrace (prefixWord ++ tailWord_904113) baseStart_904113 baseEnd_904113 := by
    simpa [prefixWord, tailWord_904113, baseEnd_904113] using wordTrace_append hprefix tailTrace_904113
  have hstable : (prefixWord ++ tailWord_904113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904113).length < 2 ^ (prefixWord ++ tailWord_904113).sum := by decide
  have hdescent : baseEnd_904113 < baseStart_904113 := by decide
  rcases family_descends (prefixWord ++ tailWord_904113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904157 : List Nat := [1, 4, 3, 1, 2, 2, 2, 3, 2]
def baseStart_904157 : Nat := 118140960795 + 904157 * 2 ^ 59
def prefixEnd_904157 : Nat := 4983230072969 + 3 ^ 40 * 904157 * 2
def baseEnd_904157 : Nat := 412681891668732635803879

theorem tailTrace_904157 : CollatzResearch.WordTrace tailWord_904157 prefixEnd_904157 412681891668732635803879 := by
  unfold tailWord_904157
  simp only [CollatzResearch.WordTrace]
  refine ⟨32977314985401081566886725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21984876656934054377924483 32977314985401081566886725)
  ·
    refine ⟨6183246559762702793791261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32977314985401081566886725 6183246559762702793791261)
    ·
      refine ⟨2318717459911013547671723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6183246559762702793791261 2318717459911013547671723)
      ·
        refine ⟨3478076189866520321507585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2318717459911013547671723 3478076189866520321507585)
        ·
          refine ⟨2608557142399890241130689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478076189866520321507585 2608557142399890241130689)
          ·
            refine ⟨1956417856799917680848017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608557142399890241130689 1956417856799917680848017)
            ·
              refine ⟨1467313392599938260636013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956417856799917680848017 1467313392599938260636013)
              ·
                refine ⟨550242522224976847738505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1467313392599938260636013 550242522224976847738505)
                ·
                  refine ⟨412681891668732635803879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550242522224976847738505 412681891668732635803879)
                  ·
                    rfl

theorem cell20_904157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_904157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904157 prefixEnd_904157 := by exact prefixLift 904157
  have htrace : WordTrace (prefixWord ++ tailWord_904157) baseStart_904157 baseEnd_904157 := by
    simpa [prefixWord, tailWord_904157, baseEnd_904157] using wordTrace_append hprefix tailTrace_904157
  have hstable : (prefixWord ++ tailWord_904157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904157).length < 2 ^ (prefixWord ++ tailWord_904157).sum := by decide
  have hdescent : baseEnd_904157 < baseStart_904157 := by decide
  rcases family_descends (prefixWord ++ tailWord_904157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904175 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 5]
def baseStart_904175 : Nat := 118140960795 + 904175 * 2 ^ 59
def prefixEnd_904175 : Nat := 4983230072969 + 3 ^ 40 * 904175 * 2
def baseEnd_904175 : Nat := 412690107359204573203805

theorem tailTrace_904175 : CollatzResearch.WordTrace tailWord_904175 prefixEnd_904175 412690107359204573203805 := by
  unfold tailWord_904175
  simp only [CollatzResearch.WordTrace]
  refine ⟨32977971499335870641041979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21985314332890580427361319 32977971499335870641041979)
  ·
    refine ⟨49466957249003805961562969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32977971499335870641041979 49466957249003805961562969)
    ·
      refine ⟨37100217936752854471172227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49466957249003805961562969 37100217936752854471172227)
      ·
        refine ⟨55650326905129281706758341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37100217936752854471172227 55650326905129281706758341)
        ·
          refine ⟨10434436294711740320017189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55650326905129281706758341 10434436294711740320017189)
          ·
            refine ⟨1956456805258451310003223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10434436294711740320017189 1956456805258451310003223)
            ·
              refine ⟨2934685207887676965004835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956456805258451310003223 2934685207887676965004835)
              ·
                refine ⟨4402027811831515447507253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934685207887676965004835 4402027811831515447507253)
                ·
                  refine ⟨412690107359204573203805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4402027811831515447507253 412690107359204573203805)
                  ·
                    rfl

theorem cell20_904175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_904175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904175 prefixEnd_904175 := by exact prefixLift 904175
  have htrace : WordTrace (prefixWord ++ tailWord_904175) baseStart_904175 baseEnd_904175 := by
    simpa [prefixWord, tailWord_904175, baseEnd_904175] using wordTrace_append hprefix tailTrace_904175
  have hstable : (prefixWord ++ tailWord_904175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904175).length < 2 ^ (prefixWord ++ tailWord_904175).sum := by decide
  have hdescent : baseEnd_904175 < baseStart_904175 := by decide
  rcases family_descends (prefixWord ++ tailWord_904175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904189 : List Nat := [1, 4, 1, 1, 1, 2, 1, 9]
def baseStart_904189 : Nat := 118140960795 + 904189 * 2 ^ 59
def prefixEnd_904189 : Nat := 4983230072969 + 3 ^ 40 * 904189 * 2
def baseEnd_904189 : Nat := 137565499113560915579027

theorem tailTrace_904189 : CollatzResearch.WordTrace tailWord_904189 prefixEnd_904189 137565499113560915579027 := by
  unfold tailWord_904189
  simp only [CollatzResearch.WordTrace]
  refine ⟨32978482121285151032051621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21985654747523434021367747 32978482121285151032051621)
  ·
    refine ⟨6183465397740965818509679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32978482121285151032051621 6183465397740965818509679)
    ·
      refine ⟨9275198096611448727764519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6183465397740965818509679 9275198096611448727764519)
      ·
        refine ⟨13912797144917173091646779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9275198096611448727764519 13912797144917173091646779)
        ·
          refine ⟨20869195717375759637470169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13912797144917173091646779 20869195717375759637470169)
          ·
            refine ⟨15651896788031819728102627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20869195717375759637470169 15651896788031819728102627)
            ·
              refine ⟨23477845182047729592153941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15651896788031819728102627 23477845182047729592153941)
              ·
                refine ⟨137565499113560915579027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23477845182047729592153941 137565499113560915579027)
                ·
                  rfl

theorem cell20_904189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_904189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904189 prefixEnd_904189 := by exact prefixLift 904189
  have htrace : WordTrace (prefixWord ++ tailWord_904189) baseStart_904189 baseEnd_904189 := by
    simpa [prefixWord, tailWord_904189, baseEnd_904189] using wordTrace_append hprefix tailTrace_904189
  have hstable : (prefixWord ++ tailWord_904189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904189).length < 2 ^ (prefixWord ++ tailWord_904189).sum := by decide
  have hdescent : baseEnd_904189 < baseStart_904189 := by decide
  rcases family_descends (prefixWord ++ tailWord_904189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904206 : List Nat := [4, 1, 1, 2, 2, 3, 1, 6]
def baseStart_904206 : Nat := 118140960795 + 904206 * 2 ^ 59
def prefixEnd_904206 : Nat := 4983230072969 + 3 ^ 40 * 904206 * 2
def baseEnd_904206 : Nat := 137568085534635414390115

theorem tailTrace_904206 : CollatzResearch.WordTrace tailWord_904206 prefixEnd_904206 137568085534635414390115 := by
  unfold tailWord_904206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122387770277945366927559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21986068108149041956946981 4122387770277945366927559)
  ·
    refine ⟨6183581655416918050391339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4122387770277945366927559 6183581655416918050391339)
    ·
      refine ⟨9275372483125377075587009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6183581655416918050391339 9275372483125377075587009)
      ·
        refine ⟨6956529362344032806690257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9275372483125377075587009 6956529362344032806690257)
        ·
          refine ⟨5217397021758024605017693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6956529362344032806690257 5217397021758024605017693)
          ·
            refine ⟨1956523883159259226881635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5217397021758024605017693 1956523883159259226881635)
            ·
              refine ⟨2934785824738888840322453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956523883159259226881635 2934785824738888840322453)
              ·
                refine ⟨137568085534635414390115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2934785824738888840322453 137568085534635414390115)
                ·
                  rfl

theorem cell20_904206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_904206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904206 prefixEnd_904206 := by exact prefixLift 904206
  have htrace : WordTrace (prefixWord ++ tailWord_904206) baseStart_904206 baseEnd_904206 := by
    simpa [prefixWord, tailWord_904206, baseEnd_904206] using wordTrace_append hprefix tailTrace_904206
  have hstable : (prefixWord ++ tailWord_904206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904206).length < 2 ^ (prefixWord ++ tailWord_904206).sum := by decide
  have hdescent : baseEnd_904206 < baseStart_904206 := by decide
  rcases family_descends (prefixWord ++ tailWord_904206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904213 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_904213 : Nat := 118140960795 + 904213 * 2 ^ 59
def prefixEnd_904213 : Nat := 4983230072969 + 3 ^ 40 * 904213 * 2
def baseEnd_904213 : Nat := 412707451594645329936983

theorem tailTrace_904213 : CollatzResearch.WordTrace tailWord_904213 prefixEnd_904213 412707451594645329936983 := by
  unfold tailWord_904213
  simp only [CollatzResearch.WordTrace]
  refine ⟨32979357473198203130925293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21986238315465468753950195 32979357473198203130925293)
  ·
    refine ⟨12367259052449326174096985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32979357473198203130925293 12367259052449326174096985)
    ·
      refine ⟨9275444289336994630572739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12367259052449326174096985 9275444289336994630572739)
      ·
        refine ⟨13913166434005491945859109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9275444289336994630572739 13913166434005491945859109)
        ·
          refine ⟨2608718706376029739848583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13913166434005491945859109 2608718706376029739848583)
          ·
            refine ⟨3913078059564044609772875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608718706376029739848583 3913078059564044609772875)
            ·
              refine ⟨5869617089346066914659313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913078059564044609772875 5869617089346066914659313)
              ·
                refine ⟨4402212817009550185994485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5869617089346066914659313 4402212817009550185994485)
                ·
                  refine ⟨412707451594645329936983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4402212817009550185994485 412707451594645329936983)
                  ·
                    rfl

theorem cell20_904213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_904213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904213 prefixEnd_904213 := by exact prefixLift 904213
  have htrace : WordTrace (prefixWord ++ tailWord_904213) baseStart_904213 baseEnd_904213 := by
    simpa [prefixWord, tailWord_904213, baseEnd_904213] using wordTrace_append hprefix tailTrace_904213
  have hstable : (prefixWord ++ tailWord_904213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904213).length < 2 ^ (prefixWord ++ tailWord_904213).sum := by decide
  have hdescent : baseEnd_904213 < baseStart_904213 := by decide
  rcases family_descends (prefixWord ++ tailWord_904213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904216 : List Nat := [2, 1, 2, 3, 2, 2, 3, 3, 2]
def baseStart_904216 : Nat := 118140960795 + 904216 * 2 ^ 59
def prefixEnd_904216 : Nat := 4983230072969 + 3 ^ 40 * 904216 * 2
def baseEnd_904216 : Nat := 412708820876390652836971

theorem tailTrace_904216 : CollatzResearch.WordTrace tailWord_904216 prefixEnd_904216 412708820876390652836971 := by
  unfold tailWord_904216
  simp only [CollatzResearch.WordTrace]
  refine ⟨16489733446093667321642251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21986311261458223095523001 16489733446093667321642251)
  ·
    refine ⟨24734600169140500982463377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16489733446093667321642251 24734600169140500982463377)
    ·
      refine ⟨18550950126855375736847533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24734600169140500982463377 18550950126855375736847533)
      ·
        refine ⟨6956606297570765901317825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18550950126855375736847533 6956606297570765901317825)
        ·
          refine ⟨5217454723178074425988369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6956606297570765901317825 5217454723178074425988369)
          ·
            refine ⟨3913091042383555819491277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5217454723178074425988369 3913091042383555819491277)
            ·
              refine ⟨1467409140893833432309229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3913091042383555819491277 1467409140893833432309229)
              ·
                refine ⟨550278427835187537115961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1467409140893833432309229 550278427835187537115961)
                ·
                  refine ⟨412708820876390652836971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550278427835187537115961 412708820876390652836971)
                  ·
                    rfl

theorem cell20_904216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_904216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904216 prefixEnd_904216 := by exact prefixLift 904216
  have htrace : WordTrace (prefixWord ++ tailWord_904216) baseStart_904216 baseEnd_904216 := by
    simpa [prefixWord, tailWord_904216, baseEnd_904216] using wordTrace_append hprefix tailTrace_904216
  have hstable : (prefixWord ++ tailWord_904216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904216).length < 2 ^ (prefixWord ++ tailWord_904216).sum := by decide
  have hdescent : baseEnd_904216 < baseStart_904216 := by decide
  rcases family_descends (prefixWord ++ tailWord_904216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904227 : List Nat := [1, 1, 1, 4, 3, 2, 8]
def baseStart_904227 : Nat := 118140960795 + 904227 * 2 ^ 59
def prefixEnd_904227 : Nat := 4983230072969 + 3 ^ 40 * 904227 * 2
def baseEnd_904227 : Nat := 45857093508458167052251

theorem tailTrace_904227 : CollatzResearch.WordTrace tailWord_904227 prefixEnd_904227 45857093508458167052251 := by
  unfold tailWord_904227
  simp only [CollatzResearch.WordTrace]
  refine ⟨32979868095147483521934935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21986578730098322347956623 32979868095147483521934935)
  ·
    refine ⟨49469802142721225282902403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32979868095147483521934935 49469802142721225282902403)
    ·
      refine ⟨74204703214081837924353605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49469802142721225282902403 74204703214081837924353605)
      ·
        refine ⟨13913381852640344610816301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74204703214081837924353605 13913381852640344610816301)
        ·
          refine ⟨5217518194740129229056113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13913381852640344610816301 5217518194740129229056113)
          ·
            refine ⟨3913138646055096921792085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5217518194740129229056113 3913138646055096921792085)
            ·
              refine ⟨45857093508458167052251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3913138646055096921792085 45857093508458167052251)
              ·
                rfl

theorem cell20_904227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 8].length) (baseStart_904227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904227 prefixEnd_904227 := by exact prefixLift 904227
  have htrace : WordTrace (prefixWord ++ tailWord_904227) baseStart_904227 baseEnd_904227 := by
    simpa [prefixWord, tailWord_904227, baseEnd_904227] using wordTrace_append hprefix tailTrace_904227
  have hstable : (prefixWord ++ tailWord_904227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904227).length < 2 ^ (prefixWord ++ tailWord_904227).sum := by decide
  have hdescent : baseEnd_904227 < baseStart_904227 := by decide
  rcases family_descends (prefixWord ++ tailWord_904227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904272 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_904272 : Nat := 118140960795 + 904272 * 2 ^ 59
def prefixEnd_904272 : Nat := 4983230072969 + 3 ^ 40 * 904272 * 2
def baseEnd_904272 : Nat := 412734380802303346970075

theorem tailTrace_904272 : CollatzResearch.WordTrace tailWord_904272 prefixEnd_904272 412734380802303346970075 := by
  unfold tailWord_904272
  simp only [CollatzResearch.WordTrace]
  refine ⟨16490754689992228103661535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21987672919989637471548713 16490754689992228103661535)
  ·
    refine ⟨24736132034988342155492303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16490754689992228103661535 24736132034988342155492303)
    ·
      refine ⟨37104198052482513233238455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24736132034988342155492303 37104198052482513233238455)
      ·
        refine ⟨55656297078723769849857683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37104198052482513233238455 55656297078723769849857683)
        ·
          refine ⟨83484445618085654774786525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55656297078723769849857683 83484445618085654774786525)
          ·
            refine ⟨31306667106782120540544947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83484445618085654774786525 31306667106782120540544947)
            ·
              refine ⟨46960000660173180810817421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31306667106782120540544947 46960000660173180810817421)
              ·
                refine ⟨17610000247564942804056533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46960000660173180810817421 17610000247564942804056533)
                ·
                  refine ⟨412734380802303346970075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17610000247564942804056533 412734380802303346970075)
                  ·
                    rfl

theorem cell20_904272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_904272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904272 prefixEnd_904272 := by exact prefixLift 904272
  have htrace : WordTrace (prefixWord ++ tailWord_904272) baseStart_904272 baseEnd_904272 := by
    simpa [prefixWord, tailWord_904272, baseEnd_904272] using wordTrace_append hprefix tailTrace_904272
  have hstable : (prefixWord ++ tailWord_904272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904272).length < 2 ^ (prefixWord ++ tailWord_904272).sum := by decide
  have hdescent : baseEnd_904272 < baseStart_904272 := by decide
  rcases family_descends (prefixWord ++ tailWord_904272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904278 : List Nat := [5, 2, 2, 1, 3, 7]
def baseStart_904278 : Nat := 118140960795 + 904278 * 2 ^ 59
def prefixEnd_904278 : Nat := 4983230072969 + 3 ^ 40 * 904278 * 2
def baseEnd_904278 : Nat := 15286559976510888621113

theorem tailTrace_904278 : CollatzResearch.WordTrace tailWord_904278 prefixEnd_904278 15286559976510888621113 := by
  unfold tailWord_904278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061358013622669952002593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21987818811975146154694325 2061358013622669952002593)
  ·
    refine ⟨1546018510217002464001945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2061358013622669952002593 1546018510217002464001945)
    ·
      refine ⟨1159513882662751848001459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1546018510217002464001945 1159513882662751848001459)
      ·
        refine ⟨1739270823994127772002189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159513882662751848001459 1739270823994127772002189)
        ·
          refine ⟨652226558997797914500821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1739270823994127772002189 652226558997797914500821)
          ·
            refine ⟨15286559976510888621113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 652226558997797914500821 15286559976510888621113)
            ·
              rfl

theorem cell20_904278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 7].length) (baseStart_904278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904278 prefixEnd_904278 := by exact prefixLift 904278
  have htrace : WordTrace (prefixWord ++ tailWord_904278) baseStart_904278 baseEnd_904278 := by
    simpa [prefixWord, tailWord_904278, baseEnd_904278] using wordTrace_append hprefix tailTrace_904278
  have hstable : (prefixWord ++ tailWord_904278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904278).length < 2 ^ (prefixWord ++ tailWord_904278).sum := by decide
  have hdescent : baseEnd_904278 < baseStart_904278 := by decide
  rcases family_descends (prefixWord ++ tailWord_904278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904289 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 3]
def baseStart_904289 : Nat := 118140960795 + 904289 * 2 ^ 59
def prefixEnd_904289 : Nat := 4983230072969 + 3 ^ 40 * 904289 * 2
def baseEnd_904289 : Nat := 412742140065526843403339

theorem tailTrace_904289 : CollatzResearch.WordTrace tailWord_904289 prefixEnd_904289 412742140065526843403339 := by
  unfold tailWord_904289
  simp only [CollatzResearch.WordTrace]
  refine ⟨32982129420922868110691921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21988086280615245407127947 32982129420922868110691921)
  ·
    refine ⟨24736597065692151083018941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32982129420922868110691921 24736597065692151083018941)
    ·
      refine ⟨9276223899634556656132103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24736597065692151083018941 9276223899634556656132103)
      ·
        refine ⟨13914335849451834984198155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9276223899634556656132103 13914335849451834984198155)
        ·
          refine ⟨20871503774177752476297233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13914335849451834984198155 20871503774177752476297233)
          ·
            refine ⟨15653627830633314357222925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20871503774177752476297233 15653627830633314357222925)
            ·
              refine ⟨5870110436487492883958597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15653627830633314357222925 5870110436487492883958597)
              ·
                refine ⟨1100645706841404915742237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5870110436487492883958597 1100645706841404915742237)
                ·
                  refine ⟨412742140065526843403339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100645706841404915742237 412742140065526843403339)
                  ·
                    rfl

theorem cell20_904289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_904289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904289 prefixEnd_904289 := by exact prefixLift 904289
  have htrace : WordTrace (prefixWord ++ tailWord_904289) baseStart_904289 baseEnd_904289 := by
    simpa [prefixWord, tailWord_904289, baseEnd_904289] using wordTrace_append hprefix tailTrace_904289
  have hstable : (prefixWord ++ tailWord_904289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904289).length < 2 ^ (prefixWord ++ tailWord_904289).sum := by decide
  have hdescent : baseEnd_904289 < baseStart_904289 := by decide
  rcases family_descends (prefixWord ++ tailWord_904289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904313 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 4]
def baseStart_904313 : Nat := 118140960795 + 904313 * 2 ^ 59
def prefixEnd_904313 : Nat := 4983230072969 + 3 ^ 40 * 904313 * 2
def baseEnd_904313 : Nat := 412753094319489426603241

theorem tailTrace_904313 : CollatzResearch.WordTrace tailWord_904313 prefixEnd_904313 412753094319489426603241 := by
  unfold tailWord_904313
  simp only [CollatzResearch.WordTrace]
  refine ⟨32983004772835920209565593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21988669848557280139710395 32983004772835920209565593)
  ·
    refine ⟨24737253579626940157174195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32983004772835920209565593 24737253579626940157174195)
    ·
      refine ⟨37105880369440410235761293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24737253579626940157174195 37105880369440410235761293)
      ·
        refine ⟨13914705138540153838410485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37105880369440410235761293 13914705138540153838410485)
        ·
          refine ⟨1304503606738139422350983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13914705138540153838410485 1304503606738139422350983)
          ·
            refine ⟨1956755410107209133526475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304503606738139422350983 1956755410107209133526475)
            ·
              refine ⟨2935133115160813700289713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956755410107209133526475 2935133115160813700289713)
              ·
                refine ⟨2201349836370610275217285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935133115160813700289713 2201349836370610275217285)
                ·
                  refine ⟨412753094319489426603241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201349836370610275217285 412753094319489426603241)
                  ·
                    rfl

theorem cell20_904313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_904313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904313 prefixEnd_904313 := by exact prefixLift 904313
  have htrace : WordTrace (prefixWord ++ tailWord_904313) baseStart_904313 baseEnd_904313 := by
    simpa [prefixWord, tailWord_904313, baseEnd_904313] using wordTrace_append hprefix tailTrace_904313
  have hstable : (prefixWord ++ tailWord_904313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904313).length < 2 ^ (prefixWord ++ tailWord_904313).sum := by decide
  have hdescent : baseEnd_904313 < baseStart_904313 := by decide
  rcases family_descends (prefixWord ++ tailWord_904313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904330 : List Nat := [3, 1, 2, 3, 1, 1, 4, 3, 2]
def baseStart_904330 : Nat := 118140960795 + 904330 * 2 ^ 59
def prefixEnd_904330 : Nat := 4983230072969 + 3 ^ 40 * 904330 * 2
def baseEnd_904330 : Nat := 412760853582712923036505

theorem tailTrace_904330 : CollatzResearch.WordTrace tailWord_904330 prefixEnd_904330 412760853582712923036505 := by
  unfold tailWord_904330
  simp only [CollatzResearch.WordTrace]
  refine ⟨8245906203443583028233611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21989083209182888075289629 8245906203443583028233611)
  ·
    refine ⟨12368859305165374542350417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8245906203443583028233611 12368859305165374542350417)
    ·
      refine ⟨9276644478874030906762813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12368859305165374542350417 9276644478874030906762813)
      ·
        refine ⟨3478741679577761590036055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9276644478874030906762813 3478741679577761590036055)
        ·
          refine ⟨5218112519366642385054083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478741679577761590036055 5218112519366642385054083)
          ·
            refine ⟨7827168779049963577581125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218112519366642385054083 7827168779049963577581125)
            ·
              refine ⟨1467594146071868170796461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7827168779049963577581125 1467594146071868170796461)
              ·
                refine ⟨550347804776950564048673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1467594146071868170796461 550347804776950564048673)
                ·
                  refine ⟨412760853582712923036505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550347804776950564048673 412760853582712923036505)
                  ·
                    rfl

theorem cell20_904330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_904330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904330 prefixEnd_904330 := by exact prefixLift 904330
  have htrace : WordTrace (prefixWord ++ tailWord_904330) baseStart_904330 baseEnd_904330 := by
    simpa [prefixWord, tailWord_904330, baseEnd_904330] using wordTrace_append hprefix tailTrace_904330
  have hstable : (prefixWord ++ tailWord_904330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904330).length < 2 ^ (prefixWord ++ tailWord_904330).sum := by decide
  have hdescent : baseEnd_904330 < baseStart_904330 := by decide
  rcases family_descends (prefixWord ++ tailWord_904330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904344 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 3]
def baseStart_904344 : Nat := 118140960795 + 904344 * 2 ^ 59
def prefixEnd_904344 : Nat := 4983230072969 + 3 ^ 40 * 904344 * 2
def baseEnd_904344 : Nat := 412767243564191096569781

theorem tailTrace_904344 : CollatzResearch.WordTrace tailWord_904344 prefixEnd_904344 412767243564191096569781 := by
  unfold tailWord_904344
  simp only [CollatzResearch.WordTrace]
  refine ⟨16492067717861806251972043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21989423623815741669296057 16492067717861806251972043)
  ·
    refine ⟨24738101576792709377958065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16492067717861806251972043 24738101576792709377958065)
    ·
      refine ⟨18553576182594532033468549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24738101576792709377958065 18553576182594532033468549)
      ·
        refine ⟨3478795534236474756275353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18553576182594532033468549 3478795534236474756275353)
        ·
          refine ⟨2609096650677356067206515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478795534236474756275353 2609096650677356067206515)
          ·
            refine ⟨3913644976016034100809773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609096650677356067206515 3913644976016034100809773)
            ·
              refine ⟨1467616866006012787803665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3913644976016034100809773 1467616866006012787803665)
              ·
                refine ⟨1100712649504509590852749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467616866006012787803665 1100712649504509590852749)
                ·
                  refine ⟨412767243564191096569781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100712649504509590852749 412767243564191096569781)
                  ·
                    rfl

theorem cell20_904344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_904344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904344 prefixEnd_904344 := by exact prefixLift 904344
  have htrace : WordTrace (prefixWord ++ tailWord_904344) baseStart_904344 baseEnd_904344 := by
    simpa [prefixWord, tailWord_904344, baseEnd_904344] using wordTrace_append hprefix tailTrace_904344
  have hstable : (prefixWord ++ tailWord_904344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904344).length < 2 ^ (prefixWord ++ tailWord_904344).sum := by decide
  have hdescent : baseEnd_904344 < baseStart_904344 := by decide
  rcases family_descends (prefixWord ++ tailWord_904344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904385 : List Nat := [1, 2, 6, 1, 1, 1, 3, 3, 2]
def baseStart_904385 : Nat := 118140960795 + 904385 * 2 ^ 59
def prefixEnd_904385 : Nat := 4983230072969 + 3 ^ 40 * 904385 * 2
def baseEnd_904385 : Nat := 412785957081377176202947

theorem tailTrace_904385 : CollatzResearch.WordTrace tailWord_904385 prefixEnd_904385 412785957081377176202947 := by
  unfold tailWord_904385
  simp only [CollatzResearch.WordTrace]
  refine ⟨32985630828575076506186609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21990420552383384337457739 32985630828575076506186609)
  ·
    refine ⟨24739223121431307379639957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32985630828575076506186609 24739223121431307379639957)
    ·
      refine ⟨1159651083817092533420623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24739223121431307379639957 1159651083817092533420623)
      ·
        refine ⟨1739476625725638800130935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159651083817092533420623 1739476625725638800130935)
        ·
          refine ⟨2609214938588458200196403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739476625725638800130935 2609214938588458200196403)
          ·
            refine ⟨3913822407882687300294605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609214938588458200196403 3913822407882687300294605)
            ·
              refine ⟨1467683402956007737610477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3913822407882687300294605 1467683402956007737610477)
              ·
                refine ⟨550381276108502901603929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1467683402956007737610477 550381276108502901603929)
                ·
                  refine ⟨412785957081377176202947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550381276108502901603929 412785957081377176202947)
                  ·
                    rfl

theorem cell20_904385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_904385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904385 prefixEnd_904385 := by exact prefixLift 904385
  have htrace : WordTrace (prefixWord ++ tailWord_904385) baseStart_904385 baseEnd_904385 := by
    simpa [prefixWord, tailWord_904385, baseEnd_904385] using wordTrace_append hprefix tailTrace_904385
  have hstable : (prefixWord ++ tailWord_904385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904385).length < 2 ^ (prefixWord ++ tailWord_904385).sum := by decide
  have hdescent : baseEnd_904385 < baseStart_904385 := by decide
  rcases family_descends (prefixWord ++ tailWord_904385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904413 : List Nat := [1, 4, 3, 2, 2, 1, 2, 5]
def baseStart_904413 : Nat := 118140960795 + 904413 * 2 ^ 59
def prefixEnd_904413 : Nat := 4983230072969 + 3 ^ 40 * 904413 * 2
def baseEnd_904413 : Nat := 137599579014777841089833

theorem tailTrace_904413 : CollatzResearch.WordTrace tailWord_904413 prefixEnd_904413 137599579014777841089833 := by
  unfold tailWord_904413
  simp only [CollatzResearch.WordTrace]
  refine ⟨32986652072473637288205893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21991101381649091525470595 32986652072473637288205893)
  ·
    refine ⟨6184997263588806991538605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32986652072473637288205893 6184997263588806991538605)
    ·
      refine ⟨2319373973845802621826977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6184997263588806991538605 2319373973845802621826977)
      ·
        refine ⟨1739530480384351966370233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2319373973845802621826977 1739530480384351966370233)
        ·
          refine ⟨1304647860288263974777675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1739530480384351966370233 1304647860288263974777675)
          ·
            refine ⟨1956971790432395962166513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304647860288263974777675 1956971790432395962166513)
            ·
              refine ⟨1467728842824296971624885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956971790432395962166513 1467728842824296971624885)
              ·
                refine ⟨137599579014777841089833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1467728842824296971624885 137599579014777841089833)
                ·
                  rfl

theorem cell20_904413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 5].length) (baseStart_904413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904413 prefixEnd_904413 := by exact prefixLift 904413
  have htrace : WordTrace (prefixWord ++ tailWord_904413) baseStart_904413 baseEnd_904413 := by
    simpa [prefixWord, tailWord_904413, baseEnd_904413] using wordTrace_append hprefix tailTrace_904413
  have hstable : (prefixWord ++ tailWord_904413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904413).length < 2 ^ (prefixWord ++ tailWord_904413).sum := by decide
  have hdescent : baseEnd_904413 < baseStart_904413 := by decide
  rcases family_descends (prefixWord ++ tailWord_904413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904417 : List Nat := [1, 2, 3, 1, 3, 2, 1, 7]
def baseStart_904417 : Nat := 118140960795 + 904417 * 2 ^ 59
def prefixEnd_904417 : Nat := 4983230072969 + 3 ^ 40 * 904417 * 2
def baseEnd_904417 : Nat := 137600187584442429045383

theorem tailTrace_904417 : CollatzResearch.WordTrace tailWord_904417 prefixEnd_904417 137600187584442429045383 := by
  unfold tailWord_904417
  simp only [CollatzResearch.WordTrace]
  refine ⟨32986797964459145971351505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21991198642972763980901003 32986797964459145971351505)
  ·
    refine ⟨24740098473344359478513629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32986797964459145971351505 24740098473344359478513629)
    ·
      refine ⟨9277536927504134804442611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24740098473344359478513629 9277536927504134804442611)
      ·
        refine ⟨13916305391256202206663917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9277536927504134804442611 13916305391256202206663917)
        ·
          refine ⟨5218614521721075827498969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13916305391256202206663917 5218614521721075827498969)
          ·
            refine ⟨3913960891290806870624227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5218614521721075827498969 3913960891290806870624227)
            ·
              refine ⟨5870941336936210305936341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913960891290806870624227 5870941336936210305936341)
              ·
                refine ⟨137600187584442429045383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5870941336936210305936341 137600187584442429045383)
                ·
                  rfl

theorem cell20_904417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_904417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904417 prefixEnd_904417 := by exact prefixLift 904417
  have htrace : WordTrace (prefixWord ++ tailWord_904417) baseStart_904417 baseEnd_904417 := by
    simpa [prefixWord, tailWord_904417, baseEnd_904417] using wordTrace_append hprefix tailTrace_904417
  have hstable : (prefixWord ++ tailWord_904417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904417).length < 2 ^ (prefixWord ++ tailWord_904417).sum := by decide
  have hdescent : baseEnd_904417 < baseStart_904417 := by decide
  rcases family_descends (prefixWord ++ tailWord_904417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904420 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 3]
def baseStart_904420 : Nat := 118140960795 + 904420 * 2 ^ 59
def prefixEnd_904420 : Nat := 4983230072969 + 3 ^ 40 * 904420 * 2
def baseEnd_904420 : Nat := 412801932035072610036137

theorem tailTrace_904420 : CollatzResearch.WordTrace tailWord_904420 prefixEnd_904420 412801932035072610036137 := by
  unfold tailWord_904420
  simp only [CollatzResearch.WordTrace]
  refine ⟨16493453691724138741855357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21991271588965518322473809 16493453691724138741855357)
  ·
    refine ⟨6185045134396552028195759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16493453691724138741855357 6185045134396552028195759)
    ·
      refine ⟨9277567701594828042293639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6185045134396552028195759 9277567701594828042293639)
      ·
        refine ⟨13916351552392242063440459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9277567701594828042293639 13916351552392242063440459)
        ·
          refine ⟨20874527328588363095160689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13916351552392242063440459 20874527328588363095160689)
          ·
            refine ⟨15655895496441272321370517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20874527328588363095160689 15655895496441272321370517)
            ·
              refine ⟨733870101395684640064243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15655895496441272321370517 733870101395684640064243)
              ·
                refine ⟨1100805152093526960096365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733870101395684640064243 1100805152093526960096365)
                ·
                  refine ⟨412801932035072610036137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100805152093526960096365 412801932035072610036137)
                  ·
                    rfl

theorem cell20_904420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_904420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904420 prefixEnd_904420 := by exact prefixLift 904420
  have htrace : WordTrace (prefixWord ++ tailWord_904420) baseStart_904420 baseEnd_904420 := by
    simpa [prefixWord, tailWord_904420, baseEnd_904420] using wordTrace_append hprefix tailTrace_904420
  have hstable : (prefixWord ++ tailWord_904420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904420).length < 2 ^ (prefixWord ++ tailWord_904420).sum := by decide
  have hdescent : baseEnd_904420 < baseStart_904420 := by decide
  rcases family_descends (prefixWord ++ tailWord_904420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904465 : List Nat := [1, 2, 2, 1, 1, 4, 3, 4, 2]
def baseStart_904465 : Nat := 118140960795 + 904465 * 2 ^ 59
def prefixEnd_904465 : Nat := 4983230072969 + 3 ^ 40 * 904465 * 2
def baseEnd_904465 : Nat := 412822471261252453535953

theorem tailTrace_904465 : CollatzResearch.WordTrace tailWord_904465 prefixEnd_904465 412822471261252453535953 := by
  unfold tailWord_904465
  simp only [CollatzResearch.WordTrace]
  refine ⟨32988548668285250169098849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21992365778856833446065899 32988548668285250169098849)
  ·
    refine ⟨24741411501213937626824137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32988548668285250169098849 24741411501213937626824137)
    ·
      refine ⟨18556058625910453220118103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24741411501213937626824137 18556058625910453220118103)
      ·
        refine ⟨27834087938865679830177155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18556058625910453220118103 27834087938865679830177155)
        ·
          refine ⟨41751131908298519745265733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27834087938865679830177155 41751131908298519745265733)
          ·
            refine ⟨7828337232805972452237325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41751131908298519745265733 7828337232805972452237325)
            ·
              refine ⟨2935626462302239669588997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7828337232805972452237325 2935626462302239669588997)
              ·
                refine ⟨550429961681669938047937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2935626462302239669588997 550429961681669938047937)
                ·
                  refine ⟨412822471261252453535953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550429961681669938047937 412822471261252453535953)
                  ·
                    rfl

theorem cell20_904465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_904465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904465 prefixEnd_904465 := by exact prefixLift 904465
  have htrace : WordTrace (prefixWord ++ tailWord_904465) baseStart_904465 baseEnd_904465 := by
    simpa [prefixWord, tailWord_904465, baseEnd_904465] using wordTrace_append hprefix tailTrace_904465
  have hstable : (prefixWord ++ tailWord_904465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904465).length < 2 ^ (prefixWord ++ tailWord_904465).sum := by decide
  have hdescent : baseEnd_904465 < baseStart_904465 := by decide
  rcases family_descends (prefixWord ++ tailWord_904465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904472 : List Nat := [2, 1, 2, 3, 1, 5, 1, 5]
def baseStart_904472 : Nat := 118140960795 + 904472 * 2 ^ 59
def prefixEnd_904472 : Nat := 4983230072969 + 3 ^ 40 * 904472 * 2
def baseEnd_904472 : Nat := 137608555417330513434197

theorem tailTrace_904472 : CollatzResearch.WordTrace tailWord_904472 prefixEnd_904472 137608555417330513434197 := by
  unfold tailWord_904472
  simp only [CollatzResearch.WordTrace]
  refine ⟨16494401989629945182301835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21992535986173260243069113 16494401989629945182301835)
  ·
    refine ⟨24741602984444917773452753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16494401989629945182301835 24741602984444917773452753)
    ·
      refine ⟨18556202238333688330089565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24741602984444917773452753 18556202238333688330089565)
      ·
        refine ⟨6958575839375133123783587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18556202238333688330089565 6958575839375133123783587)
        ·
          refine ⟨10437863759062699685675381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6958575839375133123783587 10437863759062699685675381)
          ·
            refine ⟨978549727412128095532067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10437863759062699685675381 978549727412128095532067)
            ·
              refine ⟨1467824591118192143298101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978549727412128095532067 1467824591118192143298101)
              ·
                refine ⟨137608555417330513434197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1467824591118192143298101 137608555417330513434197)
                ·
                  rfl

theorem cell20_904472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_904472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904472 prefixEnd_904472 := by exact prefixLift 904472
  have htrace : WordTrace (prefixWord ++ tailWord_904472) baseStart_904472 baseEnd_904472 := by
    simpa [prefixWord, tailWord_904472, baseEnd_904472] using wordTrace_append hprefix tailTrace_904472
  have hstable : (prefixWord ++ tailWord_904472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904472).length < 2 ^ (prefixWord ++ tailWord_904472).sum := by decide
  have hdescent : baseEnd_904472 < baseStart_904472 := by decide
  rcases family_descends (prefixWord ++ tailWord_904472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904513 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 3]
def baseStart_904513 : Nat := 118140960795 + 904513 * 2 ^ 59
def prefixEnd_904513 : Nat := 4983230072969 + 3 ^ 40 * 904513 * 2
def baseEnd_904513 : Nat := 412844379769177619935757

theorem tailTrace_904513 : CollatzResearch.WordTrace tailWord_904513 prefixEnd_904513 412844379769177619935757 := by
  unfold tailWord_904513
  simp only [CollatzResearch.WordTrace]
  refine ⟨32990299372111354366846193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21993532914740902911230795 32990299372111354366846193)
  ·
    refine ⟨24742724529083515775134645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32990299372111354366846193 24742724529083515775134645)
    ·
      refine ⟨2319630424601579603918873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24742724529083515775134645 2319630424601579603918873)
      ·
        refine ⟨1739722818451184702939155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2319630424601579603918873 1739722818451184702939155)
        ·
          refine ⟨2609584227676777054408733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739722818451184702939155 2609584227676777054408733)
          ·
            refine ⟨978594085378791395403275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2609584227676777054408733 978594085378791395403275)
            ·
              refine ⟨1467891128068187093104913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978594085378791395403275 1467891128068187093104913)
              ·
                refine ⟨1100918346051140319828685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467891128068187093104913 1100918346051140319828685)
                ·
                  refine ⟨412844379769177619935757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100918346051140319828685 412844379769177619935757)
                  ·
                    rfl

theorem cell20_904513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_904513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904513 prefixEnd_904513 := by exact prefixLift 904513
  have htrace : WordTrace (prefixWord ++ tailWord_904513) baseStart_904513 baseEnd_904513 := by
    simpa [prefixWord, tailWord_904513, baseEnd_904513] using wordTrace_append hprefix tailTrace_904513
  have hstable : (prefixWord ++ tailWord_904513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904513).length < 2 ^ (prefixWord ++ tailWord_904513).sum := by decide
  have hdescent : baseEnd_904513 < baseStart_904513 := by decide
  rcases family_descends (prefixWord ++ tailWord_904513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904524 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_904524 : Nat := 118140960795 + 904524 * 2 ^ 59
def prefixEnd_904524 : Nat := 4983230072969 + 3 ^ 40 * 904524 * 2
def baseEnd_904524 : Nat := 412849400468910470569045

theorem tailTrace_904524 : CollatzResearch.WordTrace tailWord_904524 prefixEnd_904524 412849400468910470569045 := by
  unfold tailWord_904524
  simp only [CollatzResearch.WordTrace]
  refine ⟨16495350287535751622748313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21993800383381002163664417 16495350287535751622748313)
  ·
    refine ⟨12371512715651813717061235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16495350287535751622748313 12371512715651813717061235)
    ·
      refine ⟨18557269073477720575591853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12371512715651813717061235 18557269073477720575591853)
      ·
        refine ⟨6958975902554145215846945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18557269073477720575591853 6958975902554145215846945)
        ·
          refine ⟨5219231926915608911885209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6958975902554145215846945 5219231926915608911885209)
          ·
            refine ⟨3914423945186706683913907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5219231926915608911885209 3914423945186706683913907)
            ·
              refine ⟨5871635917780060025870861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3914423945186706683913907 5871635917780060025870861)
              ·
                refine ⟨2201863469167522509701573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5871635917780060025870861 2201863469167522509701573)
                ·
                  refine ⟨412849400468910470569045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201863469167522509701573 412849400468910470569045)
                  ·
                    rfl

theorem cell20_904524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_904524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904524 prefixEnd_904524 := by exact prefixLift 904524
  have htrace : WordTrace (prefixWord ++ tailWord_904524) baseStart_904524 baseEnd_904524 := by
    simpa [prefixWord, tailWord_904524, baseEnd_904524] using wordTrace_append hprefix tailTrace_904524
  have hstable : (prefixWord ++ tailWord_904524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904524).length < 2 ^ (prefixWord ++ tailWord_904524).sum := by decide
  have hdescent : baseEnd_904524 < baseStart_904524 := by decide
  rcases family_descends (prefixWord ++ tailWord_904524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904548 : List Nat := [2, 3, 1, 1, 3, 2, 4, 4]
def baseStart_904548 : Nat := 118140960795 + 904548 * 2 ^ 59
def prefixEnd_904548 : Nat := 4983230072969 + 3 ^ 40 * 904548 * 2
def baseEnd_904548 : Nat := 137620118240957684589649

theorem tailTrace_904548 : CollatzResearch.WordTrace tailWord_904548 prefixEnd_904548 137620118240957684589649 := by
  unfold tailWord_904548
  simp only [CollatzResearch.WordTrace]
  refine ⟨16495787963492277672185149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21994383951323036896246865 16495787963492277672185149)
  ·
    refine ⟨6185920486309604127069431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16495787963492277672185149 6185920486309604127069431)
    ·
      refine ⟨9278880729464406190604147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6185920486309604127069431 9278880729464406190604147)
      ·
        refine ⟨13918321094196609285906221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9278880729464406190604147 13918321094196609285906221)
        ·
          refine ⟨5219370410323728482214833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13918321094196609285906221 5219370410323728482214833)
          ·
            refine ⟨3914527807742796361661125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5219370410323728482214833 3914527807742796361661125)
            ·
              refine ⟨733973963951774317811461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3914527807742796361661125 733973963951774317811461)
              ·
                refine ⟨137620118240957684589649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 733973963951774317811461 137620118240957684589649)
                ·
                  rfl

theorem cell20_904548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_904548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904548 prefixEnd_904548 := by exact prefixLift 904548
  have htrace : WordTrace (prefixWord ++ tailWord_904548) baseStart_904548 baseEnd_904548 := by
    simpa [prefixWord, tailWord_904548, baseEnd_904548] using wordTrace_append hprefix tailTrace_904548
  have hstable : (prefixWord ++ tailWord_904548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904548).length < 2 ^ (prefixWord ++ tailWord_904548).sum := by decide
  have hdescent : baseEnd_904548 < baseStart_904548 := by decide
  rcases family_descends (prefixWord ++ tailWord_904548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904554 : List Nat := [3, 1, 3, 3, 3, 1, 1, 3, 2]
def baseStart_904554 : Nat := 118140960795 + 904554 * 2 ^ 59
def prefixEnd_904554 : Nat := 4983230072969 + 3 ^ 40 * 904554 * 2
def baseEnd_904554 : Nat := 412863093286363699568923

theorem tailTrace_904554 : CollatzResearch.WordTrace tailWord_904554 prefixEnd_904554 412863093286363699568923 := by
  unfold tailWord_904554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8247948691240704592272179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21994529843308545579392477 8247948691240704592272179)
  ·
    refine ⟨12371923036861056888408269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8247948691240704592272179 12371923036861056888408269)
    ·
      refine ⟨4639471138822896333153101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12371923036861056888408269 4639471138822896333153101)
      ·
        refine ⟨1739801677058586124932413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4639471138822896333153101 1739801677058586124932413)
        ·
          refine ⟨652425628896969796849655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1739801677058586124932413 652425628896969796849655)
          ·
            refine ⟨978638443345454695274483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652425628896969796849655 978638443345454695274483)
            ·
              refine ⟨1467957665018182042911725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978638443345454695274483 1467957665018182042911725)
              ·
                refine ⟨550484124381818266091897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1467957665018182042911725 550484124381818266091897)
                ·
                  refine ⟨412863093286363699568923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550484124381818266091897 412863093286363699568923)
                  ·
                    rfl

theorem cell20_904554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_904554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904554 prefixEnd_904554 := by exact prefixLift 904554
  have htrace : WordTrace (prefixWord ++ tailWord_904554) baseStart_904554 baseEnd_904554 := by
    simpa [prefixWord, tailWord_904554, baseEnd_904554] using wordTrace_append hprefix tailTrace_904554
  have hstable : (prefixWord ++ tailWord_904554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904554).length < 2 ^ (prefixWord ++ tailWord_904554).sum := by decide
  have hdescent : baseEnd_904554 < baseStart_904554 := by decide
  rcases family_descends (prefixWord ++ tailWord_904554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904565 : List Nat := [1, 3, 4, 1, 4, 1, 6]
def baseStart_904565 : Nat := 118140960795 + 904565 * 2 ^ 59
def prefixEnd_904565 : Nat := 4983230072969 + 3 ^ 40 * 904565 * 2
def baseEnd_904565 : Nat := 45874234887344061133579

theorem tailTrace_904565 : CollatzResearch.WordTrace tailWord_904565 prefixEnd_904565 45874234887344061133579 := by
  unfold tailWord_904565
  simp only [CollatzResearch.WordTrace]
  refine ⟨32992195967922967247739149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21994797311948644831826099 32992195967922967247739149)
  ·
    refine ⟨12372073487971112717902181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32992195967922967247739149 12372073487971112717902181)
    ·
      refine ⟨2319763778994583634606659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12372073487971112717902181 2319763778994583634606659)
      ·
        refine ⟨3479645668491875451909989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319763778994583634606659 3479645668491875451909989)
        ·
          refine ⟨652433562842226647233123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3479645668491875451909989 652433562842226647233123)
          ·
            refine ⟨978650344263339970849685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652433562842226647233123 978650344263339970849685)
            ·
              refine ⟨45874234887344061133579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 978650344263339970849685 45874234887344061133579)
              ·
                rfl

theorem cell20_904565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 6].length) (baseStart_904565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904565 prefixEnd_904565 := by exact prefixLift 904565
  have htrace : WordTrace (prefixWord ++ tailWord_904565) baseStart_904565 baseEnd_904565 := by
    simpa [prefixWord, tailWord_904565, baseEnd_904565] using wordTrace_append hprefix tailTrace_904565
  have hstable : (prefixWord ++ tailWord_904565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904565).length < 2 ^ (prefixWord ++ tailWord_904565).sum := by decide
  have hdescent : baseEnd_904565 < baseStart_904565 := by decide
  rcases family_descends (prefixWord ++ tailWord_904565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904579 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 4]
def baseStart_904579 : Nat := 118140960795 + 904579 * 2 ^ 59
def prefixEnd_904579 : Nat := 4983230072969 + 3 ^ 40 * 904579 * 2
def baseEnd_904579 : Nat := 412874503967574723735487

theorem tailTrace_904579 : CollatzResearch.WordTrace tailWord_904579 prefixEnd_904579 412874503967574723735487 := by
  unfold tailWord_904579
  simp only [CollatzResearch.WordTrace]
  refine ⟨32992706589872247638748791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21995137726581498425832527 32992706589872247638748791)
  ·
    refine ⟨49489059884808371458123187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32992706589872247638748791 49489059884808371458123187)
    ·
      refine ⟨74233589827212557187184781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49489059884808371458123187 74233589827212557187184781)
      ·
        refine ⟨27837596185204708945194293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74233589827212557187184781 27837596185204708945194293)
        ·
          refine ⟨2609774642362941463611965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27837596185204708945194293 2609774642362941463611965)
          ·
            refine ⟨978665490886103048854487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2609774642362941463611965 978665490886103048854487)
            ·
              refine ⟨1467998236329154573281731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978665490886103048854487 1467998236329154573281731)
              ·
                refine ⟨2201997354493731859922597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467998236329154573281731 2201997354493731859922597)
                ·
                  refine ⟨412874503967574723735487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201997354493731859922597 412874503967574723735487)
                  ·
                    rfl

theorem cell20_904579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 4].length) (baseStart_904579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904579 prefixEnd_904579 := by exact prefixLift 904579
  have htrace : WordTrace (prefixWord ++ tailWord_904579) baseStart_904579 baseEnd_904579 := by
    simpa [prefixWord, tailWord_904579, baseEnd_904579] using wordTrace_append hprefix tailTrace_904579
  have hstable : (prefixWord ++ tailWord_904579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904579).length < 2 ^ (prefixWord ++ tailWord_904579).sum := by decide
  have hdescent : baseEnd_904579 < baseStart_904579 := by decide
  rcases family_descends (prefixWord ++ tailWord_904579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904607 : List Nat := [1, 1, 2, 5, 1, 2, 2, 6]
def baseStart_904607 : Nat := 118140960795 + 904607 * 2 ^ 59
def prefixEnd_904607 : Nat := 4983230072969 + 3 ^ 40 * 904607 * 2
def baseEnd_904607 : Nat := 137629094643510356934013

theorem tailTrace_904607 : CollatzResearch.WordTrace tailWord_904607 prefixEnd_904607 137629094643510356934013 := by
  unfold tailWord_904607
  simp only [CollatzResearch.WordTrace]
  refine ⟨32993727833770808420768075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21995818555847205613845383 32993727833770808420768075)
  ·
    refine ⟨49490591750656212631152113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32993727833770808420768075 49490591750656212631152113)
    ·
      refine ⟨37117943812992159473364085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49490591750656212631152113 37117943812992159473364085)
      ·
        refine ⟨3479807232468014950627883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37117943812992159473364085 3479807232468014950627883)
        ·
          refine ⟨5219710848702022425941825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3479807232468014950627883 5219710848702022425941825)
          ·
            refine ⟨3914783136526516819456369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5219710848702022425941825 3914783136526516819456369)
            ·
              refine ⟨2936087352394887614592277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3914783136526516819456369 2936087352394887614592277)
              ·
                refine ⟨137629094643510356934013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2936087352394887614592277 137629094643510356934013)
                ·
                  rfl

theorem cell20_904607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_904607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904607 prefixEnd_904607 := by exact prefixLift 904607
  have htrace : WordTrace (prefixWord ++ tailWord_904607) baseStart_904607 baseEnd_904607 := by
    simpa [prefixWord, tailWord_904607, baseEnd_904607] using wordTrace_append hprefix tailTrace_904607
  have hstable : (prefixWord ++ tailWord_904607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904607).length < 2 ^ (prefixWord ++ tailWord_904607).sum := by decide
  have hdescent : baseEnd_904607 < baseStart_904607 := by decide
  rcases family_descends (prefixWord ++ tailWord_904607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904631 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 3]
def baseStart_904631 : Nat := 118140960795 + 904631 * 2 ^ 59
def prefixEnd_904631 : Nat := 4983230072969 + 3 ^ 40 * 904631 * 2
def baseEnd_904631 : Nat := 412898238184493654001941

theorem tailTrace_904631 : CollatzResearch.WordTrace tailWord_904631 prefixEnd_904631 412898238184493654001941 := by
  unfold tailWord_904631
  simp only [CollatzResearch.WordTrace]
  refine ⟨32994603185683860519641747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21996402123789240346427831 32994603185683860519641747)
  ·
    refine ⟨49491904778525790779462621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32994603185683860519641747 49491904778525790779462621)
    ·
      refine ⟨18559464291947171542298483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49491904778525790779462621 18559464291947171542298483)
      ·
        refine ⟨27839196437920757313447725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18559464291947171542298483 27839196437920757313447725)
        ·
          refine ⟨10439698664220283992542897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27839196437920757313447725 10439698664220283992542897)
          ·
            refine ⟨7829773998165212994407173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10439698664220283992542897 7829773998165212994407173)
            ·
              refine ⟨1468082624655977436451345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7829773998165212994407173 1468082624655977436451345)
              ·
                refine ⟨1101061968491983077338509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468082624655977436451345 1101061968491983077338509)
                ·
                  refine ⟨412898238184493654001941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101061968491983077338509 412898238184493654001941)
                  ·
                    rfl

theorem cell20_904631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3].length) (baseStart_904631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904631 prefixEnd_904631 := by exact prefixLift 904631
  have htrace : WordTrace (prefixWord ++ tailWord_904631) baseStart_904631 baseEnd_904631 := by
    simpa [prefixWord, tailWord_904631, baseEnd_904631] using wordTrace_append hprefix tailTrace_904631
  have hstable : (prefixWord ++ tailWord_904631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904631).length < 2 ^ (prefixWord ++ tailWord_904631).sum := by decide
  have hdescent : baseEnd_904631 < baseStart_904631 := by decide
  rcases family_descends (prefixWord ++ tailWord_904631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904638 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_904638 : Nat := 118140960795 + 904638 * 2 ^ 59
def prefixEnd_904638 : Nat := 4983230072969 + 3 ^ 40 * 904638 * 2
def baseEnd_904638 : Nat := 412901433175232740768579

theorem tailTrace_904638 : CollatzResearch.WordTrace tailWord_904638 prefixEnd_904638 412901433175232740768579 := by
  unfold tailWord_904638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4124357312082312589393321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21996572331105667143431045 4124357312082312589393321)
  ·
    refine ⟨3093267984061734442044991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4124357312082312589393321 3093267984061734442044991)
    ·
      refine ⟨4639901976092601663067487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3093267984061734442044991 4639901976092601663067487)
      ·
        refine ⟨6959852964138902494601231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639901976092601663067487 6959852964138902494601231)
        ·
          refine ⟨10439779446208353741901847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959852964138902494601231 10439779446208353741901847)
          ·
            refine ⟨15659669169312530612852771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10439779446208353741901847 15659669169312530612852771)
            ·
              refine ⟨23489503753968795919279157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15659669169312530612852771 23489503753968795919279157)
              ·
                refine ⟨2202140976934574617432421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23489503753968795919279157 2202140976934574617432421)
                ·
                  refine ⟨412901433175232740768579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202140976934574617432421 412901433175232740768579)
                  ·
                    rfl

theorem cell20_904638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_904638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904638 prefixEnd_904638 := by exact prefixLift 904638
  have htrace : WordTrace (prefixWord ++ tailWord_904638) baseStart_904638 baseEnd_904638 := by
    simpa [prefixWord, tailWord_904638, baseEnd_904638] using wordTrace_append hprefix tailTrace_904638
  have hstable : (prefixWord ++ tailWord_904638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904638).length < 2 ^ (prefixWord ++ tailWord_904638).sum := by decide
  have hdescent : baseEnd_904638 < baseStart_904638 := by decide
  rcases family_descends (prefixWord ++ tailWord_904638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904693 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 4]
def baseStart_904693 : Nat := 118140960795 + 904693 * 2 ^ 59
def prefixEnd_904693 : Nat := 4983230072969 + 3 ^ 40 * 904693 * 2
def baseEnd_904693 : Nat := 412926536673896993935021

theorem tailTrace_904693 : CollatzResearch.WordTrace tailWord_904693 prefixEnd_904693 412926536673896993935021 := by
  unfold tailWord_904693
  simp only [CollatzResearch.WordTrace]
  refine ⟨32996864511459245108398733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21997909674306163405599155 32996864511459245108398733)
  ·
    refine ⟨12373824191797216915649525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32996864511459245108398733 12373824191797216915649525)
    ·
      refine ⟨1160046017980989085842143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12373824191797216915649525 1160046017980989085842143)
      ·
        refine ⟨1740069026971483628763215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160046017980989085842143 1740069026971483628763215)
        ·
          refine ⟨2610103540457225443144823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740069026971483628763215 2610103540457225443144823)
          ·
            refine ⟨3915155310685838164717235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610103540457225443144823 3915155310685838164717235)
            ·
              refine ⟨5872732966028757247075853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915155310685838164717235 5872732966028757247075853)
              ·
                refine ⟨2202274862260783967653445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5872732966028757247075853 2202274862260783967653445)
                ·
                  refine ⟨412926536673896993935021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202274862260783967653445 412926536673896993935021)
                  ·
                    rfl

theorem cell20_904693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_904693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904693 prefixEnd_904693 := by exact prefixLift 904693
  have htrace : WordTrace (prefixWord ++ tailWord_904693) baseStart_904693 baseEnd_904693 := by
    simpa [prefixWord, tailWord_904693, baseEnd_904693] using wordTrace_append hprefix tailTrace_904693
  have hstable : (prefixWord ++ tailWord_904693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904693).length < 2 ^ (prefixWord ++ tailWord_904693).sum := by decide
  have hdescent : baseEnd_904693 < baseStart_904693 := by decide
  rcases family_descends (prefixWord ++ tailWord_904693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904714 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_904714 : Nat := 118140960795 + 904714 * 2 ^ 59
def prefixEnd_904714 : Nat := 4983230072969 + 3 ^ 40 * 904714 * 2
def baseEnd_904714 : Nat := 412936121646114254234935

theorem tailTrace_904714 : CollatzResearch.WordTrace tailWord_904714 prefixEnd_904714 412936121646114254234935 := by
  unfold tailWord_904714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8249407611095791423728299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21998420296255443796608797 8249407611095791423728299)
  ·
    refine ⟨12374111416643687135592449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8249407611095791423728299 12374111416643687135592449)
    ·
      refine ⟨9280583562482765351694337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12374111416643687135592449 9280583562482765351694337)
      ·
        refine ⟨6960437671862074013770753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9280583562482765351694337 6960437671862074013770753)
        ·
          refine ⟨5220328253896555510328065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6960437671862074013770753 5220328253896555510328065)
          ·
            refine ⟨3915246190422416632746049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5220328253896555510328065 3915246190422416632746049)
            ·
              refine ⟨2936434642816812474559537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3915246190422416632746049 2936434642816812474559537)
              ·
                refine ⟨2202325982112609355919653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2936434642816812474559537 2202325982112609355919653)
                ·
                  refine ⟨412936121646114254234935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202325982112609355919653 412936121646114254234935)
                  ·
                    rfl

theorem cell20_904714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_904714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904714 prefixEnd_904714 := by exact prefixLift 904714
  have htrace : WordTrace (prefixWord ++ tailWord_904714) baseStart_904714 baseEnd_904714 := by
    simpa [prefixWord, tailWord_904714, baseEnd_904714] using wordTrace_append hprefix tailTrace_904714
  have hstable : (prefixWord ++ tailWord_904714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904714).length < 2 ^ (prefixWord ++ tailWord_904714).sum := by decide
  have hdescent : baseEnd_904714 < baseStart_904714 := by decide
  rcases family_descends (prefixWord ++ tailWord_904714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904735 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_904735 : Nat := 118140960795 + 904735 * 2 ^ 59
def prefixEnd_904735 : Nat := 4983230072969 + 3 ^ 40 * 904735 * 2
def baseEnd_904735 : Nat := 412945706618331514534849

theorem tailTrace_904735 : CollatzResearch.WordTrace tailWord_904735 prefixEnd_904735 412945706618331514534849 := by
  unfold tailWord_904735
  simp only [CollatzResearch.WordTrace]
  refine ⟨32998396377307086281427659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21998930918204724187618439 32998396377307086281427659)
  ·
    refine ⟨49497594565960629422141489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32998396377307086281427659 49497594565960629422141489)
    ·
      refine ⟨37123195924470472066606117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49497594565960629422141489 37123195924470472066606117)
      ·
        refine ⟨6960599235838213512488647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37123195924470472066606117 6960599235838213512488647)
        ·
          refine ⟨10440898853757320268732971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6960599235838213512488647 10440898853757320268732971)
          ·
            refine ⟨15661348280635980403099457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10440898853757320268732971 15661348280635980403099457)
            ·
              refine ⟨11746011210476985302324593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15661348280635980403099457 11746011210476985302324593)
              ·
                refine ⟨8809508407857738976743445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11746011210476985302324593 8809508407857738976743445)
                ·
                  refine ⟨412945706618331514534849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8809508407857738976743445 412945706618331514534849)
                  ·
                    rfl

theorem cell20_904735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_904735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904735 prefixEnd_904735 := by exact prefixLift 904735
  have htrace : WordTrace (prefixWord ++ tailWord_904735) baseStart_904735 baseEnd_904735 := by
    simpa [prefixWord, tailWord_904735, baseEnd_904735] using wordTrace_append hprefix tailTrace_904735
  have hstable : (prefixWord ++ tailWord_904735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904735).length < 2 ^ (prefixWord ++ tailWord_904735).sum := by decide
  have hdescent : baseEnd_904735 < baseStart_904735 := by decide
  rcases family_descends (prefixWord ++ tailWord_904735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904758 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_904758 : Nat := 118140960795 + 904758 * 2 ^ 59
def prefixEnd_904758 : Nat := 4983230072969 + 3 ^ 40 * 904758 * 2
def baseEnd_904758 : Nat := 412956204445045656768089

theorem tailTrace_904758 : CollatzResearch.WordTrace tailWord_904758 prefixEnd_904758 412956204445045656768089 := by
  unfold tailWord_904758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2062452203513985075594683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21999490170815840806343285 2062452203513985075594683)
  ·
    refine ⟨3093678305270977613392025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2062452203513985075594683 3093678305270977613392025)
    ·
      refine ⟨2320258728953233210044019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3093678305270977613392025 2320258728953233210044019)
      ·
        refine ⟨3480388093429849815066029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320258728953233210044019 3480388093429849815066029)
        ·
          refine ⟨1305145535036193680649761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3480388093429849815066029 1305145535036193680649761)
          ·
            refine ⟨978859151277145260487321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1305145535036193680649761 978859151277145260487321)
            ·
              refine ⟨734144363457858945365491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978859151277145260487321 734144363457858945365491)
              ·
                refine ⟨1101216545186788418048237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734144363457858945365491 1101216545186788418048237)
                ·
                  refine ⟨412956204445045656768089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101216545186788418048237 412956204445045656768089)
                  ·
                    rfl

theorem cell20_904758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_904758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904758 prefixEnd_904758 := by exact prefixLift 904758
  have htrace : WordTrace (prefixWord ++ tailWord_904758) baseStart_904758 baseEnd_904758 := by
    simpa [prefixWord, tailWord_904758, baseEnd_904758] using wordTrace_append hprefix tailTrace_904758
  have hstable : (prefixWord ++ tailWord_904758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904758).length < 2 ^ (prefixWord ++ tailWord_904758).sum := by decide
  have hdescent : baseEnd_904758 < baseStart_904758 := by decide
  rcases family_descends (prefixWord ++ tailWord_904758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904759 : List Nat := [1, 1, 3, 1, 2, 5, 2, 5]
def baseStart_904759 : Nat := 118140960795 + 904759 * 2 ^ 59
def prefixEnd_904759 : Nat := 4983230072969 + 3 ^ 40 * 904759 * 2
def baseEnd_904759 : Nat := 137652220290764699244917

theorem tailTrace_904759 : CollatzResearch.WordTrace tailWord_904759 prefixEnd_904759 137652220290764699244917 := by
  unfold tailWord_904759
  simp only [CollatzResearch.WordTrace]
  refine ⟨32999271729220138380301331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21999514486146758920200887 32999271729220138380301331)
  ·
    refine ⟨49498907593830207570451997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32999271729220138380301331 49498907593830207570451997)
    ·
      refine ⟨18562090347686327838919499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49498907593830207570451997 18562090347686327838919499)
      ·
        refine ⟨27843135521529491758379249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18562090347686327838919499 27843135521529491758379249)
        ·
          refine ⟨20882351641147118818784437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27843135521529491758379249 20882351641147118818784437)
          ·
            refine ⟨1957720466357542389261041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20882351641147118818784437 1957720466357542389261041)
            ·
              refine ⟨1468290349768156791945781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957720466357542389261041 1468290349768156791945781)
              ·
                refine ⟨137652220290764699244917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1468290349768156791945781 137652220290764699244917)
                ·
                  rfl

theorem cell20_904759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_904759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904759 prefixEnd_904759 := by exact prefixLift 904759
  have htrace : WordTrace (prefixWord ++ tailWord_904759) baseStart_904759 baseEnd_904759 := by
    simpa [prefixWord, tailWord_904759, baseEnd_904759] using wordTrace_append hprefix tailTrace_904759
  have hstable : (prefixWord ++ tailWord_904759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904759).length < 2 ^ (prefixWord ++ tailWord_904759).sum := by decide
  have hdescent : baseEnd_904759 < baseStart_904759 := by decide
  rcases family_descends (prefixWord ++ tailWord_904759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904773 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_904773 : Nat := 118140960795 + 904773 * 2 ^ 59
def prefixEnd_904773 : Nat := 4983230072969 + 3 ^ 40 * 904773 * 2
def baseEnd_904773 : Nat := 412963050853772271268027

theorem tailTrace_904773 : CollatzResearch.WordTrace tailWord_904773 prefixEnd_904773 412963050853772271268027 := by
  unfold tailWord_904773
  simp only [CollatzResearch.WordTrace]
  refine ⟨32999782351169418771310973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21999854900779612514207315 32999782351169418771310973)
  ·
    refine ⟨12374918381688532039241615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32999782351169418771310973 12374918381688532039241615)
    ·
      refine ⟨18562377572532798058862423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12374918381688532039241615 18562377572532798058862423)
      ·
        refine ⟨27843566358799197088293635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18562377572532798058862423 27843566358799197088293635)
        ·
          refine ⟨41765349538198795632440453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27843566358799197088293635 41765349538198795632440453)
          ·
            refine ⟨7831003038412274181082585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41765349538198795632440453 7831003038412274181082585)
            ·
              refine ⟨5873252278809205635811939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7831003038412274181082585 5873252278809205635811939)
              ·
                refine ⟨8809878418213808453717909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873252278809205635811939 8809878418213808453717909)
                ·
                  refine ⟨412963050853772271268027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8809878418213808453717909 412963050853772271268027)
                  ·
                    rfl

theorem cell20_904773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_904773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904773 prefixEnd_904773 := by exact prefixLift 904773
  have htrace : WordTrace (prefixWord ++ tailWord_904773) baseStart_904773 baseEnd_904773 := by
    simpa [prefixWord, tailWord_904773, baseEnd_904773] using wordTrace_append hprefix tailTrace_904773
  have hstable : (prefixWord ++ tailWord_904773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904773).length < 2 ^ (prefixWord ++ tailWord_904773).sum := by decide
  have hdescent : baseEnd_904773 < baseStart_904773 := by decide
  rcases family_descends (prefixWord ++ tailWord_904773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904852 : List Nat := [2, 4, 2, 2, 2, 1, 7]
def baseStart_904852 : Nat := 118140960795 + 904852 * 2 ^ 59
def prefixEnd_904852 : Nat := 4983230072969 + 3 ^ 40 * 904852 * 2
def baseEnd_904852 : Nat := 45888789845155456403819

theorem tailTrace_904852 : CollatzResearch.WordTrace tailWord_904852 prefixEnd_904852 45888789845155456403819 := by
  unfold tailWord_904852
  simp only [CollatzResearch.WordTrace]
  refine ⟨16501331858941607631718405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22001775811922143508957873 16501331858941607631718405)
  ·
    refine ⟨3093999723551551430947201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16501331858941607631718405 3093999723551551430947201)
    ·
      refine ⟨2320499792663663573210401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3093999723551551430947201 2320499792663663573210401)
      ·
        refine ⟨1740374844497747679907801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2320499792663663573210401 1740374844497747679907801)
        ·
          refine ⟨1305281133373310759930851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1740374844497747679907801 1305281133373310759930851)
          ·
            refine ⟨1957921700059966139896277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305281133373310759930851 1957921700059966139896277)
            ·
              refine ⟨45888789845155456403819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1957921700059966139896277 45888789845155456403819)
              ·
                rfl

theorem cell20_904852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 7].length) (baseStart_904852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904852 prefixEnd_904852 := by exact prefixLift 904852
  have htrace : WordTrace (prefixWord ++ tailWord_904852) baseStart_904852 baseEnd_904852 := by
    simpa [prefixWord, tailWord_904852, baseEnd_904852] using wordTrace_append hprefix tailTrace_904852
  have hstable : (prefixWord ++ tailWord_904852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904852).length < 2 ^ (prefixWord ++ tailWord_904852).sum := by decide
  have hdescent : baseEnd_904852 < baseStart_904852 := by decide
  rcases family_descends (prefixWord ++ tailWord_904852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904862 : List Nat := [4, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_904862 : Nat := 118140960795 + 904862 * 2 ^ 59
def prefixEnd_904862 : Nat := 4983230072969 + 3 ^ 40 * 904862 * 2
def baseEnd_904862 : Nat := 413003672878883517300997

theorem tailTrace_904862 : CollatzResearch.WordTrace tailWord_904862 prefixEnd_904862 413003672878883517300997 := by
  unfold tailWord_904862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4125378555980873371412605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22002018965231324647533893 4125378555980873371412605)
  ·
    refine ⟨1547016958492827514279727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4125378555980873371412605 1547016958492827514279727)
    ·
      refine ⟨2320525437739241271419591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1547016958492827514279727 2320525437739241271419591)
      ·
        refine ⟨3480788156608861907129387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320525437739241271419591 3480788156608861907129387)
        ·
          refine ⟨5221182234913292860694081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480788156608861907129387 5221182234913292860694081)
          ·
            refine ⟨3915886676184969645520561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5221182234913292860694081 3915886676184969645520561)
            ·
              refine ⟨2936915007138727234140421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3915886676184969645520561 2936915007138727234140421)
              ·
                refine ⟨550671563838511356401329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2936915007138727234140421 550671563838511356401329)
                ·
                  refine ⟨413003672878883517300997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550671563838511356401329 413003672878883517300997)
                  ·
                    rfl

theorem cell20_904862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_904862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904862 prefixEnd_904862 := by exact prefixLift 904862
  have htrace : WordTrace (prefixWord ++ tailWord_904862) baseStart_904862 baseEnd_904862 := by
    simpa [prefixWord, tailWord_904862, baseEnd_904862] using wordTrace_append hprefix tailTrace_904862
  have hstable : (prefixWord ++ tailWord_904862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904862).length < 2 ^ (prefixWord ++ tailWord_904862).sum := by decide
  have hdescent : baseEnd_904862 < baseStart_904862 := by decide
  rcases family_descends (prefixWord ++ tailWord_904862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904880 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 3]
def baseStart_904880 : Nat := 118140960795 + 904880 * 2 ^ 59
def prefixEnd_904880 : Nat := 4983230072969 + 3 ^ 40 * 904880 * 2
def baseEnd_904880 : Nat := 413011888569355454700923

theorem tailTrace_904880 : CollatzResearch.WordTrace tailWord_904880 prefixEnd_904880 413011888569355454700923 := by
  unfold tailWord_904880
  simp only [CollatzResearch.WordTrace]
  refine ⟨16501842480890888022728047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22002456641187850696970729 16501842480890888022728047)
  ·
    refine ⟨24752763721336332034092071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16501842480890888022728047 24752763721336332034092071)
    ·
      refine ⟨37129145582004498051138107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24752763721336332034092071 37129145582004498051138107)
      ·
        refine ⟨55693718373006747076707161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37129145582004498051138107 55693718373006747076707161)
        ·
          refine ⟨41770288779755060307530371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55693718373006747076707161 41770288779755060307530371)
          ·
            refine ⟨62655433169632590461295557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41770288779755060307530371 62655433169632590461295557)
            ·
              refine ⟨11747893719306110711492917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62655433169632590461295557 11747893719306110711492917)
              ·
                refine ⟨1101365036184947879202461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11747893719306110711492917 1101365036184947879202461)
                ·
                  refine ⟨413011888569355454700923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101365036184947879202461 413011888569355454700923)
                  ·
                    rfl

theorem cell20_904880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_904880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904880 prefixEnd_904880 := by exact prefixLift 904880
  have htrace : WordTrace (prefixWord ++ tailWord_904880) baseStart_904880 baseEnd_904880 := by
    simpa [prefixWord, tailWord_904880, baseEnd_904880] using wordTrace_append hprefix tailTrace_904880
  have hstable : (prefixWord ++ tailWord_904880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904880).length < 2 ^ (prefixWord ++ tailWord_904880).sum := by decide
  have hdescent : baseEnd_904880 < baseStart_904880 := by decide
  rcases family_descends (prefixWord ++ tailWord_904880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904886 : List Nat := [5, 1, 3, 1, 1, 3, 2, 4]
def baseStart_904886 : Nat := 118140960795 + 904886 * 2 ^ 59
def prefixEnd_904886 : Nat := 4983230072969 + 3 ^ 40 * 904886 * 2
def baseEnd_904886 : Nat := 137671542377615366833633

theorem tailTrace_904886 : CollatzResearch.WordTrace tailWord_904886 prefixEnd_904886 137671542377615366833633 := by
  unfold tailWord_904886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2062743987485002441885907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22002602533173359380116341 2062743987485002441885907)
  ·
    refine ⟨3094115981227503662828861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2062743987485002441885907 3094115981227503662828861)
    ·
      refine ⟨1160293492960313873560823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3094115981227503662828861 1160293492960313873560823)
      ·
        refine ⟨1740440239440470810341235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160293492960313873560823 1740440239440470810341235)
        ·
          refine ⟨2610660359160706215511853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740440239440470810341235 2610660359160706215511853)
          ·
            refine ⟨978997634685264830816945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2610660359160706215511853 978997634685264830816945)
            ·
              refine ⟨734248226013948623112709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978997634685264830816945 734248226013948623112709)
              ·
                refine ⟨137671542377615366833633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 734248226013948623112709 137671542377615366833633)
                ·
                  rfl

theorem cell20_904886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_904886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904886 prefixEnd_904886 := by exact prefixLift 904886
  have htrace : WordTrace (prefixWord ++ tailWord_904886) baseStart_904886 baseEnd_904886 := by
    simpa [prefixWord, tailWord_904886, baseEnd_904886] using wordTrace_append hprefix tailTrace_904886
  have hstable : (prefixWord ++ tailWord_904886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904886).length < 2 ^ (prefixWord ++ tailWord_904886).sum := by decide
  have hdescent : baseEnd_904886 < baseStart_904886 := by decide
  rcases family_descends (prefixWord ++ tailWord_904886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904890 : List Nat := [3, 1, 1, 1, 2, 6, 2, 4]
def baseStart_904890 : Nat := 118140960795 + 904890 * 2 ^ 59
def prefixEnd_904890 : Nat := 4983230072969 + 3 ^ 40 * 904890 * 2
def baseEnd_904890 : Nat := 137672150947279954789183

theorem tailTrace_904890 : CollatzResearch.WordTrace tailWord_904890 prefixEnd_904890 137672150947279954789183 := by
  unfold tailWord_904890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251012422936386938330031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22002699794497031835546749 8251012422936386938330031)
  ·
    refine ⟨12376518634404580407495047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8251012422936386938330031 12376518634404580407495047)
    ·
      refine ⟨18564777951606870611242571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12376518634404580407495047 18564777951606870611242571)
      ·
        refine ⟨27847166927410305916863857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18564777951606870611242571 27847166927410305916863857)
        ·
          refine ⟨20885375195557729437647893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27847166927410305916863857 20885375195557729437647893)
          ·
            refine ⟨979001962291768567389745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20885375195557729437647893 979001962291768567389745)
            ·
              refine ⟨734251471718826425542309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979001962291768567389745 734251471718826425542309)
              ·
                refine ⟨137672150947279954789183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 734251471718826425542309 137672150947279954789183)
                ·
                  rfl

theorem cell20_904890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_904890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904890 prefixEnd_904890 := by exact prefixLift 904890
  have htrace : WordTrace (prefixWord ++ tailWord_904890) baseStart_904890 baseEnd_904890 := by
    simpa [prefixWord, tailWord_904890, baseEnd_904890] using wordTrace_append hprefix tailTrace_904890
  have hstable : (prefixWord ++ tailWord_904890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904890).length < 2 ^ (prefixWord ++ tailWord_904890).sum := by decide
  have hdescent : baseEnd_904890 < baseStart_904890 := by decide
  rcases family_descends (prefixWord ++ tailWord_904890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904931 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 3]
def baseStart_904931 : Nat := 118140960795 + 904931 * 2 ^ 59
def prefixEnd_904931 : Nat := 4983230072969 + 3 ^ 40 * 904931 * 2
def baseEnd_904931 : Nat := 413035166359025944000715

theorem tailTrace_904931 : CollatzResearch.WordTrace tailWord_904931 prefixEnd_904931 413035166359025944000715 := by
  unfold tailWord_904931
  simp only [CollatzResearch.WordTrace]
  refine ⟨33005545084597011755562647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22003696723064674503708431 33005545084597011755562647)
  ·
    refine ⟨49508317626895517633343971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33005545084597011755562647 49508317626895517633343971)
    ·
      refine ⟨74262476440343276450015957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49508317626895517633343971 74262476440343276450015957)
      ·
        refine ⟨1740526791570545541797249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 74262476440343276450015957 1740526791570545541797249)
        ·
          refine ⟨1305395093677909156347937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1740526791570545541797249 1305395093677909156347937)
          ·
            refine ⟨979046320258431867260953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1305395093677909156347937 979046320258431867260953)
            ·
              refine ⟨734284740193823900445715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979046320258431867260953 734284740193823900445715)
              ·
                refine ⟨1101427110290735850668573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734284740193823900445715 1101427110290735850668573)
                ·
                  refine ⟨413035166359025944000715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101427110290735850668573 413035166359025944000715)
                  ·
                    rfl

theorem cell20_904931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 3].length) (baseStart_904931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904931 prefixEnd_904931 := by exact prefixLift 904931
  have htrace : WordTrace (prefixWord ++ tailWord_904931) baseStart_904931 baseEnd_904931 := by
    simpa [prefixWord, tailWord_904931, baseEnd_904931] using wordTrace_append hprefix tailTrace_904931
  have hstable : (prefixWord ++ tailWord_904931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904931).length < 2 ^ (prefixWord ++ tailWord_904931).sum := by decide
  have hdescent : baseEnd_904931 < baseStart_904931 := by decide
  rcases family_descends (prefixWord ++ tailWord_904931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904970 : List Nat := [3, 1, 2, 2, 1, 11]
def baseStart_904970 : Nat := 118140960795 + 904970 * 2 ^ 59
def prefixEnd_904970 : Nat := 4983230072969 + 3 ^ 40 * 904970 * 2
def baseEnd_904970 : Nat := 15298258037841301544465

theorem tailTrace_904970 : CollatzResearch.WordTrace tailWord_904970 prefixEnd_904970 15298258037841301544465 := by
  unfold tailWord_904970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251741882863930354058091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22004645020970480944154909 8251741882863930354058091)
  ·
    refine ⟨12377612824295895531087137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8251741882863930354058091 12377612824295895531087137)
    ·
      refine ⟨9283209618221921648315353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12377612824295895531087137 9283209618221921648315353)
      ·
        refine ⟨6962407213666441236236515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9283209618221921648315353 6962407213666441236236515)
        ·
          refine ⟨10443610820499661854354773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962407213666441236236515 10443610820499661854354773)
          ·
            refine ⟨15298258037841301544465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10443610820499661854354773 15298258037841301544465)
            ·
              rfl

theorem cell20_904970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 11].length) (baseStart_904970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_904970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_904970 prefixEnd_904970 := by exact prefixLift 904970
  have htrace : WordTrace (prefixWord ++ tailWord_904970) baseStart_904970 baseEnd_904970 := by
    simpa [prefixWord, tailWord_904970, baseEnd_904970] using wordTrace_append hprefix tailTrace_904970
  have hstable : (prefixWord ++ tailWord_904970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904970).length < 2 ^ (prefixWord ++ tailWord_904970).sum := by decide
  have hdescent : baseEnd_904970 < baseStart_904970 := by decide
  rcases family_descends (prefixWord ++ tailWord_904970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905014 : List Nat := [5, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_905014 : Nat := 118140960795 + 905014 * 2 ^ 59
def prefixEnd_905014 : Nat := 4983230072969 + 3 ^ 40 * 905014 * 2
def baseEnd_905014 : Nat := 413073049820646544233709

theorem tailTrace_905014 : CollatzResearch.WordTrace tailWord_905014 prefixEnd_905014 413073049820646544233709 := by
  unfold tailWord_905014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063035771456019808177131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22005714895530877953889397 2063035771456019808177131)
  ·
    refine ⟨3094553657184029712265697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2063035771456019808177131 3094553657184029712265697)
    ·
      refine ⟨2320915242888022284199273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3094553657184029712265697 2320915242888022284199273)
      ·
        refine ⟨1740686432166016713149455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2320915242888022284199273 1740686432166016713149455)
        ·
          refine ⟨2611029648249025069724183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740686432166016713149455 2611029648249025069724183)
          ·
            refine ⟨3916544472373537604586275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611029648249025069724183 3916544472373537604586275)
            ·
              refine ⟨5874816708560306406879413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916544472373537604586275 5874816708560306406879413)
              ·
                refine ⟨550764066427528725644945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5874816708560306406879413 550764066427528725644945)
                ·
                  refine ⟨413073049820646544233709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550764066427528725644945 413073049820646544233709)
                  ·
                    rfl

theorem cell20_905014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_905014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905014 prefixEnd_905014 := by exact prefixLift 905014
  have htrace : WordTrace (prefixWord ++ tailWord_905014) baseStart_905014 baseEnd_905014 := by
    simpa [prefixWord, tailWord_905014, baseEnd_905014] using wordTrace_append hprefix tailTrace_905014
  have hstable : (prefixWord ++ tailWord_905014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905014).length < 2 ^ (prefixWord ++ tailWord_905014).sum := by decide
  have hdescent : baseEnd_905014 < baseStart_905014 := by decide
  rcases family_descends (prefixWord ++ tailWord_905014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905032 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_905032 : Nat := 118140960795 + 905032 * 2 ^ 59
def prefixEnd_905032 : Nat := 4983230072969 + 3 ^ 40 * 905032 * 2
def baseEnd_905032 : Nat := 413081265511118481633635

theorem tailTrace_905032 : CollatzResearch.WordTrace tailWord_905032 prefixEnd_905032 413081265511118481633635 := by
  unfold tailWord_905032
  simp only [CollatzResearch.WordTrace]
  refine ⟨16504614428615553002494675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22006152571487404003326233 16504614428615553002494675)
  ·
    refine ⟨24756921642923329503742013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16504614428615553002494675 24756921642923329503742013)
    ·
      refine ⟨9283845616096248563903255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24756921642923329503742013 9283845616096248563903255)
      ·
        refine ⟨13925768424144372845854883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9283845616096248563903255 13925768424144372845854883)
        ·
          refine ⟨20888652636216559268782325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13925768424144372845854883 20888652636216559268782325)
          ·
            refine ⟨1958311184645302431448343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20888652636216559268782325 1958311184645302431448343)
            ·
              refine ⟨2937466776967953647172515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958311184645302431448343 2937466776967953647172515)
              ·
                refine ⟨4406200165451930470758773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937466776967953647172515 4406200165451930470758773)
                ·
                  refine ⟨413081265511118481633635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406200165451930470758773 413081265511118481633635)
                  ·
                    rfl

theorem cell20_905032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_905032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905032 prefixEnd_905032 := by exact prefixLift 905032
  have htrace : WordTrace (prefixWord ++ tailWord_905032) baseStart_905032 baseEnd_905032 := by
    simpa [prefixWord, tailWord_905032, baseEnd_905032] using wordTrace_append hprefix tailTrace_905032
  have hstable : (prefixWord ++ tailWord_905032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905032).length < 2 ^ (prefixWord ++ tailWord_905032).sum := by decide
  have hdescent : baseEnd_905032 < baseStart_905032 := by decide
  rcases family_descends (prefixWord ++ tailWord_905032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905049 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 3]
def baseStart_905049 : Nat := 118140960795 + 905049 * 2 ^ 59
def prefixEnd_905049 : Nat := 4983230072969 + 3 ^ 40 * 905049 * 2
def baseEnd_905049 : Nat := 413089024774341978066899

theorem tailTrace_905049 : CollatzResearch.WordTrace tailWord_905049 prefixEnd_905049 413089024774341978066899 := by
  unfold tailWord_905049
  simp only [CollatzResearch.WordTrace]
  refine ⟨33009848898169517908358201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22006565932113011938905467 33009848898169517908358201)
  ·
    refine ⟨24757386673627138431268651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33009848898169517908358201 24757386673627138431268651)
    ·
      refine ⟨37136080010440707646902977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24757386673627138431268651 37136080010440707646902977)
      ·
        refine ⟨27852060007830530735177233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37136080010440707646902977 27852060007830530735177233)
        ·
          refine ⟨20889045005872898051382925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27852060007830530735177233 20889045005872898051382925)
          ·
            refine ⟨7833391877202336769268597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20889045005872898051382925 7833391877202336769268597)
            ·
              refine ⟨734380488487719072118931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7833391877202336769268597 734380488487719072118931)
              ·
                refine ⟨1101570732731578608178397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734380488487719072118931 1101570732731578608178397)
                ·
                  refine ⟨413089024774341978066899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101570732731578608178397 413089024774341978066899)
                  ·
                    rfl

theorem cell20_905049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_905049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905049 prefixEnd_905049 := by exact prefixLift 905049
  have htrace : WordTrace (prefixWord ++ tailWord_905049) baseStart_905049 baseEnd_905049 := by
    simpa [prefixWord, tailWord_905049, baseEnd_905049] using wordTrace_append hprefix tailTrace_905049
  have hstable : (prefixWord ++ tailWord_905049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905049).length < 2 ^ (prefixWord ++ tailWord_905049).sum := by decide
  have hdescent : baseEnd_905049 < baseStart_905049 := by decide
  rcases family_descends (prefixWord ++ tailWord_905049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905059 : List Nat := [1, 1, 1, 5, 5, 1, 2, 4]
def baseStart_905059 : Nat := 118140960795 + 905059 * 2 ^ 59
def prefixEnd_905059 : Nat := 4983230072969 + 3 ^ 40 * 905059 * 2
def baseEnd_905059 : Nat := 137697863015608795911175

theorem tailTrace_905059 : CollatzResearch.WordTrace tailWord_905059 prefixEnd_905059 137697863015608795911175 := by
  unfold tailWord_905059
  simp only [CollatzResearch.WordTrace]
  refine ⟨33010213628133289616222231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22006809085422193077481487 33010213628133289616222231)
  ·
    refine ⟨49515320442199934424333347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33010213628133289616222231 49515320442199934424333347)
    ·
      refine ⟨74272980663299901636500021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49515320442199934424333347 74272980663299901636500021)
      ·
        refine ⟨6963091937184365778421877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74272980663299901636500021 6963091937184365778421877)
        ·
          refine ⟨652789869111034291727051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6963091937184365778421877 652789869111034291727051)
          ·
            refine ⟨979184803666551437590577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652789869111034291727051 979184803666551437590577)
            ·
              refine ⟨734388602749913578192933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979184803666551437590577 734388602749913578192933)
              ·
                refine ⟨137697863015608795911175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 734388602749913578192933 137697863015608795911175)
                ·
                  rfl

theorem cell20_905059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 4].length) (baseStart_905059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905059 prefixEnd_905059 := by exact prefixLift 905059
  have htrace : WordTrace (prefixWord ++ tailWord_905059) baseStart_905059 baseEnd_905059 := by
    simpa [prefixWord, tailWord_905059, baseEnd_905059] using wordTrace_append hprefix tailTrace_905059
  have hstable : (prefixWord ++ tailWord_905059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905059).length < 2 ^ (prefixWord ++ tailWord_905059).sum := by decide
  have hdescent : baseEnd_905059 < baseStart_905059 := by decide
  rcases family_descends (prefixWord ++ tailWord_905059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905129 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_905129 : Nat := 118140960795 + 905129 * 2 ^ 59
def prefixEnd_905129 : Nat := 4983230072969 + 3 ^ 40 * 905129 * 2
def baseEnd_905129 : Nat := 413125538954217255399905

theorem tailTrace_905129 : CollatzResearch.WordTrace tailWord_905129 prefixEnd_905129 413125538954217255399905 := by
  unfold tailWord_905129
  simp only [CollatzResearch.WordTrace]
  refine ⟨33012766737879691571270441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22008511158586461047513627 33012766737879691571270441)
  ·
    refine ⟨24759575053409768678452831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33012766737879691571270441 24759575053409768678452831)
    ·
      refine ⟨37139362580114653017679247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24759575053409768678452831 37139362580114653017679247)
      ·
        refine ⟨55709043870171979526518871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37139362580114653017679247 55709043870171979526518871)
        ·
          refine ⟨83563565805257969289778307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55709043870171979526518871 83563565805257969289778307)
          ·
            refine ⟨125345348707886953934667461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83563565805257969289778307 125345348707886953934667461)
            ·
              refine ⟨23502252882728803862750149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125345348707886953934667461 23502252882728803862750149)
              ·
                refine ⟨4406672415511650724265653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23502252882728803862750149 4406672415511650724265653)
                ·
                  refine ⟨413125538954217255399905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406672415511650724265653 413125538954217255399905)
                  ·
                    rfl

theorem cell20_905129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_905129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905129 prefixEnd_905129 := by exact prefixLift 905129
  have htrace : WordTrace (prefixWord ++ tailWord_905129) baseStart_905129 baseEnd_905129 := by
    simpa [prefixWord, tailWord_905129, baseEnd_905129] using wordTrace_append hprefix tailTrace_905129
  have hstable : (prefixWord ++ tailWord_905129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905129).length < 2 ^ (prefixWord ++ tailWord_905129).sum := by decide
  have hdescent : baseEnd_905129 < baseStart_905129 := by decide
  rcases family_descends (prefixWord ++ tailWord_905129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905149 : List Nat := [1, 4, 1, 2, 3, 2, 1, 4, 2]
def baseStart_905149 : Nat := 118140960795 + 905149 * 2 ^ 59
def prefixEnd_905149 : Nat := 4983230072969 + 3 ^ 40 * 905149 * 2
def baseEnd_905149 : Nat := 413134667499186074733157

theorem tailTrace_905149 : CollatzResearch.WordTrace tailWord_905149 prefixEnd_905149 413134667499186074733157 := by
  unfold tailWord_905149
  simp only [CollatzResearch.WordTrace]
  refine ⟨33013496197807234986998501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22008997465204823324665667 33013496197807234986998501)
  ·
    refine ⟨6190030537088856560062219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33013496197807234986998501 6190030537088856560062219)
    ·
      refine ⟨9285045805633284840093329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6190030537088856560062219 9285045805633284840093329)
      ·
        refine ⟨6963784354224963630069997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9285045805633284840093329 6963784354224963630069997)
        ·
          refine ⟨2611419132834361361276249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6963784354224963630069997 2611419132834361361276249)
          ·
            refine ⟨1958564349625771020957187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2611419132834361361276249 1958564349625771020957187)
            ·
              refine ⟨2937846524438656531435781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958564349625771020957187 2937846524438656531435781)
              ·
                refine ⟨550846223332248099644209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2937846524438656531435781 550846223332248099644209)
                ·
                  refine ⟨413134667499186074733157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550846223332248099644209 413134667499186074733157)
                  ·
                    rfl

theorem cell20_905149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_905149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905149 prefixEnd_905149 := by exact prefixLift 905149
  have htrace : WordTrace (prefixWord ++ tailWord_905149) baseStart_905149 baseEnd_905149 := by
    simpa [prefixWord, tailWord_905149, baseEnd_905149] using wordTrace_append hprefix tailTrace_905149
  have hstable : (prefixWord ++ tailWord_905149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905149).length < 2 ^ (prefixWord ++ tailWord_905149).sum := by decide
  have hdescent : baseEnd_905149 < baseStart_905149 := by decide
  rcases family_descends (prefixWord ++ tailWord_905149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905187 : List Nat := [1, 1, 1, 6, 1, 3, 2, 3, 2]
def baseStart_905187 : Nat := 118140960795 + 905187 * 2 ^ 59
def prefixEnd_905187 : Nat := 4983230072969 + 3 ^ 40 * 905187 * 2
def baseEnd_905187 : Nat := 413152011734626831466335

theorem tailTrace_905187 : CollatzResearch.WordTrace tailWord_905187 prefixEnd_905187 413152011734626831466335 := by
  unfold tailWord_905187
  simp only [CollatzResearch.WordTrace]
  refine ⟨33014882171669567476881815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22009921447779711651254543 33014882171669567476881815)
  ·
    refine ⟨49522323257504351215322723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33014882171669567476881815 49522323257504351215322723)
    ·
      refine ⟨74283484886256526822984085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49522323257504351215322723 74283484886256526822984085)
      ·
        refine ⟨3482038354043274694827379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74283484886256526822984085 3482038354043274694827379)
        ·
          refine ⟨5223057531064912042241069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3482038354043274694827379 5223057531064912042241069)
          ·
            refine ⟨1958646574149342015840401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5223057531064912042241069 1958646574149342015840401)
            ·
              refine ⟨1468984930612006511880301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958646574149342015840401 1468984930612006511880301)
              ·
                refine ⟨550869348979502441955113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1468984930612006511880301 550869348979502441955113)
                ·
                  refine ⟨413152011734626831466335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550869348979502441955113 413152011734626831466335)
                  ·
                    rfl

theorem cell20_905187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 2].length) (baseStart_905187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905187 prefixEnd_905187 := by exact prefixLift 905187
  have htrace : WordTrace (prefixWord ++ tailWord_905187) baseStart_905187 baseEnd_905187 := by
    simpa [prefixWord, tailWord_905187, baseEnd_905187] using wordTrace_append hprefix tailTrace_905187
  have hstable : (prefixWord ++ tailWord_905187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905187).length < 2 ^ (prefixWord ++ tailWord_905187).sum := by decide
  have hdescent : baseEnd_905187 < baseStart_905187 := by decide
  rcases family_descends (prefixWord ++ tailWord_905187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905197 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 3]
def baseStart_905197 : Nat := 118140960795 + 905197 * 2 ^ 59
def prefixEnd_905197 : Nat := 4983230072969 + 3 ^ 40 * 905197 * 2
def baseEnd_905197 : Nat := 413156576007111241132961

theorem tailTrace_905197 : CollatzResearch.WordTrace tailWord_905197 prefixEnd_905197 413156576007111241132961 := by
  unfold tailWord_905197
  simp only [CollatzResearch.WordTrace]
  refine ⟨33015246901633339184745845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22010164601088892789830563 33015246901633339184745845)
  ·
    refine ⟨3095179397028125548569923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33015246901633339184745845 3095179397028125548569923)
    ·
      refine ⟨4642769095542188322854885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095179397028125548569923 4642769095542188322854885)
      ·
        refine ⟨870519205414160310535291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4642769095542188322854885 870519205414160310535291)
        ·
          refine ⟨1305778808121240465802937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870519205414160310535291 1305778808121240465802937)
          ·
            refine ⟨979334106090930349352203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1305778808121240465802937 979334106090930349352203)
            ·
              refine ⟨1469001159136395524028305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979334106090930349352203 1469001159136395524028305)
              ·
                refine ⟨1101750869352296643021229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469001159136395524028305 1101750869352296643021229)
                ·
                  refine ⟨413156576007111241132961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101750869352296643021229 413156576007111241132961)
                  ·
                    rfl

theorem cell20_905197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_905197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905197 prefixEnd_905197 := by exact prefixLift 905197
  have htrace : WordTrace (prefixWord ++ tailWord_905197) baseStart_905197 baseEnd_905197 := by
    simpa [prefixWord, tailWord_905197, baseEnd_905197] using wordTrace_append hprefix tailTrace_905197
  have hstable : (prefixWord ++ tailWord_905197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905197).length < 2 ^ (prefixWord ++ tailWord_905197).sum := by decide
  have hdescent : baseEnd_905197 < baseStart_905197 := by decide
  rcases family_descends (prefixWord ++ tailWord_905197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905208 : List Nat := [2, 1, 2, 1, 1, 3, 4, 4, 2]
def baseStart_905208 : Nat := 118140960795 + 905208 * 2 ^ 59
def prefixEnd_905208 : Nat := 4983230072969 + 3 ^ 40 * 905208 * 2
def baseEnd_905208 : Nat := 413161596706844091766249

theorem tailTrace_905208 : CollatzResearch.WordTrace tailWord_905208 prefixEnd_905208 413161596706844091766249 := by
  unfold tailWord_905208
  simp only [CollatzResearch.WordTrace]
  refine ⟨16507824052296744031698139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22010432069728992042264185 16507824052296744031698139)
  ·
    refine ⟨24761736078445116047547209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16507824052296744031698139 24761736078445116047547209)
    ·
      refine ⟨18571302058833837035660407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24761736078445116047547209 18571302058833837035660407)
      ·
        refine ⟨27856953088250755553490611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18571302058833837035660407 27856953088250755553490611)
        ·
          refine ⟨41785429632376133330235917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27856953088250755553490611 41785429632376133330235917)
          ·
            refine ⟨15669536112141049998838469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41785429632376133330235917 15669536112141049998838469)
            ·
              refine ⟨2938038021026446874782213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15669536112141049998838469 2938038021026446874782213)
              ·
                refine ⟨550882128942458789021665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2938038021026446874782213 550882128942458789021665)
                ·
                  refine ⟨413161596706844091766249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550882128942458789021665 413161596706844091766249)
                  ·
                    rfl

theorem cell20_905208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_905208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905208 prefixEnd_905208 := by exact prefixLift 905208
  have htrace : WordTrace (prefixWord ++ tailWord_905208) baseStart_905208 baseEnd_905208 := by
    simpa [prefixWord, tailWord_905208, baseEnd_905208] using wordTrace_append hprefix tailTrace_905208
  have hstable : (prefixWord ++ tailWord_905208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905208).length < 2 ^ (prefixWord ++ tailWord_905208).sum := by decide
  have hdescent : baseEnd_905208 < baseStart_905208 := by decide
  rcases family_descends (prefixWord ++ tailWord_905208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905267 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 4]
def baseStart_905267 : Nat := 118140960795 + 905267 * 2 ^ 59
def prefixEnd_905267 : Nat := 4983230072969 + 3 ^ 40 * 905267 * 2
def baseEnd_905267 : Nat := 413188525914502108799341

theorem tailTrace_905267 : CollatzResearch.WordTrace tailWord_905267 prefixEnd_905267 413188525914502108799341 := by
  unfold tailWord_905267
  simp only [CollatzResearch.WordTrace]
  refine ⟨33017800011379741139794055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22011866674253160759862703 33017800011379741139794055)
  ·
    refine ⟨49526700017069611709691083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33017800011379741139794055 49526700017069611709691083)
    ·
      refine ⟨74290050025604417564536625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49526700017069611709691083 74290050025604417564536625)
      ·
        refine ⟨55717537519203313173402469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74290050025604417564536625 55717537519203313173402469)
        ·
          refine ⟨10447038284850621220012963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55717537519203313173402469 10447038284850621220012963)
          ·
            refine ⟨15670557427275931830019445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10447038284850621220012963 15670557427275931830019445)
            ·
              refine ⟨1469114758807118609064323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15670557427275931830019445 1469114758807118609064323)
              ·
                refine ⟨2203672138210677913596485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469114758807118609064323 2203672138210677913596485)
                ·
                  refine ⟨413188525914502108799341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203672138210677913596485 413188525914502108799341)
                  ·
                    rfl

theorem cell20_905267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_905267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905267 prefixEnd_905267 := by exact prefixLift 905267
  have htrace : WordTrace (prefixWord ++ tailWord_905267) baseStart_905267 baseEnd_905267 := by
    simpa [prefixWord, tailWord_905267, baseEnd_905267] using wordTrace_append hprefix tailTrace_905267
  have hstable : (prefixWord ++ tailWord_905267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905267).length < 2 ^ (prefixWord ++ tailWord_905267).sum := by decide
  have hdescent : baseEnd_905267 < baseStart_905267 := by decide
  rcases family_descends (prefixWord ++ tailWord_905267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905273 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 3]
def baseStart_905273 : Nat := 118140960795 + 905273 * 2 ^ 59
def prefixEnd_905273 : Nat := 4983230072969 + 3 ^ 40 * 905273 * 2
def baseEnd_905273 : Nat := 413191264477992754599317

theorem tailTrace_905273 : CollatzResearch.WordTrace tailWord_905273 prefixEnd_905273 413191264477992754599317 := by
  unfold tailWord_905273
  simp only [CollatzResearch.WordTrace]
  refine ⟨33018018849358004164512473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22012012566238669443008315 33018018849358004164512473)
  ·
    refine ⟨24763514137018503123384355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33018018849358004164512473 24763514137018503123384355)
    ·
      refine ⟨37145271205527754685076533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24763514137018503123384355 37145271205527754685076533)
      ·
        refine ⟨3482369175518227001725925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37145271205527754685076533 3482369175518227001725925)
        ·
          refine ⟨652944220409667562823611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3482369175518227001725925 652944220409667562823611)
          ·
            refine ⟨979416330614501344235417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652944220409667562823611 979416330614501344235417)
            ·
              refine ⟨734562247960876008176563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979416330614501344235417 734562247960876008176563)
              ·
                refine ⟨1101843371941314012264845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734562247960876008176563 1101843371941314012264845)
                ·
                  refine ⟨413191264477992754599317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101843371941314012264845 413191264477992754599317)
                  ·
                    rfl

theorem cell20_905273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_905273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905273 prefixEnd_905273 := by exact prefixLift 905273
  have htrace : WordTrace (prefixWord ++ tailWord_905273) baseStart_905273 baseEnd_905273 := by
    simpa [prefixWord, tailWord_905273, baseEnd_905273] using wordTrace_append hprefix tailTrace_905273
  have hstable : (prefixWord ++ tailWord_905273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905273).length < 2 ^ (prefixWord ++ tailWord_905273).sum := by decide
  have hdescent : baseEnd_905273 < baseStart_905273 := by decide
  rcases family_descends (prefixWord ++ tailWord_905273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905314 : List Nat := [3, 3, 2, 2, 3, 1, 2, 2, 2]
def baseStart_905314 : Nat := 118140960795 + 905314 * 2 ^ 59
def prefixEnd_905314 : Nat := 4983230072969 + 3 ^ 40 * 905314 * 2
def baseEnd_905314 : Nat := 413209977995178834232483

theorem tailTrace_905314 : CollatzResearch.WordTrace tailWord_905314 prefixEnd_905314 413209977995178834232483 := by
  unfold tailWord_905314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8254878560552367041688749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22013009494806312111169997 8254878560552367041688749)
  ·
    refine ⟨3095579460207137640633281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8254878560552367041688749 3095579460207137640633281)
    ·
      refine ⟨2321684595155353230474961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3095579460207137640633281 2321684595155353230474961)
      ·
        refine ⟨1741263446366514922856221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2321684595155353230474961 1741263446366514922856221)
        ·
          refine ⟨652973792387443096071083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1741263446366514922856221 652973792387443096071083)
          ·
            refine ⟨979460688581164644106625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652973792387443096071083 979460688581164644106625)
            ·
              refine ⟨734595516435873483079969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979460688581164644106625 734595516435873483079969)
              ·
                refine ⟨550946637326905112309977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734595516435873483079969 550946637326905112309977)
                ·
                  refine ⟨413209977995178834232483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550946637326905112309977 413209977995178834232483)
                  ·
                    rfl

theorem cell20_905314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_905314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905314 prefixEnd_905314 := by exact prefixLift 905314
  have htrace : WordTrace (prefixWord ++ tailWord_905314) baseStart_905314 baseEnd_905314 := by
    simpa [prefixWord, tailWord_905314, baseEnd_905314] using wordTrace_append hprefix tailTrace_905314
  have hstable : (prefixWord ++ tailWord_905314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905314).length < 2 ^ (prefixWord ++ tailWord_905314).sum := by decide
  have hdescent : baseEnd_905314 < baseStart_905314 := by decide
  rcases family_descends (prefixWord ++ tailWord_905314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905360 : List Nat := [2, 1, 1, 1, 1, 1, 8, 3, 2]
def baseStart_905360 : Nat := 118140960795 + 905360 * 2 ^ 59
def prefixEnd_905360 : Nat := 4983230072969 + 3 ^ 40 * 905360 * 2
def baseEnd_905360 : Nat := 413230973648607118698961

theorem tailTrace_905360 : CollatzResearch.WordTrace tailWord_905360 prefixEnd_905360 413230973648607118698961 := by
  unfold tailWord_905360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16510596000021409011464767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22014128000028545348619689 16510596000021409011464767)
  ·
    refine ⟨24765894000032113517197151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16510596000021409011464767 24765894000032113517197151)
    ·
      refine ⟨37148841000048170275795727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24765894000032113517197151 37148841000048170275795727)
      ·
        refine ⟨55723261500072255413693591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37148841000048170275795727 55723261500072255413693591)
        ·
          refine ⟨83584892250108383120540387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55723261500072255413693591 83584892250108383120540387)
          ·
            refine ⟨125377338375162574680810581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83584892250108383120540387 125377338375162574680810581)
            ·
              refine ⟨1469265684083936422040749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 125377338375162574680810581 1469265684083936422040749)
              ·
                refine ⟨550974631531476158265281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1469265684083936422040749 550974631531476158265281)
                ·
                  refine ⟨413230973648607118698961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550974631531476158265281 413230973648607118698961)
                  ·
                    rfl

theorem cell20_905360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_905360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905360 prefixEnd_905360 := by exact prefixLift 905360
  have htrace : WordTrace (prefixWord ++ tailWord_905360) baseStart_905360 baseEnd_905360 := by
    simpa [prefixWord, tailWord_905360, baseEnd_905360] using wordTrace_append hprefix tailTrace_905360
  have hstable : (prefixWord ++ tailWord_905360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905360).length < 2 ^ (prefixWord ++ tailWord_905360).sum := by decide
  have hdescent : baseEnd_905360 < baseStart_905360 := by decide
  rcases family_descends (prefixWord ++ tailWord_905360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905366 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_905366 : Nat := 118140960795 + 905366 * 2 ^ 59
def prefixEnd_905366 : Nat := 4983230072969 + 3 ^ 40 * 905366 * 2
def baseEnd_905366 : Nat := 413233712212097764498937

theorem tailTrace_905366 : CollatzResearch.WordTrace tailWord_905366 prefixEnd_905366 413233712212097764498937 := by
  unfold tailWord_905366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063838177376317565477997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22014273892014054031765301 2063838177376317565477997)
  ·
    refine ⟨773939316516119087054249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2063838177376317565477997 773939316516119087054249)
    ·
      refine ⟨580454487387089315290687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 773939316516119087054249 580454487387089315290687)
      ·
        refine ⟨870681731080633972936031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580454487387089315290687 870681731080633972936031)
        ·
          refine ⟨1306022596620950959404047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870681731080633972936031 1306022596620950959404047)
          ·
            refine ⟨1959033894931426439106071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306022596620950959404047 1959033894931426439106071)
            ·
              refine ⟨2938550842397139658659107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1959033894931426439106071 2938550842397139658659107)
              ·
                refine ⟨4407826263595709487988661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938550842397139658659107 4407826263595709487988661)
                ·
                  refine ⟨413233712212097764498937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4407826263595709487988661 413233712212097764498937)
                  ·
                    rfl

theorem cell20_905366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_905366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905366 prefixEnd_905366 := by exact prefixLift 905366
  have htrace : WordTrace (prefixWord ++ tailWord_905366) baseStart_905366 baseEnd_905366 := by
    simpa [prefixWord, tailWord_905366, baseEnd_905366] using wordTrace_append hprefix tailTrace_905366
  have hstable : (prefixWord ++ tailWord_905366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905366).length < 2 ^ (prefixWord ++ tailWord_905366).sum := by decide
  have hdescent : baseEnd_905366 < baseStart_905366 := by decide
  rcases family_descends (prefixWord ++ tailWord_905366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905370 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_905370 : Nat := 118140960795 + 905370 * 2 ^ 59
def prefixEnd_905370 : Nat := 4983230072969 + 3 ^ 40 * 905370 * 2
def baseEnd_905370 : Nat := 413235537921091528365587

theorem tailTrace_905370 : CollatzResearch.WordTrace tailWord_905370 prefixEnd_905370 413235537921091528365587 := by
  unfold tailWord_905370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8255389182501647432698391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22014371153337726487195709 8255389182501647432698391)
  ·
    refine ⟨12383083773752471149047587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8255389182501647432698391 12383083773752471149047587)
    ·
      refine ⟨18574625660628706723571381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12383083773752471149047587 18574625660628706723571381)
      ·
        refine ⟨1741371155683941255334817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18574625660628706723571381 1741371155683941255334817)
        ·
          refine ⟨1306028366762955941501113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1741371155683941255334817 1306028366762955941501113)
          ·
            refine ⟨979521275072216956125835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306028366762955941501113 979521275072216956125835)
            ·
              refine ⟨1469281912608325434188753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979521275072216956125835 1469281912608325434188753)
              ·
                refine ⟨1101961434456244075641565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469281912608325434188753 1101961434456244075641565)
                ·
                  refine ⟨413235537921091528365587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101961434456244075641565 413235537921091528365587)
                  ·
                    rfl

theorem cell20_905370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_905370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905370 prefixEnd_905370 := by exact prefixLift 905370
  have htrace : WordTrace (prefixWord ++ tailWord_905370) baseStart_905370 baseEnd_905370 := by
    simpa [prefixWord, tailWord_905370, baseEnd_905370] using wordTrace_append hprefix tailTrace_905370
  have hstable : (prefixWord ++ tailWord_905370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905370).length < 2 ^ (prefixWord ++ tailWord_905370).sum := by decide
  have hdescent : baseEnd_905370 < baseStart_905370 := by decide
  rcases family_descends (prefixWord ++ tailWord_905370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905381 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 4]
def baseStart_905381 : Nat := 118140960795 + 905381 * 2 ^ 59
def prefixEnd_905381 : Nat := 4983230072969 + 3 ^ 40 * 905381 * 2
def baseEnd_905381 : Nat := 413240558620824378998875

theorem tailTrace_905381 : CollatzResearch.WordTrace tailWord_905381 prefixEnd_905381 413240558620824378998875 := by
  unfold tailWord_905381
  simp only [CollatzResearch.WordTrace]
  refine ⟨33021957932966738609443997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22014638621977825739629331 33021957932966738609443997)
  ·
    refine ⟨12383234224862526978541499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33021957932966738609443997 12383234224862526978541499)
    ·
      refine ⟨18574851337293790467812249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12383234224862526978541499 18574851337293790467812249)
      ·
        refine ⟨13931138502970342850859187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18574851337293790467812249 13931138502970342850859187)
        ·
          refine ⟨20896707754455514276288781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13931138502970342850859187 20896707754455514276288781)
          ·
            refine ⟨7836265407920817853608293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20896707754455514276288781 7836265407920817853608293)
            ·
              refine ⟨1469299763985153347551555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7836265407920817853608293 1469299763985153347551555)
              ·
                refine ⟨2203949645977730021327333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469299763985153347551555 2203949645977730021327333)
                ·
                  refine ⟨413240558620824378998875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203949645977730021327333 413240558620824378998875)
                  ·
                    rfl

theorem cell20_905381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_905381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905381 prefixEnd_905381 := by exact prefixLift 905381
  have htrace : WordTrace (prefixWord ++ tailWord_905381) baseStart_905381 baseEnd_905381 := by
    simpa [prefixWord, tailWord_905381, baseEnd_905381] using wordTrace_append hprefix tailTrace_905381
  have hstable : (prefixWord ++ tailWord_905381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905381).length < 2 ^ (prefixWord ++ tailWord_905381).sum := by decide
  have hdescent : baseEnd_905381 < baseStart_905381 := by decide
  rcases family_descends (prefixWord ++ tailWord_905381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905412 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_905412 : Nat := 118140960795 + 905412 * 2 ^ 59
def prefixEnd_905412 : Nat := 4983230072969 + 3 ^ 40 * 905412 * 2
def baseEnd_905412 : Nat := 413254707865526048965415

theorem tailTrace_905412 : CollatzResearch.WordTrace tailWord_905412 prefixEnd_905412 413254707865526048965415 := by
  unfold tailWord_905412
  simp only [CollatzResearch.WordTrace]
  refine ⟨16511544297927215451911245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22015392397236287269214993 16511544297927215451911245)
  ·
    refine ⟨6191829111722705794466717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16511544297927215451911245 6191829111722705794466717)
    ·
      refine ⟨2321935916896014672925019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6191829111722705794466717 2321935916896014672925019)
      ·
        refine ⟨3482903875344022009387529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2321935916896014672925019 3482903875344022009387529)
        ·
          refine ⟨2612177906508016507040647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3482903875344022009387529 2612177906508016507040647)
          ·
            refine ⟨3918266859762024760560971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612177906508016507040647 3918266859762024760560971)
            ·
              refine ⟨5877400289643037140841457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918266859762024760560971 5877400289643037140841457)
              ·
                refine ⟨4408050217232277855631093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5877400289643037140841457 4408050217232277855631093)
                ·
                  refine ⟨413254707865526048965415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4408050217232277855631093 413254707865526048965415)
                  ·
                    rfl

theorem cell20_905412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_905412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905412 prefixEnd_905412 := by exact prefixLift 905412
  have htrace : WordTrace (prefixWord ++ tailWord_905412) baseStart_905412 baseEnd_905412 := by
    simpa [prefixWord, tailWord_905412, baseEnd_905412] using wordTrace_append hprefix tailTrace_905412
  have hstable : (prefixWord ++ tailWord_905412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905412).length < 2 ^ (prefixWord ++ tailWord_905412).sum := by decide
  have hdescent : baseEnd_905412 < baseStart_905412 := by decide
  rcases family_descends (prefixWord ++ tailWord_905412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905426 : List Nat := [3, 2, 2, 2, 1, 2, 8]
def baseStart_905426 : Nat := 118140960795 + 905426 * 2 ^ 59
def prefixEnd_905426 : Nat := 4983230072969 + 3 ^ 40 * 905426 * 2
def baseEnd_905426 : Nat := 45917899760778246944299

theorem tailTrace_905426 : CollatzResearch.WordTrace tailWord_905426 prefixEnd_905426 45917899760778246944299 := by
  unfold tailWord_905426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8255899804450927823708033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22015732811869140863221421 8255899804450927823708033)
  ·
    refine ⟨6191924853338195867781025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8255899804450927823708033 6191924853338195867781025)
    ·
      refine ⟨4643943640003646900835769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6191924853338195867781025 4643943640003646900835769)
      ·
        refine ⟨3482957730002735175626827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4643943640003646900835769 3482957730002735175626827)
        ·
          refine ⟨5224436595004102763440241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3482957730002735175626827 5224436595004102763440241)
          ·
            refine ⟨3918327446253077072580181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5224436595004102763440241 3918327446253077072580181)
            ·
              refine ⟨45917899760778246944299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3918327446253077072580181 45917899760778246944299)
              ·
                rfl

theorem cell20_905426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 8].length) (baseStart_905426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905426 prefixEnd_905426 := by exact prefixLift 905426
  have htrace : WordTrace (prefixWord ++ tailWord_905426) baseStart_905426 baseEnd_905426 := by
    simpa [prefixWord, tailWord_905426, baseEnd_905426] using wordTrace_append hprefix tailTrace_905426
  have hstable : (prefixWord ++ tailWord_905426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905426).length < 2 ^ (prefixWord ++ tailWord_905426).sum := by decide
  have hdescent : baseEnd_905426 < baseStart_905426 := by decide
  rcases family_descends (prefixWord ++ tailWord_905426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905433 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_905433 : Nat := 118140960795 + 905433 * 2 ^ 59
def prefixEnd_905433 : Nat := 4983230072969 + 3 ^ 40 * 905433 * 2
def baseEnd_905433 : Nat := 413264292837743309265329

theorem tailTrace_905433 : CollatzResearch.WordTrace tailWord_905433 prefixEnd_905433 413264292837743309265329 := by
  unfold tailWord_905433
  simp only [CollatzResearch.WordTrace]
  refine ⟨33023854528778351490336953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22015903019185567660224635 33023854528778351490336953)
  ·
    refine ⟨24767890896583763617752715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33023854528778351490336953 24767890896583763617752715)
    ·
      refine ⟨37151836344875645426629073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24767890896583763617752715 37151836344875645426629073)
      ·
        refine ⟨27863877258656734069971805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37151836344875645426629073 27863877258656734069971805)
        ·
          refine ⟨10448953971996275276239427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27863877258656734069971805 10448953971996275276239427)
          ·
            refine ⟨15673430957994412914359141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10448953971996275276239427 15673430957994412914359141)
            ·
              refine ⟨2938768304623952421442339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15673430957994412914359141 2938768304623952421442339)
              ·
                refine ⟨4408152456935928632163509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938768304623952421442339 4408152456935928632163509)
                ·
                  refine ⟨413264292837743309265329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4408152456935928632163509 413264292837743309265329)
                  ·
                    rfl

theorem cell20_905433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_905433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905433 prefixEnd_905433 := by exact prefixLift 905433
  have htrace : WordTrace (prefixWord ++ tailWord_905433) baseStart_905433 baseEnd_905433 := by
    simpa [prefixWord, tailWord_905433, baseEnd_905433] using wordTrace_append hprefix tailTrace_905433
  have hstable : (prefixWord ++ tailWord_905433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905433).length < 2 ^ (prefixWord ++ tailWord_905433).sum := by decide
  have hdescent : baseEnd_905433 < baseStart_905433 := by decide
  rcases family_descends (prefixWord ++ tailWord_905433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905450 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_905450 : Nat := 118140960795 + 905450 * 2 ^ 59
def prefixEnd_905450 : Nat := 4983230072969 + 3 ^ 40 * 905450 * 2
def baseEnd_905450 : Nat := 413272052100966805698593

theorem tailTrace_905450 : CollatzResearch.WordTrace tailWord_905450 prefixEnd_905450 413272052100966805698593 := by
  unfold tailWord_905450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8256118642429190848426451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22016316379811175595803869 8256118642429190848426451)
  ·
    refine ⟨12384177963643786272639677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8256118642429190848426451 12384177963643786272639677)
    ·
      refine ⟨4644066736366419852239879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12384177963643786272639677 4644066736366419852239879)
      ·
        refine ⟨6966100104549629778359819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4644066736366419852239879 6966100104549629778359819)
        ·
          refine ⟨10449150156824444667539729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6966100104549629778359819 10449150156824444667539729)
          ·
            refine ⟨7836862617618333500654797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10449150156824444667539729 7836862617618333500654797)
            ·
              refine ⟨2938823481606875062745549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7836862617618333500654797 2938823481606875062745549)
              ·
                refine ⟨1102058805602578148529581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2938823481606875062745549 1102058805602578148529581)
                ·
                  refine ⟨413272052100966805698593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102058805602578148529581 413272052100966805698593)
                  ·
                    rfl

theorem cell20_905450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_905450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905450 prefixEnd_905450 := by exact prefixLift 905450
  have htrace : WordTrace (prefixWord ++ tailWord_905450) baseStart_905450 baseEnd_905450 := by
    simpa [prefixWord, tailWord_905450, baseEnd_905450] using wordTrace_append hprefix tailTrace_905450
  have hstable : (prefixWord ++ tailWord_905450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905450).length < 2 ^ (prefixWord ++ tailWord_905450).sum := by decide
  have hdescent : baseEnd_905450 < baseStart_905450 := by decide
  rcases family_descends (prefixWord ++ tailWord_905450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905498 : List Nat := [3, 1, 1, 3, 5, 1, 1, 5]
def baseStart_905498 : Nat := 118140960795 + 905498 * 2 ^ 59
def prefixEnd_905498 : Nat := 4983230072969 + 3 ^ 40 * 905498 * 2
def baseEnd_905498 : Nat := 137764653536297324032799

theorem tailTrace_905498 : CollatzResearch.WordTrace tailWord_905498 prefixEnd_905498 137764653536297324032799 := by
  unfold tailWord_905498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8256556318385716897863287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22017483515695245060968765 8256556318385716897863287)
  ·
    refine ⟨12384834477578575346794931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8256556318385716897863287 12384834477578575346794931)
    ·
      refine ⟨18577251716367863020192397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12384834477578575346794931 18577251716367863020192397)
      ·
        refine ⟨6966469393637948632572149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18577251716367863020192397 6966469393637948632572149)
        ·
          refine ⟨653106505653557684303639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6966469393637948632572149 653106505653557684303639)
          ·
            refine ⟨979659758480336526455459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653106505653557684303639 979659758480336526455459)
            ·
              refine ⟨1469489637720504789683189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979659758480336526455459 1469489637720504789683189)
              ·
                refine ⟨137764653536297324032799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1469489637720504789683189 137764653536297324032799)
                ·
                  rfl

theorem cell20_905498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_905498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905498 prefixEnd_905498 := by exact prefixLift 905498
  have htrace : WordTrace (prefixWord ++ tailWord_905498) baseStart_905498 baseEnd_905498 := by
    simpa [prefixWord, tailWord_905498, baseEnd_905498] using wordTrace_append hprefix tailTrace_905498
  have hstable : (prefixWord ++ tailWord_905498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905498).length < 2 ^ (prefixWord ++ tailWord_905498).sum := by decide
  have hdescent : baseEnd_905498 < baseStart_905498 := by decide
  rcases family_descends (prefixWord ++ tailWord_905498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905512 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 4]
def baseStart_905512 : Nat := 118140960795 + 905512 * 2 ^ 59
def prefixEnd_905512 : Nat := 4983230072969 + 3 ^ 40 * 905512 * 2
def baseEnd_905512 : Nat := 413300350590370145631673

theorem tailTrace_905512 : CollatzResearch.WordTrace tailWord_905512 prefixEnd_905512 413300350590370145631673 := by
  unfold tailWord_905512
  simp only [CollatzResearch.WordTrace]
  refine ⟨16513367947746073991231395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22017823930328098654975193 16513367947746073991231395)
  ·
    refine ⟨24770051921619110986847093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16513367947746073991231395 24770051921619110986847093)
    ·
      refine ⟨2322192367651791655016915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24770051921619110986847093 2322192367651791655016915)
      ·
        refine ⟨3483288551477687482525373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322192367651791655016915 3483288551477687482525373)
        ·
          refine ⟨1306233206804132805947015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3483288551477687482525373 1306233206804132805947015)
          ·
            refine ⟨1959349810206199208920523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306233206804132805947015 1959349810206199208920523)
            ·
              refine ⟨2939024715309298813380785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1959349810206199208920523 2939024715309298813380785)
              ·
                refine ⟨2204268536481974110035589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2939024715309298813380785 2204268536481974110035589)
                ·
                  refine ⟨413300350590370145631673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204268536481974110035589 413300350590370145631673)
                  ·
                    rfl

theorem cell20_905512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_905512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905512 prefixEnd_905512 := by exact prefixLift 905512
  have htrace : WordTrace (prefixWord ++ tailWord_905512) baseStart_905512 baseEnd_905512 := by
    simpa [prefixWord, tailWord_905512, baseEnd_905512] using wordTrace_append hprefix tailTrace_905512
  have hstable : (prefixWord ++ tailWord_905512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905512).length < 2 ^ (prefixWord ++ tailWord_905512).sum := by decide
  have hdescent : baseEnd_905512 < baseStart_905512 := by decide
  rcases family_descends (prefixWord ++ tailWord_905512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905516 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_905516 : Nat := 118140960795 + 905516 * 2 ^ 59
def prefixEnd_905516 : Nat := 4983230072969 + 3 ^ 40 * 905516 * 2
def baseEnd_905516 : Nat := 413302176299363909498323

theorem tailTrace_905516 : CollatzResearch.WordTrace tailWord_905516 prefixEnd_905516 413302176299363909498323 := by
  unfold tailWord_905516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16513440893738828332804201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22017921191651771110405601 16513440893738828332804201)
  ·
    refine ⟨12385080670304121249603151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16513440893738828332804201 12385080670304121249603151)
    ·
      refine ⟨18577621005456181874404727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12385080670304121249603151 18577621005456181874404727)
      ·
        refine ⟨27866431508184272811607091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18577621005456181874404727 27866431508184272811607091)
        ·
          refine ⟨41799647262276409217410637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27866431508184272811607091 41799647262276409217410637)
          ·
            refine ⟨15674867723353653456528989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41799647262276409217410637 15674867723353653456528989)
            ·
              refine ⟨5878075396257620046198371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15674867723353653456528989 5878075396257620046198371)
              ·
                refine ⟨8817113094386430069297557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878075396257620046198371 8817113094386430069297557)
                ·
                  refine ⟨413302176299363909498323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8817113094386430069297557 413302176299363909498323)
                  ·
                    rfl

theorem cell20_905516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_905516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905516 prefixEnd_905516 := by exact prefixLift 905516
  have htrace : WordTrace (prefixWord ++ tailWord_905516) baseStart_905516 baseEnd_905516 := by
    simpa [prefixWord, tailWord_905516, baseEnd_905516] using wordTrace_append hprefix tailTrace_905516
  have hstable : (prefixWord ++ tailWord_905516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905516).length < 2 ^ (prefixWord ++ tailWord_905516).sum := by decide
  have hdescent : baseEnd_905516 < baseStart_905516 := by decide
  rcases family_descends (prefixWord ++ tailWord_905516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905529 : List Nat := [1, 2, 1, 6, 1, 2, 2, 3, 2]
def baseStart_905529 : Nat := 118140960795 + 905529 * 2 ^ 59
def prefixEnd_905529 : Nat := 4983230072969 + 3 ^ 40 * 905529 * 2
def baseEnd_905529 : Nat := 413308109853593642064937

theorem tailTrace_905529 : CollatzResearch.WordTrace tailWord_905529 prefixEnd_905529 413308109853593642064937 := by
  unfold tailWord_905529
  simp only [CollatzResearch.WordTrace]
  refine ⟨33027355936430559885831641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22018237290953706590554427 33027355936430559885831641)
  ·
    refine ⟨24770516952322919914373731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33027355936430559885831641 24770516952322919914373731)
    ·
      refine ⟨37155775428484379871560597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24770516952322919914373731 37155775428484379871560597)
      ·
        refine ⟨1741676973210205306479403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37155775428484379871560597 1741676973210205306479403)
        ·
          refine ⟨2612515459815307959719105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741676973210205306479403 2612515459815307959719105)
          ·
            refine ⟨1959386594861480969789329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2612515459815307959719105 1959386594861480969789329)
            ·
              refine ⟨1469539946146110727341997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1959386594861480969789329 1469539946146110727341997)
              ·
                refine ⟨551077479804791522753249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1469539946146110727341997 551077479804791522753249)
                ·
                  refine ⟨413308109853593642064937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551077479804791522753249 413308109853593642064937)
                  ·
                    rfl

theorem cell20_905529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_905529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905529 prefixEnd_905529 := by exact prefixLift 905529
  have htrace : WordTrace (prefixWord ++ tailWord_905529) baseStart_905529 baseEnd_905529 := by
    simpa [prefixWord, tailWord_905529, baseEnd_905529] using wordTrace_append hprefix tailTrace_905529
  have hstable : (prefixWord ++ tailWord_905529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905529).length < 2 ^ (prefixWord ++ tailWord_905529).sum := by decide
  have hdescent : baseEnd_905529 < baseStart_905529 := by decide
  rcases family_descends (prefixWord ++ tailWord_905529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905547 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 3]
def baseStart_905547 : Nat := 118140960795 + 905547 * 2 ^ 59
def prefixEnd_905547 : Nat := 4983230072969 + 3 ^ 40 * 905547 * 2
def baseEnd_905547 : Nat := 413316325544065579464863

theorem tailTrace_905547 : CollatzResearch.WordTrace tailWord_905547 prefixEnd_905547 413316325544065579464863 := by
  unfold tailWord_905547
  simp only [CollatzResearch.WordTrace]
  refine ⟨33028012450365348959986895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22018674966910232639991263 33028012450365348959986895)
  ·
    refine ⟨49542018675548023439980343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33028012450365348959986895 49542018675548023439980343)
    ·
      refine ⟨74313028013322035159970515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49542018675548023439980343 74313028013322035159970515)
      ·
        refine ⟨111469542019983052739955773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74313028013322035159970515 111469542019983052739955773)
        ·
          refine ⟨41801078257493644777483415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111469542019983052739955773 41801078257493644777483415)
          ·
            refine ⟨62701617386240467166225123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41801078257493644777483415 62701617386240467166225123)
            ·
              refine ⟨94052426079360700749337685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62701617386240467166225123 94052426079360700749337685)
              ·
                refine ⟨1102176868117508211906301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 94052426079360700749337685 1102176868117508211906301)
                ·
                  refine ⟨413316325544065579464863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102176868117508211906301 413316325544065579464863)
                  ·
                    rfl

theorem cell20_905547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 3].length) (baseStart_905547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905547 prefixEnd_905547 := by exact prefixLift 905547
  have htrace : WordTrace (prefixWord ++ tailWord_905547) baseStart_905547 baseEnd_905547 := by
    simpa [prefixWord, tailWord_905547, baseEnd_905547] using wordTrace_append hprefix tailTrace_905547
  have hstable : (prefixWord ++ tailWord_905547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905547).length < 2 ^ (prefixWord ++ tailWord_905547).sum := by decide
  have hdescent : baseEnd_905547 < baseStart_905547 := by decide
  rcases family_descends (prefixWord ++ tailWord_905547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905561 : List Nat := [1, 2, 1, 2, 2, 2, 1, 9]
def baseStart_905561 : Nat := 118140960795 + 905561 * 2 ^ 59
def prefixEnd_905561 : Nat := 4983230072969 + 3 ^ 40 * 905561 * 2
def baseEnd_905561 : Nat := 137774238508514584332713

theorem tailTrace_905561 : CollatzResearch.WordTrace tailWord_905561 prefixEnd_905561 137774238508514584332713 := by
  unfold tailWord_905561
  simp only [CollatzResearch.WordTrace]
  refine ⟨33028523072314629350996537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22019015381543086233997691 33028523072314629350996537)
  ·
    refine ⟨24771392304235972013247403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33028523072314629350996537 24771392304235972013247403)
    ·
      refine ⟨37157088456353958019871105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24771392304235972013247403 37157088456353958019871105)
      ·
        refine ⟨27867816342265468514903329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37157088456353958019871105 27867816342265468514903329)
        ·
          refine ⟨20900862256699101386177497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27867816342265468514903329 20900862256699101386177497)
          ·
            refine ⟨15675646692524326039633123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20900862256699101386177497 15675646692524326039633123)
            ·
              refine ⟨23513470038786489059449685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15675646692524326039633123 23513470038786489059449685)
              ·
                refine ⟨137774238508514584332713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23513470038786489059449685 137774238508514584332713)
                ·
                  rfl

theorem cell20_905561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_905561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905561 prefixEnd_905561 := by exact prefixLift 905561
  have htrace : WordTrace (prefixWord ++ tailWord_905561) baseStart_905561 baseEnd_905561 := by
    simpa [prefixWord, tailWord_905561, baseEnd_905561] using wordTrace_append hprefix tailTrace_905561
  have hstable : (prefixWord ++ tailWord_905561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905561).length < 2 ^ (prefixWord ++ tailWord_905561).sum := by decide
  have hdescent : baseEnd_905561 < baseStart_905561 := by decide
  rcases family_descends (prefixWord ++ tailWord_905561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905566 : List Nat := [4, 4, 2, 1, 2, 1, 2, 4]
def baseStart_905566 : Nat := 118140960795 + 905566 * 2 ^ 59
def prefixEnd_905566 : Nat := 4983230072969 + 3 ^ 40 * 905566 * 2
def baseEnd_905566 : Nat := 137774999220595319277151

theorem tailTrace_905566 : CollatzResearch.WordTrace tailWord_905566 prefixEnd_905566 137774999220595319277151 := by
  unfold tailWord_905566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128588179662064400616069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22019136958197676803285701 4128588179662064400616069)
  ·
    refine ⟨774110283686637075115513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4128588179662064400616069 774110283686637075115513)
    ·
      refine ⟨580582712764977806336635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 774110283686637075115513 580582712764977806336635)
      ·
        refine ⟨870874069147466709504953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580582712764977806336635 870874069147466709504953)
        ·
          refine ⟨653155551860600032128715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870874069147466709504953 653155551860600032128715)
          ·
            refine ⟨979733327790900048193073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653155551860600032128715 979733327790900048193073)
            ·
              refine ⟨734799995843175036144805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979733327790900048193073 734799995843175036144805)
              ·
                refine ⟨137774999220595319277151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 734799995843175036144805 137774999220595319277151)
                ·
                  rfl

theorem cell20_905566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_905566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905566 prefixEnd_905566 := by exact prefixLift 905566
  have htrace : WordTrace (prefixWord ++ tailWord_905566) baseStart_905566 baseEnd_905566 := by
    simpa [prefixWord, tailWord_905566, baseEnd_905566] using wordTrace_append hprefix tailTrace_905566
  have hstable : (prefixWord ++ tailWord_905566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905566).length < 2 ^ (prefixWord ++ tailWord_905566).sum := by decide
  have hdescent : baseEnd_905566 < baseStart_905566 := by decide
  rcases family_descends (prefixWord ++ tailWord_905566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905609 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 4]
def baseStart_905609 : Nat := 118140960795 + 905609 * 2 ^ 59
def prefixEnd_905609 : Nat := 4983230072969 + 3 ^ 40 * 905609 * 2
def baseEnd_905609 : Nat := 413344624033468919397943

theorem tailTrace_905609 : CollatzResearch.WordTrace tailWord_905609 prefixEnd_905609 413344624033468919397943 := by
  unfold tailWord_905609
  simp only [CollatzResearch.WordTrace]
  refine ⟨33030273776140733548743881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22020182517427155699162587 33030273776140733548743881)
  ·
    refine ⟨24772705332105550161557911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33030273776140733548743881 24772705332105550161557911)
    ·
      refine ⟨37159057998158325242336867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24772705332105550161557911 37159057998158325242336867)
      ·
        refine ⟨55738586997237487863505301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37159057998158325242336867 55738586997237487863505301)
        ·
          refine ⟨2612746265495507243601811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55738586997237487863505301 2612746265495507243601811)
          ·
            refine ⟨3919119398243260865402717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612746265495507243601811 3919119398243260865402717)
            ·
              refine ⟨1469669774341222824526019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3919119398243260865402717 1469669774341222824526019)
              ·
                refine ⟨2204504661511834236789029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469669774341222824526019 2204504661511834236789029)
                ·
                  refine ⟨413344624033468919397943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204504661511834236789029 413344624033468919397943)
                  ·
                    rfl

theorem cell20_905609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_905609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905609 prefixEnd_905609 := by exact prefixLift 905609
  have htrace : WordTrace (prefixWord ++ tailWord_905609) baseStart_905609 baseEnd_905609 := by
    simpa [prefixWord, tailWord_905609, baseEnd_905609] using wordTrace_append hprefix tailTrace_905609
  have hstable : (prefixWord ++ tailWord_905609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905609).length < 2 ^ (prefixWord ++ tailWord_905609).sum := by decide
  have hdescent : baseEnd_905609 < baseStart_905609 := by decide
  rcases family_descends (prefixWord ++ tailWord_905609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905637 : List Nat := [1, 3, 1, 2, 1, 1, 3, 8]
def baseStart_905637 : Nat := 118140960795 + 905637 * 2 ^ 59
def prefixEnd_905637 : Nat := 4983230072969 + 3 ^ 40 * 905637 * 2
def baseEnd_905637 : Nat := 137785801332141755488165

theorem tailTrace_905637 : CollatzResearch.WordTrace tailWord_905637 prefixEnd_905637 137785801332141755488165 := by
  unfold tailWord_905637
  simp only [CollatzResearch.WordTrace]
  refine ⟨33031295020039294330763165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22020863346692862887175443 33031295020039294330763165)
  ·
    refine ⟨12386735632514735374036187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33031295020039294330763165 12386735632514735374036187)
    ·
      refine ⟨18580103448772103061054281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12386735632514735374036187 18580103448772103061054281)
      ·
        refine ⟨13935077586579077295790711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18580103448772103061054281 13935077586579077295790711)
        ·
          refine ⟨20902616379868615943686067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13935077586579077295790711 20902616379868615943686067)
          ·
            refine ⟨31353924569802923915529101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20902616379868615943686067 31353924569802923915529101)
            ·
              refine ⟨11757721713676096468323413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31353924569802923915529101 11757721713676096468323413)
              ·
                refine ⟨137785801332141755488165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11757721713676096468323413 137785801332141755488165)
                ·
                  rfl

theorem cell20_905637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_905637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905637 prefixEnd_905637 := by exact prefixLift 905637
  have htrace : WordTrace (prefixWord ++ tailWord_905637) baseStart_905637 baseEnd_905637 := by
    simpa [prefixWord, tailWord_905637, baseEnd_905637] using wordTrace_append hprefix tailTrace_905637
  have hstable : (prefixWord ++ tailWord_905637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905637).length < 2 ^ (prefixWord ++ tailWord_905637).sum := by decide
  have hdescent : baseEnd_905637 < baseStart_905637 := by decide
  rcases family_descends (prefixWord ++ tailWord_905637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905660 : List Nat := [2, 2, 2, 4, 1, 3, 2, 2, 2]
def baseStart_905660 : Nat := 118140960795 + 905660 * 2 ^ 59
def prefixEnd_905660 : Nat := 4983230072969 + 3 ^ 40 * 905660 * 2
def baseEnd_905660 : Nat := 413367901823139408697735

theorem tailTrace_905660 : CollatzResearch.WordTrace tailWord_905660 prefixEnd_905660 413367901823139408697735 := by
  unfold tailWord_905660
  simp only [CollatzResearch.WordTrace]
  refine ⟨16516066949477984629425217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22021422599303979505900289 16516066949477984629425217)
  ·
    refine ⟨12387050212108488472068913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16516066949477984629425217 12387050212108488472068913)
    ·
      refine ⟨9290287659081366354051685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12387050212108488472068913 9290287659081366354051685)
      ·
        refine ⟨1741928936077756191384691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9290287659081366354051685 1741928936077756191384691)
        ·
          refine ⟨2612893404116634287077037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741928936077756191384691 2612893404116634287077037)
          ·
            refine ⟨979835026543737857653889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2612893404116634287077037 979835026543737857653889)
            ·
              refine ⟨734876269907803393240417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979835026543737857653889 734876269907803393240417)
              ·
                refine ⟨551157202430852544930313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734876269907803393240417 551157202430852544930313)
                ·
                  refine ⟨413367901823139408697735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551157202430852544930313 413367901823139408697735)
                  ·
                    rfl

theorem cell20_905660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_905660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905660 prefixEnd_905660 := by exact prefixLift 905660
  have htrace : WordTrace (prefixWord ++ tailWord_905660) baseStart_905660 baseEnd_905660 := by
    simpa [prefixWord, tailWord_905660, baseEnd_905660] using wordTrace_append hprefix tailTrace_905660
  have hstable : (prefixWord ++ tailWord_905660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905660).length < 2 ^ (prefixWord ++ tailWord_905660).sum := by decide
  have hdescent : baseEnd_905660 < baseStart_905660 := by decide
  rcases family_descends (prefixWord ++ tailWord_905660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905685 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 4]
def baseStart_905685 : Nat := 118140960795 + 905685 * 2 ^ 59
def prefixEnd_905685 : Nat := 4983230072969 + 3 ^ 40 * 905685 * 2
def baseEnd_905685 : Nat := 413379312504350432864299

theorem tailTrace_905685 : CollatzResearch.WordTrace tailWord_905685 prefixEnd_905685 413379312504350432864299 := by
  unfold tailWord_905685
  simp only [CollatzResearch.WordTrace]
  refine ⟨33033045723865398528510509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22022030482576932352340339 33033045723865398528510509)
  ·
    refine ⟨12387392146449524448191441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33033045723865398528510509 12387392146449524448191441)
    ·
      refine ⟨9290544109837143336143581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12387392146449524448191441 9290544109837143336143581)
      ·
        refine ⟨3483954041188928751053843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9290544109837143336143581 3483954041188928751053843)
        ·
          refine ⟨5225931061783393126580765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483954041188928751053843 5225931061783393126580765)
          ·
            refine ⟨1959724148168772422467787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5225931061783393126580765 1959724148168772422467787)
            ·
              refine ⟨2939586222253158633701681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1959724148168772422467787 2939586222253158633701681)
              ·
                refine ⟨2204689666689868975276261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2939586222253158633701681 2204689666689868975276261)
                ·
                  refine ⟨413379312504350432864299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204689666689868975276261 413379312504350432864299)
                  ·
                    rfl

theorem cell20_905685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_905685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905685 prefixEnd_905685 := by exact prefixLift 905685
  have htrace : WordTrace (prefixWord ++ tailWord_905685) baseStart_905685 baseEnd_905685 := by
    simpa [prefixWord, tailWord_905685, baseEnd_905685] using wordTrace_append hprefix tailTrace_905685
  have hstable : (prefixWord ++ tailWord_905685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905685).length < 2 ^ (prefixWord ++ tailWord_905685).sum := by decide
  have hdescent : baseEnd_905685 < baseStart_905685 := by decide
  rcases family_descends (prefixWord ++ tailWord_905685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905713 : List Nat := [1, 2, 2, 2, 3, 1, 9]
def baseStart_905713 : Nat := 118140960795 + 905713 * 2 ^ 59
def prefixEnd_905713 : Nat := 4983230072969 + 3 ^ 40 * 905713 * 2
def baseEnd_905713 : Nat := 45932454718589642214539

theorem tailTrace_905713 : CollatzResearch.WordTrace tailWord_905713 prefixEnd_905713 45932454718589642214539 := by
  unfold tailWord_905713
  simp only [CollatzResearch.WordTrace]
  refine ⟨33034066967763959310529793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22022711311842639540353195 33034066967763959310529793)
  ·
    refine ⟨24775550225822969482897345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33034066967763959310529793 24775550225822969482897345)
    ·
      refine ⟨18581662669367227112173009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24775550225822969482897345 18581662669367227112173009)
      ·
        refine ⟨13936247002025420334129757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18581662669367227112173009 13936247002025420334129757)
        ·
          refine ⟨5226092625759532625298659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13936247002025420334129757 5226092625759532625298659)
          ·
            refine ⟨7839138938639298937947989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226092625759532625298659 7839138938639298937947989)
            ·
              refine ⟨45932454718589642214539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7839138938639298937947989 45932454718589642214539)
              ·
                rfl

theorem cell20_905713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 9].length) (baseStart_905713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905713 prefixEnd_905713 := by exact prefixLift 905713
  have htrace : WordTrace (prefixWord ++ tailWord_905713) baseStart_905713 baseEnd_905713 := by
    simpa [prefixWord, tailWord_905713, baseEnd_905713] using wordTrace_append hprefix tailTrace_905713
  have hstable : (prefixWord ++ tailWord_905713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905713).length < 2 ^ (prefixWord ++ tailWord_905713).sum := by decide
  have hdescent : baseEnd_905713 < baseStart_905713 := by decide
  rcases family_descends (prefixWord ++ tailWord_905713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905757 : List Nat := [1, 4, 2, 2, 1, 4, 1, 3, 2]
def baseStart_905757 : Nat := 118140960795 + 905757 * 2 ^ 59
def prefixEnd_905757 : Nat := 4983230072969 + 3 ^ 40 * 905757 * 2
def baseEnd_905757 : Nat := 413412175266238182464005

theorem tailTrace_905757 : CollatzResearch.WordTrace tailWord_905757 prefixEnd_905757 413412175266238182464005 := by
  unfold tailWord_905757
  simp only [CollatzResearch.WordTrace]
  refine ⟨33035671779604554825131525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22023781186403036550087683 33035671779604554825131525)
  ·
    refine ⟨6194188458675854029712161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33035671779604554825131525 6194188458675854029712161)
    ·
      refine ⟨4645641344006890522284121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6194188458675854029712161 4645641344006890522284121)
      ·
        refine ⟨3484231008005167891713091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4645641344006890522284121 3484231008005167891713091)
        ·
          refine ⟨5226346512007751837569637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3484231008005167891713091 5226346512007751837569637)
          ·
            refine ⟨979939971001453469544307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5226346512007751837569637 979939971001453469544307)
            ·
              refine ⟨1469909956502180204316461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979939971001453469544307 1469909956502180204316461)
              ·
                refine ⟨551216233688317576618673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1469909956502180204316461 551216233688317576618673)
                ·
                  refine ⟨413412175266238182464005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551216233688317576618673 413412175266238182464005)
                  ·
                    rfl

theorem cell20_905757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_905757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905757 prefixEnd_905757 := by exact prefixLift 905757
  have htrace : WordTrace (prefixWord ++ tailWord_905757) baseStart_905757 baseEnd_905757 := by
    simpa [prefixWord, tailWord_905757, baseEnd_905757] using wordTrace_append hprefix tailTrace_905757
  have hstable : (prefixWord ++ tailWord_905757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905757).length < 2 ^ (prefixWord ++ tailWord_905757).sum := by decide
  have hdescent : baseEnd_905757 < baseStart_905757 := by decide
  rcases family_descends (prefixWord ++ tailWord_905757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905764 : List Nat := [2, 3, 1, 5, 2, 1, 6]
def baseStart_905764 : Nat := 118140960795 + 905764 * 2 ^ 59
def prefixEnd_905764 : Nat := 4983230072969 + 3 ^ 40 * 905764 * 2
def baseEnd_905764 : Nat := 45935041139664141025627

theorem tailTrace_905764 : CollatzResearch.WordTrace tailWord_905764 prefixEnd_905764 45935041139664141025627 := by
  unfold tailWord_905764
  simp only [CollatzResearch.WordTrace]
  refine ⟨16517963545289597510318173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22023951393719463347090897 16517963545289597510318173)
  ·
    refine ⟨6194236329483599066369315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16517963545289597510318173 6194236329483599066369315)
    ·
      refine ⟨9291354494225398599553973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6194236329483599066369315 9291354494225398599553973)
      ·
        refine ⟨871064483833631118708185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9291354494225398599553973 871064483833631118708185)
        ·
          refine ⟨653298362875223339031139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871064483833631118708185 653298362875223339031139)
          ·
            refine ⟨979947544312835008546709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653298362875223339031139 979947544312835008546709)
            ·
              refine ⟨45935041139664141025627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 979947544312835008546709 45935041139664141025627)
              ·
                rfl

theorem cell20_905764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 6].length) (baseStart_905764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905764 prefixEnd_905764 := by exact prefixLift 905764
  have htrace : WordTrace (prefixWord ++ tailWord_905764) baseStart_905764 baseEnd_905764 := by
    simpa [prefixWord, tailWord_905764, baseEnd_905764] using wordTrace_append hprefix tailTrace_905764
  have hstable : (prefixWord ++ tailWord_905764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905764).length < 2 ^ (prefixWord ++ tailWord_905764).sum := by decide
  have hdescent : baseEnd_905764 < baseStart_905764 := by decide
  rcases family_descends (prefixWord ++ tailWord_905764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905768 : List Nat := [2, 1, 5, 2, 1, 1, 8]
def baseStart_905768 : Nat := 118140960795 + 905768 * 2 ^ 59
def prefixEnd_905768 : Nat := 4983230072969 + 3 ^ 40 * 905768 * 2
def baseEnd_905768 : Nat := 45935243996219003677477

theorem tailTrace_905768 : CollatzResearch.WordTrace tailWord_905768 prefixEnd_905768 45935243996219003677477 := by
  unfold tailWord_905768
  simp only [CollatzResearch.WordTrace]
  refine ⟨16518036491282351851890979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22024048655043135802521305 16518036491282351851890979)
  ·
    refine ⟨24777054736923527777836469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16518036491282351851890979 24777054736923527777836469)
    ·
      refine ⟨2322848881586580729172169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24777054736923527777836469 2322848881586580729172169)
      ·
        refine ⟨1742136661189935546879127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2322848881586580729172169 1742136661189935546879127)
        ·
          refine ⟨2613204991784903320318691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742136661189935546879127 2613204991784903320318691)
          ·
            refine ⟨3919807487677354980478037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613204991784903320318691 3919807487677354980478037)
            ·
              refine ⟨45935243996219003677477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3919807487677354980478037 45935243996219003677477)
              ·
                rfl

theorem cell20_905768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 8].length) (baseStart_905768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905768 prefixEnd_905768 := by exact prefixLift 905768
  have htrace : WordTrace (prefixWord ++ tailWord_905768) baseStart_905768 baseEnd_905768 := by
    simpa [prefixWord, tailWord_905768, baseEnd_905768] using wordTrace_append hprefix tailTrace_905768
  have hstable : (prefixWord ++ tailWord_905768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905768).length < 2 ^ (prefixWord ++ tailWord_905768).sum := by decide
  have hdescent : baseEnd_905768 < baseStart_905768 := by decide
  rcases family_descends (prefixWord ++ tailWord_905768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905774 : List Nat := [4, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_905774 : Nat := 118140960795 + 905774 * 2 ^ 59
def prefixEnd_905774 : Nat := 4983230072969 + 3 ^ 40 * 905774 * 2
def baseEnd_905774 : Nat := 413419934529461678897269

theorem tailTrace_905774 : CollatzResearch.WordTrace tailWord_905774 prefixEnd_905774 413419934529461678897269 := by
  unfold tailWord_905774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4129536477567870841062547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22024194547028644485666917 4129536477567870841062547)
  ·
    refine ⟨6194304716351806261593821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4129536477567870841062547 6194304716351806261593821)
    ·
      refine ⟨2322864268631927348097683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6194304716351806261593821 2322864268631927348097683)
      ·
        refine ⟨3484296402947891022146525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322864268631927348097683 3484296402947891022146525)
        ·
          refine ⟨1306611151105459133304947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3484296402947891022146525 1306611151105459133304947)
          ·
            refine ⟨1959916726658188699957421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306611151105459133304947 1959916726658188699957421)
            ·
              refine ⟨734968772496820762484033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1959916726658188699957421 734968772496820762484033)
              ·
                refine ⟨551226579372615571863025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734968772496820762484033 551226579372615571863025)
                ·
                  refine ⟨413419934529461678897269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551226579372615571863025 413419934529461678897269)
                  ·
                    rfl

theorem cell20_905774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_905774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905774 prefixEnd_905774 := by exact prefixLift 905774
  have htrace : WordTrace (prefixWord ++ tailWord_905774) baseStart_905774 baseEnd_905774 := by
    simpa [prefixWord, tailWord_905774, baseEnd_905774] using wordTrace_append hprefix tailTrace_905774
  have hstable : (prefixWord ++ tailWord_905774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905774).length < 2 ^ (prefixWord ++ tailWord_905774).sum := by decide
  have hdescent : baseEnd_905774 < baseStart_905774 := by decide
  rcases family_descends (prefixWord ++ tailWord_905774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905792 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 3]
def baseStart_905792 : Nat := 118140960795 + 905792 * 2 ^ 59
def prefixEnd_905792 : Nat := 4983230072969 + 3 ^ 40 * 905792 * 2
def baseEnd_905792 : Nat := 413428150219933616297195

theorem tailTrace_905792 : CollatzResearch.WordTrace tailWord_905792 prefixEnd_905792 413428150219933616297195 := by
  unfold tailWord_905792
  simp only [CollatzResearch.WordTrace]
  refine ⟨16518474167238877901327815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22024632222985170535103753 16518474167238877901327815)
  ·
    refine ⟨24777711250858316851991723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16518474167238877901327815 24777711250858316851991723)
    ·
      refine ⟨37166566876287475277987585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24777711250858316851991723 37166566876287475277987585)
      ·
        refine ⟨27874925157215606458490689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37166566876287475277987585 27874925157215606458490689)
        ·
          refine ⟨20906193867911704843868017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27874925157215606458490689 20906193867911704843868017)
          ·
            refine ⟨15679645400933778632901013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20906193867911704843868017 15679645400933778632901013)
            ·
              refine ⟨734983378168770873417235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15679645400933778632901013 734983378168770873417235)
              ·
                refine ⟨1102475067253156310125853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734983378168770873417235 1102475067253156310125853)
                ·
                  refine ⟨413428150219933616297195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102475067253156310125853 413428150219933616297195)
                  ·
                    rfl

theorem cell20_905792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_905792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905792 prefixEnd_905792 := by exact prefixLift 905792
  have htrace : WordTrace (prefixWord ++ tailWord_905792) baseStart_905792 baseEnd_905792 := by
    simpa [prefixWord, tailWord_905792, baseEnd_905792] using wordTrace_append hprefix tailTrace_905792
  have hstable : (prefixWord ++ tailWord_905792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905792).length < 2 ^ (prefixWord ++ tailWord_905792).sum := by decide
  have hdescent : baseEnd_905792 < baseStart_905792 := by decide
  rcases family_descends (prefixWord ++ tailWord_905792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905826 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_905826 : Nat := 118140960795 + 905826 * 2 ^ 59
def prefixEnd_905826 : Nat := 4983230072969 + 3 ^ 40 * 905826 * 2
def baseEnd_905826 : Nat := 413443668746380609163723

theorem tailTrace_905826 : CollatzResearch.WordTrace tailWord_905826 prefixEnd_905826 413443668746380609163723 := by
  unfold tailWord_905826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8259547104088644902348333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22025458944236386406262221 8259547104088644902348333)
  ·
    refine ⟨3097330164033241838380625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8259547104088644902348333 3097330164033241838380625)
    ·
      refine ⟨2322997623024931378785469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3097330164033241838380625 2322997623024931378785469)
      ·
        refine ⟨871124108634349267044551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2322997623024931378785469 871124108634349267044551)
        ·
          refine ⟨1306686162951523900566827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871124108634349267044551 1306686162951523900566827)
          ·
            refine ⟨1960029244427285850850241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306686162951523900566827 1960029244427285850850241)
            ·
              refine ⟨1470021933320464388137681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960029244427285850850241 1470021933320464388137681)
              ·
                refine ⟨1102516449990348291103261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470021933320464388137681 1102516449990348291103261)
                ·
                  refine ⟨413443668746380609163723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102516449990348291103261 413443668746380609163723)
                  ·
                    rfl

theorem cell20_905826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_905826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905826 prefixEnd_905826 := by exact prefixLift 905826
  have htrace : WordTrace (prefixWord ++ tailWord_905826) baseStart_905826 baseEnd_905826 := by
    simpa [prefixWord, tailWord_905826, baseEnd_905826] using wordTrace_append hprefix tailTrace_905826
  have hstable : (prefixWord ++ tailWord_905826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905826).length < 2 ^ (prefixWord ++ tailWord_905826).sum := by decide
  have hdescent : baseEnd_905826 < baseStart_905826 := by decide
  rcases family_descends (prefixWord ++ tailWord_905826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905902 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_905902 : Nat := 118140960795 + 905902 * 2 ^ 59
def prefixEnd_905902 : Nat := 4983230072969 + 3 ^ 40 * 905902 * 2
def baseEnd_905902 : Nat := 413478357217262122630079

theorem tailTrace_905902 : CollatzResearch.WordTrace tailWord_905902 prefixEnd_905902 413478357217262122630079 := by
  unfold tailWord_905902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4130120045509905573644995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22027306909386163059439973 4130120045509905573644995)
  ·
    refine ⟨6195180068264858360467493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4130120045509905573644995 6195180068264858360467493)
    ·
      refine ⟨1161596262799660942587655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6195180068264858360467493 1161596262799660942587655)
      ·
        refine ⟨1742394394199491413881483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161596262799660942587655 1742394394199491413881483)
        ·
          refine ⟨2613591591299237120822225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742394394199491413881483 2613591591299237120822225)
          ·
            refine ⟨1960193693474427840616669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2613591591299237120822225 1960193693474427840616669)
            ·
              refine ⟨735072635052910440231251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1960193693474427840616669 735072635052910440231251)
              ·
                refine ⟨1102608952579365660346877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735072635052910440231251 1102608952579365660346877)
                ·
                  refine ⟨413478357217262122630079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102608952579365660346877 413478357217262122630079)
                  ·
                    rfl

theorem cell20_905902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_905902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905902 prefixEnd_905902 := by exact prefixLift 905902
  have htrace : WordTrace (prefixWord ++ tailWord_905902) baseStart_905902 baseEnd_905902 := by
    simpa [prefixWord, tailWord_905902, baseEnd_905902] using wordTrace_append hprefix tailTrace_905902
  have hstable : (prefixWord ++ tailWord_905902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905902).length < 2 ^ (prefixWord ++ tailWord_905902).sum := by decide
  have hdescent : baseEnd_905902 < baseStart_905902 := by decide
  rcases family_descends (prefixWord ++ tailWord_905902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905920 : List Nat := [2, 1, 1, 2, 4, 2, 4, 4]
def baseStart_905920 : Nat := 118140960795 + 905920 * 2 ^ 59
def prefixEnd_905920 : Nat := 4983230072969 + 3 ^ 40 * 905920 * 2
def baseEnd_905920 : Nat := 137828857635911353343335

theorem tailTrace_905920 : CollatzResearch.WordTrace tailWord_905920 prefixEnd_905920 137828857635911353343335 := by
  unfold tailWord_905920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16520808439007016831657607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22027744585342689108876809 16520808439007016831657607)
  ·
    refine ⟨24781212658510525247486411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16520808439007016831657607 24781212658510525247486411)
    ·
      refine ⟨37171818987765787871229617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24781212658510525247486411 37171818987765787871229617)
      ·
        refine ⟨27878864240824340903422213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37171818987765787871229617 27878864240824340903422213)
        ·
          refine ⟨5227287045154563919391665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27878864240824340903422213 5227287045154563919391665)
          ·
            refine ⟨3920465283865922939543749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5227287045154563919391665 3920465283865922939543749)
            ·
              refine ⟨735087240724860551164453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3920465283865922939543749 735087240724860551164453)
              ·
                refine ⟨137828857635911353343335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 735087240724860551164453 137828857635911353343335)
                ·
                  rfl

theorem cell20_905920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_905920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905920 prefixEnd_905920 := by exact prefixLift 905920
  have htrace : WordTrace (prefixWord ++ tailWord_905920) baseStart_905920 baseEnd_905920 := by
    simpa [prefixWord, tailWord_905920, baseEnd_905920] using wordTrace_append hprefix tailTrace_905920
  have hstable : (prefixWord ++ tailWord_905920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905920).length < 2 ^ (prefixWord ++ tailWord_905920).sum := by decide
  have hdescent : baseEnd_905920 < baseStart_905920 := by decide
  rcases family_descends (prefixWord ++ tailWord_905920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
