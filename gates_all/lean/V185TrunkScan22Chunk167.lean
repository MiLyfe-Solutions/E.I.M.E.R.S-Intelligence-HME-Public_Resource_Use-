import V185TrunkScan22Chunk166

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1490488 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 2, 3]
def baseStart_1490488 : Nat := 118140960795 + 1490488 * 2 ^ 59
def prefixEnd_1490488 : Nat := 4983230072969 + 3 ^ 40 * 1490488 * 2
def baseEnd_1490488 : Nat := 510224502505779795030251

theorem tailTrace_1490488 : CollatzResearch.WordTrace tailWord_1490488 prefixEnd_1490488 510224502505779795030251 := by
  unfold tailWord_1490488
  simp only [CollatzResearch.WordTrace]
  refine ⟨27181281712112002964672059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36241708949482670619562745 27181281712112002964672059)
  ·
    refine ⟨40771922568168004447008089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27181281712112002964672059 40771922568168004447008089)
    ·
      refine ⟨30578941926126003335256067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40771922568168004447008089 30578941926126003335256067)
      ·
        refine ⟨45868412889189005002884101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30578941926126003335256067 45868412889189005002884101)
        ·
          refine ⟨8600327416722938438040769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45868412889189005002884101 8600327416722938438040769)
          ·
            refine ⟨6450245562542203828530577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8600327416722938438040769 6450245562542203828530577)
            ·
              refine ⟨4837684171906652871397933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6450245562542203828530577 4837684171906652871397933)
              ·
                refine ⟨1814131564464994826774225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4837684171906652871397933 1814131564464994826774225)
                ·
                  refine ⟨1360598673348746120080669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1814131564464994826774225 1360598673348746120080669)
                  ·
                    refine ⟨510224502505779795030251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360598673348746120080669 510224502505779795030251)
                    ·
                      rfl

theorem cell22_1490488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_1490488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490488 prefixEnd_1490488 := by exact prefixLift 1490488
  have htrace : WordTrace (prefixWord ++ tailWord_1490488) baseStart_1490488 baseEnd_1490488 := by
    simpa [prefixWord, tailWord_1490488, baseEnd_1490488] using wordTrace_append hprefix tailTrace_1490488
  have hstable : (prefixWord ++ tailWord_1490488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490488).length < 2 ^ (prefixWord ++ tailWord_1490488).sum := by decide
  have hdescent : baseEnd_1490488 < baseStart_1490488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490501 : List Nat := [1, 3, 1, 1, 1, 4, 5, 6]
def baseStart_1490501 : Nat := 118140960795 + 1490501 * 2 ^ 59
def prefixEnd_1490501 : Nat := 4983230072969 + 3 ^ 40 * 1490501 * 2
def baseEnd_1490501 : Nat := 56692105852383566050579

theorem tailTrace_1490501 : CollatzResearch.WordTrace tailWord_1490501 prefixEnd_1490501 56692105852383566050579 := by
  unfold tailWord_1490501
  simp only [CollatzResearch.WordTrace]
  refine ⟨54363037573176909149567357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36242025048784606099711571 54363037573176909149567357)
  ·
    refine ⟨20386139089941340931087759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54363037573176909149567357 20386139089941340931087759)
    ·
      refine ⟨30579208634912011396631639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20386139089941340931087759 30579208634912011396631639)
      ·
        refine ⟨45868812952368017094947459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30579208634912011396631639 45868812952368017094947459)
        ·
          refine ⟨68803219428552025642421189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45868812952368017094947459 68803219428552025642421189)
          ·
            refine ⟨12900603642853504807953973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68803219428552025642421189 12900603642853504807953973)
            ·
              refine ⟨1209431591517516075745685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12900603642853504807953973 1209431591517516075745685)
              ·
                refine ⟨56692105852383566050579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1209431591517516075745685 56692105852383566050579)
                ·
                  rfl

theorem cell22_1490501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 6].length) (baseStart_1490501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490501 prefixEnd_1490501 := by exact prefixLift 1490501
  have htrace : WordTrace (prefixWord ++ tailWord_1490501) baseStart_1490501 baseEnd_1490501 := by
    simpa [prefixWord, tailWord_1490501, baseEnd_1490501] using wordTrace_append hprefix tailTrace_1490501
  have hstable : (prefixWord ++ tailWord_1490501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490501).length < 2 ^ (prefixWord ++ tailWord_1490501).sum := by decide
  have hdescent : baseEnd_1490501 < baseStart_1490501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490509 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1490509 : Nat := 118140960795 + 1490509 * 2 ^ 59
def prefixEnd_1490509 : Nat := 4983230072969 + 3 ^ 40 * 1490509 * 2
def baseEnd_1490509 : Nat := 510231691234942740255187

theorem tailTrace_1490509 : CollatzResearch.WordTrace tailWord_1490509 prefixEnd_1490509 510231691234942740255187 := by
  unfold tailWord_1490509
  simp only [CollatzResearch.WordTrace]
  refine ⟨54363329357147926515858581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36242219571431951010572387 54363329357147926515858581)
  ·
    refine ⟨2548281063616309055430871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54363329357147926515858581 2548281063616309055430871)
    ·
      refine ⟨3822421595424463583146307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2548281063616309055430871 3822421595424463583146307)
      ·
        refine ⟨5733632393136695374719461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3822421595424463583146307 5733632393136695374719461)
        ·
          refine ⟨1075056073713130382759899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5733632393136695374719461 1075056073713130382759899)
          ·
            refine ⟨1612584110569695574139849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075056073713130382759899 1612584110569695574139849)
            ·
              refine ⟨1209438082927271680604887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1612584110569695574139849 1209438082927271680604887)
              ·
                refine ⟨1814157124390907520907331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209438082927271680604887 1814157124390907520907331)
                ·
                  refine ⟨2721235686586361281360997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814157124390907520907331 2721235686586361281360997)
                  ·
                    refine ⟨510231691234942740255187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2721235686586361281360997 510231691234942740255187)
                    ·
                      rfl

theorem cell22_1490509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1490509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490509 prefixEnd_1490509 := by exact prefixLift 1490509
  have htrace : WordTrace (prefixWord ++ tailWord_1490509) baseStart_1490509 baseEnd_1490509 := by
    simpa [prefixWord, tailWord_1490509, baseEnd_1490509] using wordTrace_append hprefix tailTrace_1490509
  have hstable : (prefixWord ++ tailWord_1490509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490509).length < 2 ^ (prefixWord ++ tailWord_1490509).sum := by decide
  have hdescent : baseEnd_1490509 < baseStart_1490509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490533 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 3, 3]
def baseStart_1490533 : Nat := 118140960795 + 1490533 * 2 ^ 59
def prefixEnd_1490533 : Nat := 4983230072969 + 3 ^ 40 * 1490533 * 2
def baseEnd_1490533 : Nat := 510239906925414677655113

theorem tailTrace_1490533 : CollatzResearch.WordTrace tailWord_1490533 prefixEnd_1490533 510239906925414677655113 := by
  unfold tailWord_1490533
  simp only [CollatzResearch.WordTrace]
  refine ⟨54364204709060978614732253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36242803139373985743154835 54364204709060978614732253)
  ·
    refine ⟨20386576765897866980524595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54364204709060978614732253 20386576765897866980524595)
    ·
      refine ⟨30579865148846800470786893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20386576765897866980524595 30579865148846800470786893)
      ·
        refine ⟨11467449430817550176545085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30579865148846800470786893 11467449430817550176545085)
        ·
          refine ⟨4300293536556581316204407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11467449430817550176545085 4300293536556581316204407)
          ·
            refine ⟨6450440304834871974306611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300293536556581316204407 6450440304834871974306611)
            ·
              refine ⟨9675660457252307961459917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6450440304834871974306611 9675660457252307961459917)
              ·
                refine ⟨3628372671469615485547469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9675660457252307961459917 3628372671469615485547469)
                ·
                  refine ⟨1360639751801105807080301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3628372671469615485547469 1360639751801105807080301)
                  ·
                    refine ⟨510239906925414677655113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360639751801105807080301 510239906925414677655113)
                    ·
                      rfl

theorem cell22_1490533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_1490533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490533 prefixEnd_1490533 := by exact prefixLift 1490533
  have htrace : WordTrace (prefixWord ++ tailWord_1490533) baseStart_1490533 baseEnd_1490533 := by
    simpa [prefixWord, tailWord_1490533, baseEnd_1490533] using wordTrace_append hprefix tailTrace_1490533
  have hstable : (prefixWord ++ tailWord_1490533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490533).length < 2 ^ (prefixWord ++ tailWord_1490533).sum := by decide
  have hdescent : baseEnd_1490533 < baseStart_1490533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490550 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_1490550 : Nat := 118140960795 + 1490550 * 2 ^ 59
def prefixEnd_1490550 : Nat := 4983230072969 + 3 ^ 40 * 1490550 * 2
def baseEnd_1490550 : Nat := 510245726372832299980061

theorem tailTrace_1490550 : CollatzResearch.WordTrace tailWord_1490550 prefixEnd_1490550 510245726372832299980061 := by
  unfold tailWord_1490550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3397801546874961907381319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36243216499999593678734069 3397801546874961907381319)
  ·
    refine ⟨5096702320312442861071979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3397801546874961907381319 5096702320312442861071979)
    ·
      refine ⟨7645053480468664291607969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5096702320312442861071979 7645053480468664291607969)
      ·
        refine ⟨5733790110351498218705977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7645053480468664291607969 5733790110351498218705977)
        ·
          refine ⟨4300342582763623664029483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5733790110351498218705977 4300342582763623664029483)
          ·
            refine ⟨6450513874145435496044225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300342582763623664029483 6450513874145435496044225)
            ·
              refine ⟨4837885405609076622033169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6450513874145435496044225 4837885405609076622033169)
              ·
                refine ⟨3628414054206807466524877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4837885405609076622033169 3628414054206807466524877)
                ·
                  refine ⟨1360655270327552799946829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3628414054206807466524877 1360655270327552799946829)
                  ·
                    refine ⟨510245726372832299980061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360655270327552799946829 510245726372832299980061)
                    ·
                      rfl

theorem cell22_1490550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_1490550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490550 prefixEnd_1490550 := by exact prefixLift 1490550
  have htrace : WordTrace (prefixWord ++ tailWord_1490550) baseStart_1490550 baseEnd_1490550 := by
    simpa [prefixWord, tailWord_1490550, baseEnd_1490550] using wordTrace_append hprefix tailTrace_1490550
  have hstable : (prefixWord ++ tailWord_1490550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490550).length < 2 ^ (prefixWord ++ tailWord_1490550).sum := by decide
  have hdescent : baseEnd_1490550 < baseStart_1490550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490567 : List Nat := [1, 1, 4, 2, 1, 5, 1, 3, 1, 3]
def baseStart_1490567 : Nat := 118140960795 + 1490567 * 2 ^ 59
def prefixEnd_1490567 : Nat := 4983230072969 + 3 ^ 40 * 1490567 * 2
def baseEnd_1490567 : Nat := 510251545820249922305009

theorem tailTrace_1490567 : CollatzResearch.WordTrace tailWord_1490567 prefixEnd_1490567 510251545820249922305009 := by
  unfold tailWord_1490567
  simp only [CollatzResearch.WordTrace]
  refine ⟨54365444790937802421469955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36243629860625201614313303 54365444790937802421469955)
  ·
    refine ⟨81548167186406703632204933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54365444790937802421469955 81548167186406703632204933)
    ·
      refine ⟨15290281347451256931038425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81548167186406703632204933 15290281347451256931038425)
      ·
        refine ⟨11467711010588442698278819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15290281347451256931038425 11467711010588442698278819)
        ·
          refine ⟨17201566515882664047418229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11467711010588442698278819 17201566515882664047418229)
          ·
            refine ⟨1612646860863999754445459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17201566515882664047418229 1612646860863999754445459)
            ·
              refine ⟨2418970291295999631668189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612646860863999754445459 2418970291295999631668189)
              ·
                refine ⟨907113859235999861875571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2418970291295999631668189 907113859235999861875571)
                ·
                  refine ⟨1360670788853999792813357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907113859235999861875571 1360670788853999792813357)
                  ·
                    refine ⟨510251545820249922305009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360670788853999792813357 510251545820249922305009)
                    ·
                      rfl

theorem cell22_1490567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_1490567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490567 prefixEnd_1490567 := by exact prefixLift 1490567
  have htrace : WordTrace (prefixWord ++ tailWord_1490567) baseStart_1490567 baseEnd_1490567 := by
    simpa [prefixWord, tailWord_1490567, baseEnd_1490567] using wordTrace_append hprefix tailTrace_1490567
  have hstable : (prefixWord ++ tailWord_1490567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490567).length < 2 ^ (prefixWord ++ tailWord_1490567).sum := by decide
  have hdescent : baseEnd_1490567 < baseStart_1490567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490636 : List Nat := [2, 2, 1, 5, 12]
def baseStart_1490636 : Nat := 118140960795 + 1490636 * 2 ^ 59
def prefixEnd_1490636 : Nat := 4983230072969 + 3 ^ 40 * 1490636 * 2
def baseEnd_1490636 : Nat := 2099897802182538034279

theorem tailTrace_1490636 : CollatzResearch.WordTrace tailWord_1490636 prefixEnd_1490636 2099897802182538034279 := by
  unfold tailWord_1490636
  simp only [CollatzResearch.WordTrace]
  refine ⟨27183980713843913602865881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36245307618458551470487841 27183980713843913602865881)
  ·
    refine ⟨20387985535382935202149411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27183980713843913602865881 20387985535382935202149411)
    ·
      refine ⟨30581978303074402803224117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20387985535382935202149411 30581978303074402803224117)
      ·
        refine ⟨2867060465913225262802261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30581978303074402803224117 2867060465913225262802261)
        ·
          refine ⟨2099897802182538034279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2867060465913225262802261 2099897802182538034279)
          ·
            rfl

theorem cell22_1490636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 12].length) (baseStart_1490636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490636 prefixEnd_1490636 := by exact prefixLift 1490636
  have htrace : WordTrace (prefixWord ++ tailWord_1490636) baseStart_1490636 baseEnd_1490636 := by
    simpa [prefixWord, tailWord_1490636, baseEnd_1490636] using wordTrace_append hprefix tailTrace_1490636
  have hstable : (prefixWord ++ tailWord_1490636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490636).length < 2 ^ (prefixWord ++ tailWord_1490636).sum := by decide
  have hdescent : baseEnd_1490636 < baseStart_1490636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490638 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1490638 : Nat := 118140960795 + 1490638 * 2 ^ 59
def prefixEnd_1490638 : Nat := 4983230072969 + 3 ^ 40 * 1490638 * 2
def baseEnd_1490638 : Nat := 510275850571229403779791

theorem tailTrace_1490638 : CollatzResearch.WordTrace tailWord_1490638 prefixEnd_1490638 510275850571229403779791 := by
  unfold tailWord_1490638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6796004296710072693413071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36245356249120387698203045 6796004296710072693413071)
  ·
    refine ⟨10194006445065109040119607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6796004296710072693413071 10194006445065109040119607)
    ·
      refine ⟨15291009667597663560179411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10194006445065109040119607 15291009667597663560179411)
      ·
        refine ⟨22936514501396495340269117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15291009667597663560179411 22936514501396495340269117)
        ·
          refine ⟨8601192938023685752600919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22936514501396495340269117 8601192938023685752600919)
          ·
            refine ⟨12901789407035528628901379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8601192938023685752600919 12901789407035528628901379)
            ·
              refine ⟨19352684110553292943352069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12901789407035528628901379 19352684110553292943352069)
              ·
                refine ⟨3628628270728742426878513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19352684110553292943352069 3628628270728742426878513)
                ·
                  refine ⟨2721471203046556820158885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3628628270728742426878513 2721471203046556820158885)
                  ·
                    refine ⟨510275850571229403779791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2721471203046556820158885 510275850571229403779791)
                    ·
                      rfl

theorem cell22_1490638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1490638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490638 prefixEnd_1490638 := by exact prefixLift 1490638
  have htrace : WordTrace (prefixWord ++ tailWord_1490638) baseStart_1490638 baseEnd_1490638 := by
    simpa [prefixWord, tailWord_1490638, baseEnd_1490638] using wordTrace_append hprefix tailTrace_1490638
  have hstable : (prefixWord ++ tailWord_1490638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490638).length < 2 ^ (prefixWord ++ tailWord_1490638).sum := by decide
  have hdescent : baseEnd_1490638 < baseStart_1490638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490642 : List Nat := [3, 2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_1490642 : Nat := 118140960795 + 1490642 * 2 ^ 59
def prefixEnd_1490642 : Nat := 4983230072969 + 3 ^ 40 * 1490642 * 2
def baseEnd_1490642 : Nat := 170092406617658242226593

theorem tailTrace_1490642 : CollatzResearch.WordTrace tailWord_1490642 prefixEnd_1490642 170092406617658242226593 := by
  unfold tailWord_1490642
  simp only [CollatzResearch.WordTrace]
  refine ⟨13592045066416522557612545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36245453510444060153633453 13592045066416522557612545)
  ·
    refine ⟨10194033799812391918209409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13592045066416522557612545 10194033799812391918209409)
    ·
      refine ⟨7645525349859293938657057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10194033799812391918209409 7645525349859293938657057)
      ·
        refine ⟨5734144012394470453992793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7645525349859293938657057 5734144012394470453992793)
        ·
          refine ⟨4300608009295852840494595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5734144012394470453992793 4300608009295852840494595)
          ·
            refine ⟨6450912013943779260741893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300608009295852840494595 6450912013943779260741893)
            ·
              refine ⟨1209546002614458611389105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6450912013943779260741893 1209546002614458611389105)
              ·
                refine ⟨907159501960843958541829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1209546002614458611389105 907159501960843958541829)
                ·
                  refine ⟨170092406617658242226593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 907159501960843958541829 170092406617658242226593)
                  ·
                    rfl

theorem cell22_1490642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_1490642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490642 prefixEnd_1490642 := by exact prefixLift 1490642
  have htrace : WordTrace (prefixWord ++ tailWord_1490642) baseStart_1490642 baseEnd_1490642 := by
    simpa [prefixWord, tailWord_1490642, baseEnd_1490642] using wordTrace_append hprefix tailTrace_1490642
  have hstable : (prefixWord ++ tailWord_1490642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490642).length < 2 ^ (prefixWord ++ tailWord_1490642).sum := by decide
  have hdescent : baseEnd_1490642 < baseStart_1490642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490668 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 5, 3]
def baseStart_1490668 : Nat := 118140960795 + 1490668 * 2 ^ 59
def prefixEnd_1490668 : Nat := 4983230072969 + 3 ^ 40 * 1490668 * 2
def baseEnd_1490668 : Nat := 510286120184319325529699

theorem tailTrace_1490668 : CollatzResearch.WordTrace tailWord_1490668 prefixEnd_1490668 510286120184319325529699 := by
  unfold tailWord_1490668
  simp only [CollatzResearch.WordTrace]
  refine ⟨27184564281785948335448329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36246085709047931113931105 27184564281785948335448329)
  ·
    refine ⟨20388423211339461251586247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27184564281785948335448329 20388423211339461251586247)
    ·
      refine ⟨30582634817009191877379371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20388423211339461251586247 30582634817009191877379371)
      ·
        refine ⟨45873952225513787816069057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30582634817009191877379371 45873952225513787816069057)
        ·
          refine ⟨34405464169135340862051793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45873952225513787816069057 34405464169135340862051793)
          ·
            refine ⟨25804098126851505646538845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34405464169135340862051793 25804098126851505646538845)
            ·
              refine ⟨9676536797569314617452067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25804098126851505646538845 9676536797569314617452067)
              ·
                refine ⟨14514805196353971926178101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9676536797569314617452067 14514805196353971926178101)
                ·
                  refine ⟨1360762987158184868079197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14514805196353971926178101 1360762987158184868079197)
                  ·
                    refine ⟨510286120184319325529699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360762987158184868079197 510286120184319325529699)
                    ·
                      rfl

theorem cell22_1490668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_1490668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490668 prefixEnd_1490668 := by exact prefixLift 1490668
  have htrace : WordTrace (prefixWord ++ tailWord_1490668) baseStart_1490668 baseEnd_1490668 := by
    simpa [prefixWord, tailWord_1490668, baseEnd_1490668] using wordTrace_append hprefix tailTrace_1490668
  have hstable : (prefixWord ++ tailWord_1490668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490668).length < 2 ^ (prefixWord ++ tailWord_1490668).sum := by decide
  have hdescent : baseEnd_1490668 < baseStart_1490668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490698 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_1490698 : Nat := 118140960795 + 1490698 * 2 ^ 59
def prefixEnd_1490698 : Nat := 4983230072969 + 3 ^ 40 * 1490698 * 2
def baseEnd_1490698 : Nat := 170098796599136415759869

theorem tailTrace_1490698 : CollatzResearch.WordTrace tailWord_1490698 prefixEnd_1490698 170098796599136415759869 := by
  unfold tailWord_1490698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13592555688365802948622187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36246815168975474529659165 13592555688365802948622187)
  ·
    refine ⟨20388833532548704422933281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13592555688365802948622187 20388833532548704422933281)
    ·
      refine ⟨15291625149411528317199961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20388833532548704422933281 15291625149411528317199961)
      ·
        refine ⟨11468718862058646237899971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15291625149411528317199961 11468718862058646237899971)
        ·
          refine ⟨17203078293087969356849957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11468718862058646237899971 17203078293087969356849957)
          ·
            refine ⟨3225577179953994254409367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17203078293087969356849957 3225577179953994254409367)
            ·
              refine ⟨4838365769930991381614051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3225577179953994254409367 4838365769930991381614051)
              ·
                refine ⟨7257548654896487072421077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4838365769930991381614051 7257548654896487072421077)
                ·
                  refine ⟨170098796599136415759869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7257548654896487072421077 170098796599136415759869)
                  ·
                    rfl

theorem cell22_1490698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_1490698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490698 prefixEnd_1490698 := by exact prefixLift 1490698
  have htrace : WordTrace (prefixWord ++ tailWord_1490698) baseStart_1490698 baseEnd_1490698 := by
    simpa [prefixWord, tailWord_1490698, baseEnd_1490698] using wordTrace_append hprefix tailTrace_1490698
  have hstable : (prefixWord ++ tailWord_1490698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490698).length < 2 ^ (prefixWord ++ tailWord_1490698).sum := by decide
  have hdescent : baseEnd_1490698 < baseStart_1490698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490702 : List Nat := [4, 1, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_1490702 : Nat := 118140960795 + 1490702 * 2 ^ 59
def prefixEnd_1490702 : Nat := 4983230072969 + 3 ^ 40 * 1490702 * 2
def baseEnd_1490702 : Nat := 510297759079154570179595

theorem tailTrace_1490702 : CollatzResearch.WordTrace tailWord_1490702 prefixEnd_1490702 510297759079154570179595 := by
  unfold tailWord_1490702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6796296080681090059704295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36246912430299146985089573 6796296080681090059704295)
  ·
    refine ⟨10194444121021635089556443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6796296080681090059704295 10194444121021635089556443)
    ·
      refine ⟨15291666181532452634334665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10194444121021635089556443 15291666181532452634334665)
      ·
        refine ⟨11468749636149339475750999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15291666181532452634334665 11468749636149339475750999)
        ·
          refine ⟨17203124454224009213626499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11468749636149339475750999 17203124454224009213626499)
          ·
            refine ⟨25804686681336013820439749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17203124454224009213626499 25804686681336013820439749)
            ·
              refine ⟨4838378752750502591332453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25804686681336013820439749 4838378752750502591332453)
              ·
                refine ⟨907196016140719235874835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4838378752750502591332453 907196016140719235874835)
                ·
                  refine ⟨1360794024211078853812253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907196016140719235874835 1360794024211078853812253)
                  ·
                    refine ⟨510297759079154570179595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360794024211078853812253 510297759079154570179595)
                    ·
                      rfl

theorem cell22_1490702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_1490702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490702 prefixEnd_1490702 := by exact prefixLift 1490702
  have htrace : WordTrace (prefixWord ++ tailWord_1490702) baseStart_1490702 baseEnd_1490702 := by
    simpa [prefixWord, tailWord_1490702, baseEnd_1490702] using wordTrace_append hprefix tailTrace_1490702
  have hstable : (prefixWord ++ tailWord_1490702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490702).length < 2 ^ (prefixWord ++ tailWord_1490702).sum := by decide
  have hdescent : baseEnd_1490702 < baseStart_1490702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490708 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1490708 : Nat := 118140960795 + 1490708 * 2 ^ 59
def prefixEnd_1490708 : Nat := 4983230072969 + 3 ^ 40 * 1490708 * 2
def baseEnd_1490708 : Nat := 510299813001772554529577

theorem tailTrace_1490708 : CollatzResearch.WordTrace tailWord_1490708 prefixEnd_1490708 510299813001772554529577 := by
  unfold tailWord_1490708
  simp only [CollatzResearch.WordTrace]
  refine ⟨27185293741713491751176389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36247058322284655668235185 27185293741713491751176389)
  ·
    refine ⟨5097242576571279703345573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27185293741713491751176389 5097242576571279703345573)
    ·
      refine ⟨955732983107114944377295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5097242576571279703345573 955732983107114944377295)
      ·
        refine ⟨1433599474660672416565943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955732983107114944377295 1433599474660672416565943)
        ·
          refine ⟨2150399211991008624848915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433599474660672416565943 2150399211991008624848915)
          ·
            refine ⟨3225598817986512937273373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150399211991008624848915 3225598817986512937273373)
            ·
              refine ⟨1209599556744942351477515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3225598817986512937273373 1209599556744942351477515)
              ·
                refine ⟨1814399335117413527216273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209599556744942351477515 1814399335117413527216273)
                ·
                  refine ⟨1360799501338060145412205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1814399335117413527216273 1360799501338060145412205)
                  ·
                    refine ⟨510299813001772554529577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360799501338060145412205 510299813001772554529577)
                    ·
                      rfl

theorem cell22_1490708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1490708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490708 prefixEnd_1490708 := by exact prefixLift 1490708
  have htrace : WordTrace (prefixWord ++ tailWord_1490708) baseStart_1490708 baseEnd_1490708 := by
    simpa [prefixWord, tailWord_1490708, baseEnd_1490708] using wordTrace_append hprefix tailTrace_1490708
  have hstable : (prefixWord ++ tailWord_1490708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490708).length < 2 ^ (prefixWord ++ tailWord_1490708).sum := by decide
  have hdescent : baseEnd_1490708 < baseStart_1490708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490760 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 6]
def baseStart_1490760 : Nat := 118140960795 + 1490760 * 2 ^ 59
def prefixEnd_1490760 : Nat := 4983230072969 + 3 ^ 40 * 1490760 * 2
def baseEnd_1490760 : Nat := 170105871221487250743139

theorem tailTrace_1490760 : CollatzResearch.WordTrace tailWord_1490760 prefixEnd_1490760 170105871221487250743139 := by
  unfold tailWord_1490760
  simp only [CollatzResearch.WordTrace]
  refine ⟨27186242039619298191622867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36248322719492397588830489 27186242039619298191622867)
  ·
    refine ⟨40779363059428947287434301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27186242039619298191622867 40779363059428947287434301)
    ·
      refine ⟨15292261147285855232787863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40779363059428947287434301 15292261147285855232787863)
      ·
        refine ⟨22938391720928782849181795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15292261147285855232787863 22938391720928782849181795)
        ·
          refine ⟨34407587581393174273772693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22938391720928782849181795 34407587581393174273772693)
          ·
            refine ⟨1612855667877805044083095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34407587581393174273772693 1612855667877805044083095)
            ·
              refine ⟨2419283501816707566124643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612855667877805044083095 2419283501816707566124643)
              ·
                refine ⟨3628925252725061349186965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419283501816707566124643 3628925252725061349186965)
                ·
                  refine ⟨170105871221487250743139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3628925252725061349186965 170105871221487250743139)
                  ·
                    rfl

theorem cell22_1490760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 6].length) (baseStart_1490760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490760 prefixEnd_1490760 := by exact prefixLift 1490760
  have htrace : WordTrace (prefixWord ++ tailWord_1490760) baseStart_1490760 baseEnd_1490760 := by
    simpa [prefixWord, tailWord_1490760, baseEnd_1490760] using wordTrace_append hprefix tailTrace_1490760
  have hstable : (prefixWord ++ tailWord_1490760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490760).length < 2 ^ (prefixWord ++ tailWord_1490760).sum := by decide
  have hdescent : baseEnd_1490760 < baseStart_1490760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490848 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_1490848 : Nat := 118140960795 + 1490848 * 2 ^ 59
def prefixEnd_1490848 : Nat := 4983230072969 + 3 ^ 40 * 1490848 * 2
def baseEnd_1490848 : Nat := 510347737862858856029147

theorem tailTrace_1490848 : CollatzResearch.WordTrace tailWord_1490848 prefixEnd_1490848 510347737862858856029147 := by
  unfold tailWord_1490848
  simp only [CollatzResearch.WordTrace]
  refine ⟨27187846851459893706224599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36250462468613191608299465 27187846851459893706224599)
  ·
    refine ⟨40781770277189840559336899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27187846851459893706224599 40781770277189840559336899)
    ·
      refine ⟨61172655415784760839005349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40781770277189840559336899 61172655415784760839005349)
      ·
        refine ⟨11469872890459642657313503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61172655415784760839005349 11469872890459642657313503)
        ·
          refine ⟨17204809335689463985970255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11469872890459642657313503 17204809335689463985970255)
          ·
            refine ⟨25807214003534195978955383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17204809335689463985970255 25807214003534195978955383)
            ·
              refine ⟨38710821005301293968433075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25807214003534195978955383 38710821005301293968433075)
              ·
                refine ⟨58066231507951940952649613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38710821005301293968433075 58066231507951940952649613)
                ·
                  refine ⟨21774836815481977857243605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58066231507951940952649613 21774836815481977857243605)
                  ·
                    refine ⟨510347737862858856029147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21774836815481977857243605 510347737862858856029147)
                    ·
                      rfl

theorem cell22_1490848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_1490848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490848 prefixEnd_1490848 := by exact prefixLift 1490848
  have htrace : WordTrace (prefixWord ++ tailWord_1490848) baseStart_1490848 baseEnd_1490848 := by
    simpa [prefixWord, tailWord_1490848, baseEnd_1490848] using wordTrace_append hprefix tailTrace_1490848
  have hstable : (prefixWord ++ tailWord_1490848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490848).length < 2 ^ (prefixWord ++ tailWord_1490848).sum := by decide
  have hdescent : baseEnd_1490848 < baseStart_1490848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490865 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_1490865 : Nat := 118140960795 + 1490865 * 2 ^ 59
def prefixEnd_1490865 : Nat := 4983230072969 + 3 ^ 40 * 1490865 * 2
def baseEnd_1490865 : Nat := 510353557310276478354095

theorem tailTrace_1490865 : CollatzResearch.WordTrace tailWord_1490865 prefixEnd_1490865 510353557310276478354095 := by
  unfold tailWord_1490865
  simp only [CollatzResearch.WordTrace]
  refine ⟨54376313743858199315818049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36250875829238799543878699 54376313743858199315818049)
  ·
    refine ⟨40782235307893649486863537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54376313743858199315818049 40782235307893649486863537)
    ·
      refine ⟨30586676480920237115147653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40782235307893649486863537 30586676480920237115147653)
      ·
        refine ⟨5735001840172544459090185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30586676480920237115147653 5735001840172544459090185)
        ·
          refine ⟨4301251380129408344317639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5735001840172544459090185 4301251380129408344317639)
          ·
            refine ⟨6451877070194112516476459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301251380129408344317639 6451877070194112516476459)
            ·
              refine ⟨9677815605291168774714689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451877070194112516476459 9677815605291168774714689)
              ·
                refine ⟨7258361703968376581036017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9677815605291168774714689 7258361703968376581036017)
                ·
                  refine ⟨5443771277976282435777013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7258361703968376581036017 5443771277976282435777013)
                  ·
                    refine ⟨510353557310276478354095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5443771277976282435777013 510353557310276478354095)
                    ·
                      rfl

theorem cell22_1490865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_1490865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490865 prefixEnd_1490865 := by exact prefixLift 1490865
  have htrace : WordTrace (prefixWord ++ tailWord_1490865) baseStart_1490865 baseEnd_1490865 := by
    simpa [prefixWord, tailWord_1490865, baseEnd_1490865] using wordTrace_append hprefix tailTrace_1490865
  have hstable : (prefixWord ++ tailWord_1490865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490865).length < 2 ^ (prefixWord ++ tailWord_1490865).sum := by decide
  have hdescent : baseEnd_1490865 < baseStart_1490865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490927 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 2, 3]
def baseStart_1490927 : Nat := 118140960795 + 1490927 * 2 ^ 59
def prefixEnd_1490927 : Nat := 4983230072969 + 3 ^ 40 * 1490927 * 2
def baseEnd_1490927 : Nat := 510374781177328983303905

theorem tailTrace_1490927 : CollatzResearch.WordTrace tailWord_1490927 prefixEnd_1490927 510374781177328983303905 := by
  unfold tailWord_1490927
  simp only [CollatzResearch.WordTrace]
  refine ⟨54378575069633583904575035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36252383379755722603050023 54378575069633583904575035)
  ·
    refine ⟨81567862604450375856862553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54378575069633583904575035 81567862604450375856862553)
    ·
      refine ⟨61175896953337781892646915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81567862604450375856862553 61175896953337781892646915)
      ·
        refine ⟨91763845430006672838970373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61175896953337781892646915 91763845430006672838970373)
        ·
          refine ⟨17205721018126251157306945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91763845430006672838970373 17205721018126251157306945)
          ·
            refine ⟨12904290763594688367980209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17205721018126251157306945 12904290763594688367980209)
            ·
              refine ⟨9678218072696016275985157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12904290763594688367980209 9678218072696016275985157)
              ·
                refine ⟨1814665888630503051747217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9678218072696016275985157 1814665888630503051747217)
                ·
                  refine ⟨1360999416472877288810413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1814665888630503051747217 1360999416472877288810413)
                  ·
                    refine ⟨510374781177328983303905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360999416472877288810413 510374781177328983303905)
                    ·
                      rfl

theorem cell22_1490927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 3].length) (baseStart_1490927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490927 prefixEnd_1490927 := by exact prefixLift 1490927
  have htrace : WordTrace (prefixWord ++ tailWord_1490927) baseStart_1490927 baseEnd_1490927 := by
    simpa [prefixWord, tailWord_1490927, baseEnd_1490927] using wordTrace_append hprefix tailTrace_1490927
  have hstable : (prefixWord ++ tailWord_1490927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490927).length < 2 ^ (prefixWord ++ tailWord_1490927).sum := by decide
  have hdescent : baseEnd_1490927 < baseStart_1490927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490929 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 6]
def baseStart_1490929 : Nat := 118140960795 + 1490929 * 2 ^ 59
def prefixEnd_1490929 : Nat := 4983230072969 + 3 ^ 40 * 1490929 * 2
def baseEnd_1490929 : Nat := 170125155272733881584633

theorem tailTrace_1490929 : CollatzResearch.WordTrace tailWord_1490929 prefixEnd_1490929 170125155272733881584633 := by
  unfold tailWord_1490929
  simp only [CollatzResearch.WordTrace]
  refine ⟨54378648015626338246147841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36252432010417558830765227 54378648015626338246147841)
  ·
    refine ⟨40783986011719753684610881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54378648015626338246147841 40783986011719753684610881)
    ·
      refine ⟨30587989508789815263458161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40783986011719753684610881 30587989508789815263458161)
      ·
        refine ⟨22940992131592361447593621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30587989508789815263458161 22940992131592361447593621)
        ·
          refine ⟨1075359006168391942855951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22940992131592361447593621 1075359006168391942855951)
          ·
            refine ⟨1613038509252587914283927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075359006168391942855951 1613038509252587914283927)
            ·
              refine ⟨2419557763878881871425891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613038509252587914283927 2419557763878881871425891)
              ·
                refine ⟨3629336645818322807138837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419557763878881871425891 3629336645818322807138837)
                ·
                  refine ⟨170125155272733881584633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3629336645818322807138837 170125155272733881584633)
                  ·
                    rfl

theorem cell22_1490929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 6].length) (baseStart_1490929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490929 prefixEnd_1490929 := by exact prefixLift 1490929
  have htrace : WordTrace (prefixWord ++ tailWord_1490929) baseStart_1490929 baseEnd_1490929 := by
    simpa [prefixWord, tailWord_1490929, baseEnd_1490929] using wordTrace_append hprefix tailTrace_1490929
  have hstable : (prefixWord ++ tailWord_1490929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490929).length < 2 ^ (prefixWord ++ tailWord_1490929).sum := by decide
  have hdescent : baseEnd_1490929 < baseStart_1490929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490940 : List Nat := [2, 2, 2, 1, 2, 2, 4, 7]
def baseStart_1490940 : Nat := 118140960795 + 1490940 * 2 ^ 59
def prefixEnd_1490940 : Nat := 4983230072969 + 3 ^ 40 * 1490940 * 2
def baseEnd_1490940 : Nat := 56708803482555698080985

theorem tailTrace_1490940 : CollatzResearch.WordTrace tailWord_1490940 prefixEnd_1490940 56708803482555698080985 := by
  unfold tailWord_1490940
  simp only [CollatzResearch.WordTrace]
  refine ⟨27189524609293243562399137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36252699479057658083198849 27189524609293243562399137)
  ·
    refine ⟨20392143456969932671799353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27189524609293243562399137 20392143456969932671799353)
    ·
      refine ⟨15294107592727449503849515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20392143456969932671799353 15294107592727449503849515)
      ·
        refine ⟨22941161389091174255774273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15294107592727449503849515 22941161389091174255774273)
        ·
          refine ⟨17205871041818380691830705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22941161389091174255774273 17205871041818380691830705)
          ·
            refine ⟨12904403281363785518873029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17205871041818380691830705 12904403281363785518873029)
            ·
              refine ⟨2419575615255709784788693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12904403281363785518873029 2419575615255709784788693)
              ·
                refine ⟨56708803482555698080985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2419575615255709784788693 56708803482555698080985)
                ·
                  rfl

theorem cell22_1490940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 7].length) (baseStart_1490940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490940 prefixEnd_1490940 := by exact prefixLift 1490940
  have htrace : WordTrace (prefixWord ++ tailWord_1490940) baseStart_1490940 baseEnd_1490940 := by
    simpa [prefixWord, tailWord_1490940, baseEnd_1490940] using wordTrace_append hprefix tailTrace_1490940
  have hstable : (prefixWord ++ tailWord_1490940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490940).length < 2 ^ (prefixWord ++ tailWord_1490940).sum := by decide
  have hdescent : baseEnd_1490940 < baseStart_1490940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490948 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_1490948 : Nat := 118140960795 + 1490948 * 2 ^ 59
def prefixEnd_1490948 : Nat := 4983230072969 + 3 ^ 40 * 1490948 * 2
def baseEnd_1490948 : Nat := 510381969906491928528841

theorem tailTrace_1490948 : CollatzResearch.WordTrace tailWord_1490948 prefixEnd_1490948 510381969906491928528841 := by
  unfold tailWord_1490948
  simp only [CollatzResearch.WordTrace]
  refine ⟨27189670501278752245544749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36252894001705002994059665 27189670501278752245544749)
  ·
    refine ⟨10196126437979532092079281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27189670501278752245544749 10196126437979532092079281)
    ·
      refine ⟨7647094828484649069059461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10196126437979532092079281 7647094828484649069059461)
      ·
        refine ⟨1433830280340871700448649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7647094828484649069059461 1433830280340871700448649)
        ·
          refine ⟨1075372710255653775336487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1433830280340871700448649 1075372710255653775336487)
          ·
            refine ⟨1613059065383480663004731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075372710255653775336487 1613059065383480663004731)
            ·
              refine ⟨2419588598075220994507097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613059065383480663004731 2419588598075220994507097)
              ·
                refine ⟨1814691448556415745880323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2419588598075220994507097 1814691448556415745880323)
                ·
                  refine ⟨2722037172834623618820485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814691448556415745880323 2722037172834623618820485)
                  ·
                    refine ⟨510381969906491928528841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2722037172834623618820485 510381969906491928528841)
                    ·
                      rfl

theorem cell22_1490948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_1490948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490948 prefixEnd_1490948 := by exact prefixLift 1490948
  have htrace : WordTrace (prefixWord ++ tailWord_1490948) baseStart_1490948 baseEnd_1490948 := by
    simpa [prefixWord, tailWord_1490948, baseEnd_1490948] using wordTrace_append hprefix tailTrace_1490948
  have hstable : (prefixWord ++ tailWord_1490948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490948).length < 2 ^ (prefixWord ++ tailWord_1490948).sum := by decide
  have hdescent : baseEnd_1490948 < baseStart_1490948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491006 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_1491006 : Nat := 118140960795 + 1491006 * 2 ^ 59
def prefixEnd_1491006 : Nat := 4983230072969 + 3 ^ 40 * 1491006 * 2
def baseEnd_1491006 : Nat := 510401824491799110578663

theorem tailTrace_1491006 : CollatzResearch.WordTrace tailWord_1491006 prefixEnd_1491006 510401824491799110578663 := by
  unfold tailWord_1491006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797682054543422549587609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36254304290898253597800581 6797682054543422549587609)
  ·
    refine ⟨5098261540907566912190707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6797682054543422549587609 5098261540907566912190707)
    ·
      refine ⟨7647392311361350368286061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5098261540907566912190707 7647392311361350368286061)
      ·
        refine ⟨2867772116760506388107273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7647392311361350368286061 2867772116760506388107273)
        ·
          refine ⟨2150829087570379791080455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2867772116760506388107273 2150829087570379791080455)
          ·
            refine ⟨3226243631355569686620683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150829087570379791080455 3226243631355569686620683)
            ·
              refine ⟨4839365447033354529931025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3226243631355569686620683 4839365447033354529931025)
              ·
                refine ⟨3629524085275015897448269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4839365447033354529931025 3629524085275015897448269)
                ·
                  refine ⟨1361071531978130961543101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3629524085275015897448269 1361071531978130961543101)
                  ·
                    refine ⟨510401824491799110578663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1361071531978130961543101 510401824491799110578663)
                    ·
                      rfl

theorem cell22_1491006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_1491006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491006 prefixEnd_1491006 := by exact prefixLift 1491006
  have htrace : WordTrace (prefixWord ++ tailWord_1491006) baseStart_1491006 baseEnd_1491006 := by
    simpa [prefixWord, tailWord_1491006, baseEnd_1491006] using wordTrace_append hprefix tailTrace_1491006
  have hstable : (prefixWord ++ tailWord_1491006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491006).length < 2 ^ (prefixWord ++ tailWord_1491006).sum := by decide
  have hdescent : baseEnd_1491006 < baseStart_1491006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491047 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 6]
def baseStart_1491047 : Nat := 118140960795 + 1491047 * 2 ^ 59
def prefixEnd_1491047 : Nat := 4983230072969 + 3 ^ 40 * 1491047 * 2
def baseEnd_1491047 : Nat := 170138619876562890101179

theorem tailTrace_1491047 : CollatzResearch.WordTrace tailWord_1491047 prefixEnd_1491047 170138619876562890101179 := by
  unfold tailWord_1491047
  simp only [CollatzResearch.WordTrace]
  refine ⟨54382951829198844398943395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36255301219465896265962263 54382951829198844398943395)
  ·
    refine ⟨81574427743798266598415093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54382951829198844398943395 81574427743798266598415093)
    ·
      refine ⟨7647602600981087493601415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81574427743798266598415093 7647602600981087493601415)
      ·
        refine ⟨11471403901471631240402123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7647602600981087493601415 11471403901471631240402123)
        ·
          refine ⟨17207105852207446860603185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11471403901471631240402123 17207105852207446860603185)
          ·
            refine ⟨12905329389155585145452389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17207105852207446860603185 12905329389155585145452389)
            ·
              refine ⟨2419749260466672214772323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12905329389155585145452389 2419749260466672214772323)
              ·
                refine ⟨3629623890700008322158485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419749260466672214772323 3629623890700008322158485)
                ·
                  refine ⟨170138619876562890101179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3629623890700008322158485 170138619876562890101179)
                  ·
                    rfl

theorem cell22_1491047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 6].length) (baseStart_1491047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491047 prefixEnd_1491047 := by exact prefixLift 1491047
  have htrace : WordTrace (prefixWord ++ tailWord_1491047) baseStart_1491047 baseEnd_1491047 := by
    simpa [prefixWord, tailWord_1491047, baseEnd_1491047] using wordTrace_append hprefix tailTrace_1491047
  have hstable : (prefixWord ++ tailWord_1491047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491047).length < 2 ^ (prefixWord ++ tailWord_1491047).sum := by decide
  have hdescent : baseEnd_1491047 < baseStart_1491047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491077 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_1491077 : Nat := 118140960795 + 1491077 * 2 ^ 59
def prefixEnd_1491077 : Nat := 4983230072969 + 3 ^ 40 * 1491077 * 2
def baseEnd_1491077 : Nat := 510426129242778592053445

theorem tailTrace_1491077 : CollatzResearch.WordTrace tailWord_1491077 prefixEnd_1491077 510426129242778592053445 := by
  unfold tailWord_1491077
  simp only [CollatzResearch.WordTrace]
  refine ⟨54384046019090159522535485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36256030679393439681690323 54384046019090159522535485)
  ·
    refine ⟨20394017257158809820950807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54384046019090159522535485 20394017257158809820950807)
    ·
      refine ⟨30591025885738214731426211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20394017257158809820950807 30591025885738214731426211)
      ·
        refine ⟨45886538828607322097139317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30591025885738214731426211 45886538828607322097139317)
        ·
          refine ⟨4301863015181936446606811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45886538828607322097139317 4301863015181936446606811)
          ·
            refine ⟨6452794522772904669910217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301863015181936446606811 6452794522772904669910217)
            ·
              refine ⟨4839595892079678502432663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6452794522772904669910217 4839595892079678502432663)
              ·
                refine ⟨7259393838119517753648995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4839595892079678502432663 7259393838119517753648995)
                ·
                  refine ⟨10889090757179276630473493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7259393838119517753648995 10889090757179276630473493)
                  ·
                    refine ⟨510426129242778592053445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10889090757179276630473493 510426129242778592053445)
                    ·
                      rfl

theorem cell22_1491077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_1491077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491077 prefixEnd_1491077 := by exact prefixLift 1491077
  have htrace : WordTrace (prefixWord ++ tailWord_1491077) baseStart_1491077 baseEnd_1491077 := by
    simpa [prefixWord, tailWord_1491077, baseEnd_1491077] using wordTrace_append hprefix tailTrace_1491077
  have hstable : (prefixWord ++ tailWord_1491077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491077).length < 2 ^ (prefixWord ++ tailWord_1491077).sum := by decide
  have hdescent : baseEnd_1491077 < baseStart_1491077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491098 : List Nat := [3, 1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_1491098 : Nat := 118140960795 + 1491098 * 2 ^ 59
def prefixEnd_1491098 : Nat := 4983230072969 + 3 ^ 40 * 1491098 * 2
def baseEnd_1491098 : Nat := 170144439323980512426127

theorem tailTrace_1491098 : CollatzResearch.WordTrace tailWord_1491098 prefixEnd_1491098 170144439323980512426127 := by
  unfold tailWord_1491098
  simp only [CollatzResearch.WordTrace]
  refine ⟨13596202988003520027262487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36256541301342720072699965 13596202988003520027262487)
  ·
    refine ⟨20394304482005280040893731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13596202988003520027262487 20394304482005280040893731)
    ·
      refine ⟨30591456723007920061340597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20394304482005280040893731 30591456723007920061340597)
      ·
        refine ⟨2867949067781992505750681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30591456723007920061340597 2867949067781992505750681)
        ·
          refine ⟨2150961800836494379313011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2867949067781992505750681 2150961800836494379313011)
          ·
            refine ⟨3226442701254741568969517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150961800836494379313011 3226442701254741568969517)
            ·
              refine ⟨1209916012970528088363569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3226442701254741568969517 1209916012970528088363569)
              ·
                refine ⟨907437009727896066272677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1209916012970528088363569 907437009727896066272677)
                ·
                  refine ⟨170144439323980512426127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 907437009727896066272677 170144439323980512426127)
                  ·
                    rfl

theorem cell22_1491098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_1491098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491098 prefixEnd_1491098 := by exact prefixLift 1491098
  have htrace : WordTrace (prefixWord ++ tailWord_1491098) baseStart_1491098 baseEnd_1491098 := by
    simpa [prefixWord, tailWord_1491098, baseEnd_1491098] using wordTrace_append hprefix tailTrace_1491098
  have hstable : (prefixWord ++ tailWord_1491098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491098).length < 2 ^ (prefixWord ++ tailWord_1491098).sum := by decide
  have hdescent : baseEnd_1491098 < baseStart_1491098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491154 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_1491154 : Nat := 118140960795 + 1491154 * 2 ^ 59
def prefixEnd_1491154 : Nat := 4983230072969 + 3 ^ 40 * 1491154 * 2
def baseEnd_1491154 : Nat := 170150829305458685959403

theorem tailTrace_1491154 : CollatzResearch.WordTrace tailWord_1491154 prefixEnd_1491154 170150829305458685959403 := by
  unfold tailWord_1491154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13596713609952800418272129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36257902959874134448725677 13596713609952800418272129)
  ·
    refine ⟨10197535207464600313704097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13596713609952800418272129 10197535207464600313704097)
    ·
      refine ⟨7648151405598450235278073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10197535207464600313704097 7648151405598450235278073)
      ·
        refine ⟨5736113554198837676458555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7648151405598450235278073 5736113554198837676458555)
        ·
          refine ⟨8604170331298256514687833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5736113554198837676458555 8604170331298256514687833)
          ·
            refine ⟨6453127748473692386015875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8604170331298256514687833 6453127748473692386015875)
            ·
              refine ⟨9679691622710538579023813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453127748473692386015875 9679691622710538579023813)
              ·
                refine ⟨1814942179258225983566965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9679691622710538579023813 1814942179258225983566965)
                ·
                  refine ⟨170150829305458685959403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1814942179258225983566965 170150829305458685959403)
                  ·
                    rfl

theorem cell22_1491154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_1491154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491154 prefixEnd_1491154 := by exact prefixLift 1491154
  have htrace : WordTrace (prefixWord ++ tailWord_1491154) baseStart_1491154 baseEnd_1491154 := by
    simpa [prefixWord, tailWord_1491154, baseEnd_1491154] using wordTrace_append hprefix tailTrace_1491154
  have hstable : (prefixWord ++ tailWord_1491154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491154).length < 2 ^ (prefixWord ++ tailWord_1491154).sum := by decide
  have hdescent : baseEnd_1491154 < baseStart_1491154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491231 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 1, 5]
def baseStart_1491231 : Nat := 118140960795 + 1491231 * 2 ^ 59
def prefixEnd_1491231 : Nat := 4983230072969 + 3 ^ 40 * 1491231 * 2
def baseEnd_1491231 : Nat := 510478846589973523702973

theorem tailTrace_1491231 : CollatzResearch.WordTrace tailWord_1491231 prefixEnd_1491231 510478846589973523702973 := by
  unfold tailWord_1491231
  simp only [CollatzResearch.WordTrace]
  refine ⟨54389662860532243823641547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36259775240354829215761031 54389662860532243823641547)
  ·
    refine ⟨81584494290798365735462321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54389662860532243823641547 81584494290798365735462321)
    ·
      refine ⟨61188370718098774301596741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81584494290798365735462321 61188370718098774301596741)
      ·
        refine ⟨11472819509643520181549389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61188370718098774301596741 11472819509643520181549389)
        ·
          refine ⟨4302307316116320068081021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11472819509643520181549389 4302307316116320068081021)
          ·
            refine ⟨1613365243543620025530383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4302307316116320068081021 1613365243543620025530383)
            ·
              refine ⟨2420047865315430038295575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613365243543620025530383 2420047865315430038295575)
              ·
                refine ⟨3630071797973145057443363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420047865315430038295575 3630071797973145057443363)
                ·
                  refine ⟨5445107696959717586165045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630071797973145057443363 5445107696959717586165045)
                  ·
                    refine ⟨510478846589973523702973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5445107696959717586165045 510478846589973523702973)
                    ·
                      rfl

theorem cell22_1491231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 5].length) (baseStart_1491231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491231 prefixEnd_1491231 := by exact prefixLift 1491231
  have htrace : WordTrace (prefixWord ++ tailWord_1491231) baseStart_1491231 baseEnd_1491231 := by
    simpa [prefixWord, tailWord_1491231, baseEnd_1491231] using wordTrace_append hprefix tailTrace_1491231
  have hstable : (prefixWord ++ tailWord_1491231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491231).length < 2 ^ (prefixWord ++ tailWord_1491231).sum := by decide
  have hdescent : baseEnd_1491231 < baseStart_1491231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491244 : List Nat := [2, 2, 1, 1, 1, 3, 6, 6]
def baseStart_1491244 : Nat := 118140960795 + 1491244 * 2 ^ 59
def prefixEnd_1491244 : Nat := 4983230072969 + 3 ^ 40 * 1491244 * 2
def baseEnd_1491244 : Nat := 56720366306182869236437

theorem tailTrace_1491244 : CollatzResearch.WordTrace tailWord_1491244 prefixEnd_1491244 56720366306182869236437 := by
  unfold tailWord_1491244
  simp only [CollatzResearch.WordTrace]
  refine ⟨27195068504742573521932393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36260091339656764695909857 27195068504742573521932393)
  ·
    refine ⟨20396301378556930141449295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27195068504742573521932393 20396301378556930141449295)
    ·
      refine ⟨30594452067835395212173943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20396301378556930141449295 30594452067835395212173943)
      ·
        refine ⟨45891678101753092818260915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30594452067835395212173943 45891678101753092818260915)
        ·
          refine ⟨68837517152629639227391373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45891678101753092818260915 68837517152629639227391373)
          ·
            refine ⟨25814068932236114710271765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68837517152629639227391373 25814068932236114710271765)
            ·
              refine ⟨1210034481198567877043989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25814068932236114710271765 1210034481198567877043989)
              ·
                refine ⟨56720366306182869236437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1210034481198567877043989 56720366306182869236437)
                ·
                  rfl

theorem cell22_1491244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 6].length) (baseStart_1491244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491244 prefixEnd_1491244 := by exact prefixLift 1491244
  have htrace : WordTrace (prefixWord ++ tailWord_1491244) baseStart_1491244 baseEnd_1491244 := by
    simpa [prefixWord, tailWord_1491244, baseEnd_1491244] using wordTrace_append hprefix tailTrace_1491244
  have hstable : (prefixWord ++ tailWord_1491244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491244).length < 2 ^ (prefixWord ++ tailWord_1491244).sum := by decide
  have hdescent : baseEnd_1491244 < baseStart_1491244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491250 : List Nat := [3, 2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_1491250 : Nat := 118140960795 + 1491250 * 2 ^ 59
def prefixEnd_1491250 : Nat := 4983230072969 + 3 ^ 40 * 1491250 * 2
def baseEnd_1491250 : Nat := 170161783559421269159305

theorem tailTrace_1491250 : CollatzResearch.WordTrace tailWord_1491250 prefixEnd_1491250 170161783559421269159305 := by
  unfold tailWord_1491250
  simp only [CollatzResearch.WordTrace]
  refine ⟨13597588961865852517145801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36260237231642273379055469 13597588961865852517145801)
  ·
    refine ⟨10198191721399389387859351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13597588961865852517145801 10198191721399389387859351)
    ·
      refine ⟨15297287582099084081789027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10198191721399389387859351 15297287582099084081789027)
      ·
        refine ⟨22945931373148626122683541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15297287582099084081789027 22945931373148626122683541)
        ·
          refine ⟨1075590533116341849500791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22945931373148626122683541 1075590533116341849500791)
          ·
            refine ⟨1613385799674512774251187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075590533116341849500791 1613385799674512774251187)
            ·
              refine ⟨2420078699511769161376781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613385799674512774251187 2420078699511769161376781)
              ·
                refine ⟨907529512316913435516293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2420078699511769161376781 907529512316913435516293)
                ·
                  refine ⟨170161783559421269159305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 907529512316913435516293 170161783559421269159305)
                  ·
                    rfl

theorem cell22_1491250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_1491250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491250 prefixEnd_1491250 := by exact prefixLift 1491250
  have htrace : WordTrace (prefixWord ++ tailWord_1491250) baseStart_1491250 baseEnd_1491250 := by
    simpa [prefixWord, tailWord_1491250, baseEnd_1491250] using wordTrace_append hprefix tailTrace_1491250
  have hstable : (prefixWord ++ tailWord_1491250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491250).length < 2 ^ (prefixWord ++ tailWord_1491250).sum := by decide
  have hdescent : baseEnd_1491250 < baseStart_1491250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491338 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 2, 5]
def baseStart_1491338 : Nat := 118140960795 + 1491338 * 2 ^ 59
def prefixEnd_1491338 : Nat := 4983230072969 + 3 ^ 40 * 1491338 * 2
def baseEnd_1491338 : Nat := 510515474876660911277645

theorem tailTrace_1491338 : CollatzResearch.WordTrace tailWord_1491338 prefixEnd_1491338 510515474876660911277645 := by
  unfold tailWord_1491338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13598391367786150274446667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36262376980763067398524445 13598391367786150274446667)
  ·
    refine ⟨20397587051679225411670001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13598391367786150274446667 20397587051679225411670001)
    ·
      refine ⟨15298190288759419058752501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20397587051679225411670001 15298190288759419058752501)
      ·
        refine ⟨1434205339571195536758047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15298190288759419058752501 1434205339571195536758047)
        ·
          refine ⟨2151308009356793305137071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434205339571195536758047 2151308009356793305137071)
          ·
            refine ⟨3226962014035189957705607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151308009356793305137071 3226962014035189957705607)
            ·
              refine ⟨4840443021052784936558411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3226962014035189957705607 4840443021052784936558411)
              ·
                refine ⟨7260664531579177404837617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4840443021052784936558411 7260664531579177404837617)
                ·
                  refine ⟨5445498398684383053628213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7260664531579177404837617 5445498398684383053628213)
                  ·
                    refine ⟨510515474876660911277645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5445498398684383053628213 510515474876660911277645)
                    ·
                      rfl

theorem cell22_1491338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_1491338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491338 prefixEnd_1491338 := by exact prefixLift 1491338
  have htrace : WordTrace (prefixWord ++ tailWord_1491338) baseStart_1491338 baseEnd_1491338 := by
    simpa [prefixWord, tailWord_1491338, baseEnd_1491338] using wordTrace_append hprefix tailTrace_1491338
  have hstable : (prefixWord ++ tailWord_1491338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491338).length < 2 ^ (prefixWord ++ tailWord_1491338).sum := by decide
  have hdescent : baseEnd_1491338 < baseStart_1491338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491383 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 2, 3]
def baseStart_1491383 : Nat := 118140960795 + 1491383 * 2 ^ 59
def prefixEnd_1491383 : Nat := 4983230072969 + 3 ^ 40 * 1491383 * 2
def baseEnd_1491383 : Nat := 510530879296295793902507

theorem tailTrace_1491383 : CollatzResearch.WordTrace tailWord_1491383 prefixEnd_1491383 510530879296295793902507 := by
  unfold tailWord_1491383
  simp only [CollatzResearch.WordTrace]
  refine ⟨54395206755981573783174803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36263471170654382522116535 54395206755981573783174803)
  ·
    refine ⟨81592810133972360674762205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54395206755981573783174803 81592810133972360674762205)
    ·
      refine ⟨30597303800239635253035827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81592810133972360674762205 30597303800239635253035827)
      ·
        refine ⟨45895955700359452879553741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30597303800239635253035827 45895955700359452879553741)
        ·
          refine ⟨17210983387634794829832653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45895955700359452879553741 17210983387634794829832653)
          ·
            refine ⟨6454118770363048061187245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17210983387634794829832653 6454118770363048061187245)
            ·
              refine ⟨2420294538886143022945217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6454118770363048061187245 2420294538886143022945217)
              ·
                refine ⟨1815220904164607267208913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420294538886143022945217 1815220904164607267208913)
                ·
                  refine ⟨1361415678123455450406685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1815220904164607267208913 1361415678123455450406685)
                  ·
                    refine ⟨510530879296295793902507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1361415678123455450406685 510530879296295793902507)
                    ·
                      rfl

theorem cell22_1491383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_1491383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491383 prefixEnd_1491383 := by exact prefixLift 1491383
  have htrace : WordTrace (prefixWord ++ tailWord_1491383) baseStart_1491383 baseEnd_1491383 := by
    simpa [prefixWord, tailWord_1491383, baseEnd_1491383] using wordTrace_append hprefix tailTrace_1491383
  have hstable : (prefixWord ++ tailWord_1491383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491383).length < 2 ^ (prefixWord ++ tailWord_1491383).sum := by decide
  have hdescent : baseEnd_1491383 < baseStart_1491383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491400 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 2, 3]
def baseStart_1491400 : Nat := 118140960795 + 1491400 * 2 ^ 59
def prefixEnd_1491400 : Nat := 4983230072969 + 3 ^ 40 * 1491400 * 2
def baseEnd_1491400 : Nat := 510536698743713416227455

theorem tailTrace_1491400 : CollatzResearch.WordTrace tailWord_1491400 prefixEnd_1491400 510536698743713416227455 := by
  unfold tailWord_1491400
  simp only [CollatzResearch.WordTrace]
  refine ⟨27197913398459992843271827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36263884531279990457695769 27197913398459992843271827)
  ·
    refine ⟨40796870097689989264907741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27197913398459992843271827 40796870097689989264907741)
    ·
      refine ⟨15298826286633745974340403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40796870097689989264907741 15298826286633745974340403)
      ·
        refine ⟨22948239429950618961510605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15298826286633745974340403 22948239429950618961510605)
        ·
          refine ⟨8605589786231482110566477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22948239429950618961510605 8605589786231482110566477)
          ·
            refine ⟨3227096169836805791462429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8605589786231482110566477 3227096169836805791462429)
            ·
              refine ⟨1210161063688802171798411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3227096169836805791462429 1210161063688802171798411)
              ·
                refine ⟨1815241595533203257697617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210161063688802171798411 1815241595533203257697617)
                ·
                  refine ⟨1361431196649902443273213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1815241595533203257697617 1361431196649902443273213)
                  ·
                    refine ⟨510536698743713416227455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1361431196649902443273213 510536698743713416227455)
                    ·
                      rfl

theorem cell22_1491400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_1491400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491400 prefixEnd_1491400 := by exact prefixLift 1491400
  have htrace : WordTrace (prefixWord ++ tailWord_1491400) baseStart_1491400 baseEnd_1491400 := by
    simpa [prefixWord, tailWord_1491400, baseEnd_1491400] using wordTrace_append hprefix tailTrace_1491400
  have hstable : (prefixWord ++ tailWord_1491400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491400).length < 2 ^ (prefixWord ++ tailWord_1491400).sum := by decide
  have hdescent : baseEnd_1491400 < baseStart_1491400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491409 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_1491409 : Nat := 118140960795 + 1491409 * 2 ^ 59
def prefixEnd_1491409 : Nat := 4983230072969 + 3 ^ 40 * 1491409 * 2
def baseEnd_1491409 : Nat := 510539779627640392752427

theorem tailTrace_1491409 : CollatzResearch.WordTrace tailWord_1491409 prefixEnd_1491409 510539779627640392752427 := by
  unfold tailWord_1491409
  simp only [CollatzResearch.WordTrace]
  refine ⟨54396155053887380223621281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36264103369258253482414187 54396155053887380223621281)
  ·
    refine ⟨40797116290415535167715961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54396155053887380223621281 40797116290415535167715961)
    ·
      refine ⟨30597837217811651375786971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40797116290415535167715961 30597837217811651375786971)
      ·
        refine ⟨45896755826717477063680457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30597837217811651375786971 45896755826717477063680457)
        ·
          refine ⟨34422566870038107797760343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45896755826717477063680457 34422566870038107797760343)
          ·
            refine ⟨51633850305057161696640515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34422566870038107797760343 51633850305057161696640515)
            ·
              refine ⟨77450775457585742544960773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51633850305057161696640515 77450775457585742544960773)
              ·
                refine ⟨14522020398297326727180145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77450775457585742544960773 14522020398297326727180145)
                ·
                  refine ⟨10891515298722995045385109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14522020398297326727180145 10891515298722995045385109)
                  ·
                    refine ⟨510539779627640392752427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10891515298722995045385109 510539779627640392752427)
                    ·
                      rfl

theorem cell22_1491409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_1491409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491409 prefixEnd_1491409 := by exact prefixLift 1491409
  have htrace : WordTrace (prefixWord ++ tailWord_1491409) baseStart_1491409 baseEnd_1491409 := by
    simpa [prefixWord, tailWord_1491409, baseEnd_1491409] using wordTrace_append hprefix tailTrace_1491409
  have hstable : (prefixWord ++ tailWord_1491409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491409).length < 2 ^ (prefixWord ++ tailWord_1491409).sum := by decide
  have hdescent : baseEnd_1491409 < baseStart_1491409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491413 : List Nat := [1, 3, 2, 3, 1, 4, 2, 6]
def baseStart_1491413 : Nat := 118140960795 + 1491413 * 2 ^ 59
def prefixEnd_1491413 : Nat := 4983230072969 + 3 ^ 40 * 1491413 * 2
def baseEnd_1491413 : Nat := 56726794323265079516935

theorem tailTrace_1491413 : CollatzResearch.WordTrace tailWord_1491413 prefixEnd_1491413 56726794323265079516935 := by
  unfold tailWord_1491413
  simp only [CollatzResearch.WordTrace]
  refine ⟨54396300945872888906766893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36264200630581925937844595 54396300945872888906766893)
  ·
    refine ⟨20398612854702333340037585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54396300945872888906766893 20398612854702333340037585)
    ·
      refine ⟨15298959641026750005028189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20398612854702333340037585 15298959641026750005028189)
      ·
        refine ⟨5737109865385031251885571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15298959641026750005028189 5737109865385031251885571)
        ·
          refine ⟨8605664798077546877828357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5737109865385031251885571 8605664798077546877828357)
          ·
            refine ⟨1613562149639540039592817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8605664798077546877828357 1613562149639540039592817)
            ·
              refine ⟨1210171612229655029694613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613562149639540039592817 1210171612229655029694613)
              ·
                refine ⟨56726794323265079516935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1210171612229655029694613 56726794323265079516935)
                ·
                  rfl

theorem cell22_1491413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 6].length) (baseStart_1491413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491413 prefixEnd_1491413 := by exact prefixLift 1491413
  have htrace : WordTrace (prefixWord ++ tailWord_1491413) baseStart_1491413 baseEnd_1491413 := by
    simpa [prefixWord, tailWord_1491413, baseEnd_1491413] using wordTrace_append hprefix tailTrace_1491413
  have hstable : (prefixWord ++ tailWord_1491413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491413).length < 2 ^ (prefixWord ++ tailWord_1491413).sum := by decide
  have hdescent : baseEnd_1491413 < baseStart_1491413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491424 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 9]
def baseStart_1491424 : Nat := 118140960795 + 1491424 * 2 ^ 59
def prefixEnd_1491424 : Nat := 4983230072969 + 3 ^ 40 * 1491424 * 2
def baseEnd_1491424 : Nat := 170181638144728451209127

theorem tailTrace_1491424 : CollatzResearch.WordTrace tailWord_1491424 prefixEnd_1491424 170181638144728451209127 := by
  unfold tailWord_1491424
  simp only [CollatzResearch.WordTrace]
  refine ⟨27198351074416518892708663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36264468099222025190278217 27198351074416518892708663)
  ·
    refine ⟨40797526611624778339062995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27198351074416518892708663 40797526611624778339062995)
    ·
      refine ⟨61196289917437167508594493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40797526611624778339062995 61196289917437167508594493)
      ·
        refine ⟨22948608719038937815722935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61196289917437167508594493 22948608719038937815722935)
        ·
          refine ⟨34422913078558406723584403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22948608719038937815722935 34422913078558406723584403)
          ·
            refine ⟨51634369617837610085376605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34422913078558406723584403 51634369617837610085376605)
            ·
              refine ⟨19362888606689103782016227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51634369617837610085376605 19362888606689103782016227)
              ·
                refine ⟨29044332910033655673024341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19362888606689103782016227 29044332910033655673024341)
                ·
                  refine ⟨170181638144728451209127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29044332910033655673024341 170181638144728451209127)
                  ·
                    rfl

theorem cell22_1491424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_1491424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491424 prefixEnd_1491424 := by exact prefixLift 1491424
  have htrace : WordTrace (prefixWord ++ tailWord_1491424) baseStart_1491424 baseEnd_1491424 := by
    simpa [prefixWord, tailWord_1491424, baseEnd_1491424] using wordTrace_append hprefix tailTrace_1491424
  have hstable : (prefixWord ++ tailWord_1491424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491424).length < 2 ^ (prefixWord ++ tailWord_1491424).sum := by decide
  have hdescent : baseEnd_1491424 < baseStart_1491424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491441 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 5]
def baseStart_1491441 : Nat := 118140960795 + 1491441 * 2 ^ 59
def prefixEnd_1491441 : Nat := 4983230072969 + 3 ^ 40 * 1491441 * 2
def baseEnd_1491441 : Nat := 170183577960534325317443

theorem tailTrace_1491441 : CollatzResearch.WordTrace tailWord_1491441 prefixEnd_1491441 170183577960534325317443 := by
  unfold tailWord_1491441
  simp only [CollatzResearch.WordTrace]
  refine ⟨54397322189771449688786177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36264881459847633125857451 54397322189771449688786177)
  ·
    refine ⟨40797991642328587266589633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54397322189771449688786177 40797991642328587266589633)
    ·
      refine ⟨30598493731746440449942225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40797991642328587266589633 30598493731746440449942225)
      ·
        refine ⟨22948870298809830337456669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30598493731746440449942225 22948870298809830337456669)
        ·
          refine ⟨8605826362053686376546251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22948870298809830337456669 8605826362053686376546251)
          ·
            refine ⟨12908739543080529564819377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8605826362053686376546251 12908739543080529564819377)
            ·
              refine ⟨9681554657310397173614533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12908739543080529564819377 9681554657310397173614533)
              ·
                refine ⟨1815291498245699470052725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9681554657310397173614533 1815291498245699470052725)
                ·
                  refine ⟨170183577960534325317443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1815291498245699470052725 170183577960534325317443)
                  ·
                    rfl

theorem cell22_1491441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_1491441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491441 prefixEnd_1491441 := by exact prefixLift 1491441
  have htrace : WordTrace (prefixWord ++ tailWord_1491441) baseStart_1491441 baseEnd_1491441 := by
    simpa [prefixWord, tailWord_1491441, baseEnd_1491441] using wordTrace_append hprefix tailTrace_1491441
  have hstable : (prefixWord ++ tailWord_1491441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491441).length < 2 ^ (prefixWord ++ tailWord_1491441).sum := by decide
  have hdescent : baseEnd_1491441 < baseStart_1491441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491548 : List Nat := [2, 2, 4, 1, 3, 1, 9]
def baseStart_1491548 : Nat := 118140960795 + 1491548 * 2 ^ 59
def prefixEnd_1491548 : Nat := 4983230072969 + 3 ^ 40 * 1491548 * 2
def baseEnd_1491548 : Nat := 18910643043270013463963

theorem tailTrace_1491548 : CollatzResearch.WordTrace tailWord_1491548 prefixEnd_1491548 18910643043270013463963 := by
  unfold tailWord_1491548
  simp only [CollatzResearch.WordTrace]
  refine ⟨27200612400191903481465649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36267483200255871308620865 27200612400191903481465649)
  ·
    refine ⟨20400459300143927611099237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27200612400191903481465649 20400459300143927611099237)
    ·
      refine ⟨3825086118776986427081107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20400459300143927611099237 3825086118776986427081107)
      ·
        refine ⟨5737629178165479640621661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825086118776986427081107 5737629178165479640621661)
        ·
          refine ⟨2151610941812054865233123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5737629178165479640621661 2151610941812054865233123)
          ·
            refine ⟨3227416412718082297849685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151610941812054865233123 3227416412718082297849685)
            ·
              refine ⟨18910643043270013463963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3227416412718082297849685 18910643043270013463963)
              ·
                rfl

theorem cell22_1491548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 9].length) (baseStart_1491548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491548 prefixEnd_1491548 := by exact prefixLift 1491548
  have htrace : WordTrace (prefixWord ++ tailWord_1491548) baseStart_1491548 baseEnd_1491548 := by
    simpa [prefixWord, tailWord_1491548, baseEnd_1491548] using wordTrace_append hprefix tailTrace_1491548
  have hstable : (prefixWord ++ tailWord_1491548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491548).length < 2 ^ (prefixWord ++ tailWord_1491548).sum := by decide
  have hdescent : baseEnd_1491548 < baseStart_1491548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491672 : List Nat := [2, 1, 2, 2, 3, 2, 4, 2, 4]
def baseStart_1491672 : Nat := 118140960795 + 1491672 * 2 ^ 59
def prefixEnd_1491672 : Nat := 4983230072969 + 3 ^ 40 * 1491672 * 2
def baseEnd_1491672 : Nat := 170209936634131791142207

theorem tailTrace_1491672 : CollatzResearch.WordTrace tailWord_1491672 prefixEnd_1491672 170209936634131791142207 := by
  unfold tailWord_1491672
  simp only [CollatzResearch.WordTrace]
  refine ⟨27202873725967288070222635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36270498301289717426963513 27202873725967288070222635)
  ·
    refine ⟨40804310588950932105333953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27202873725967288070222635 40804310588950932105333953)
    ·
      refine ⟨30603232941713199079000465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40804310588950932105333953 30603232941713199079000465)
      ·
        refine ⟨22952424706284899309250349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30603232941713199079000465 22952424706284899309250349)
        ·
          refine ⟨8607159264856837240968881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22952424706284899309250349 8607159264856837240968881)
          ·
            refine ⟨6455369448642627930726661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8607159264856837240968881 6455369448642627930726661)
            ·
              refine ⟨1210381771620492737011249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6455369448642627930726661 1210381771620492737011249)
              ·
                refine ⟨907786328715369552758437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1210381771620492737011249 907786328715369552758437)
                ·
                  refine ⟨170209936634131791142207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 907786328715369552758437 170209936634131791142207)
                  ·
                    rfl

theorem cell22_1491672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 4].length) (baseStart_1491672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491672 prefixEnd_1491672 := by exact prefixLift 1491672
  have htrace : WordTrace (prefixWord ++ tailWord_1491672) baseStart_1491672 baseEnd_1491672 := by
    simpa [prefixWord, tailWord_1491672, baseEnd_1491672] using wordTrace_append hprefix tailTrace_1491672
  have hstable : (prefixWord ++ tailWord_1491672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491672).length < 2 ^ (prefixWord ++ tailWord_1491672).sum := by decide
  have hdescent : baseEnd_1491672 < baseStart_1491672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491796 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 5]
def baseStart_1491796 : Nat := 118140960795 + 1491796 * 2 ^ 59
def prefixEnd_1491796 : Nat := 4983230072969 + 3 ^ 40 * 1491796 * 2
def baseEnd_1491796 : Nat := 170224085878833461108747

theorem tailTrace_1491796 : CollatzResearch.WordTrace tailWord_1491796 prefixEnd_1491796 170224085878833461108747 := by
  unfold tailWord_1491796
  simp only [CollatzResearch.WordTrace]
  refine ⟨27205135051742672658979621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36273513402323563545306161 27205135051742672658979621)
  ·
    refine ⟨5100962822201751123558679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27205135051742672658979621 5100962822201751123558679)
    ·
      refine ⟨7651444233302626685338019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100962822201751123558679 7651444233302626685338019)
      ·
        refine ⟨11477166349953940028007029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7651444233302626685338019 11477166349953940028007029)
        ·
          refine ⟨1075984345308181877625659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11477166349953940028007029 1075984345308181877625659)
          ·
            refine ⟨1613976517962272816438489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075984345308181877625659 1613976517962272816438489)
            ·
              refine ⟨1210482388471704612328867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613976517962272816438489 1210482388471704612328867)
              ·
                refine ⟨1815723582707556918493301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210482388471704612328867 1815723582707556918493301)
                ·
                  refine ⟨170224085878833461108747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1815723582707556918493301 170224085878833461108747)
                  ·
                    rfl

theorem cell22_1491796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_1491796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491796 prefixEnd_1491796 := by exact prefixLift 1491796
  have htrace : WordTrace (prefixWord ++ tailWord_1491796) baseStart_1491796 baseEnd_1491796 := by
    simpa [prefixWord, tailWord_1491796, baseEnd_1491796] using wordTrace_append hprefix tailTrace_1491796
  have hstable : (prefixWord ++ tailWord_1491796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491796).length < 2 ^ (prefixWord ++ tailWord_1491796).sum := by decide
  have hdescent : baseEnd_1491796 < baseStart_1491796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491895 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 2, 5]
def baseStart_1491895 : Nat := 118140960795 + 1491895 * 2 ^ 59
def prefixEnd_1491895 : Nat := 4983230072969 + 3 ^ 40 * 1491895 * 2
def baseEnd_1491895 : Nat := 510706147359697125100937

theorem tailTrace_1491895 : CollatzResearch.WordTrace tailWord_1491895 prefixEnd_1491895 510706147359697125100937 := by
  unfold tailWord_1491895
  simp only [CollatzResearch.WordTrace]
  refine ⟨54413880930126685225813139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36275920620084456817208759 54413880930126685225813139)
  ·
    refine ⟨81620821395190027838719709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54413880930126685225813139 81620821395190027838719709)
    ·
      refine ⟨30607808023196260439519891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81620821395190027838719709 30607808023196260439519891)
      ·
        refine ⟨45911712034794390659279837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30607808023196260439519891 45911712034794390659279837)
        ·
          refine ⟨17216892013047896497229939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45911712034794390659279837 17216892013047896497229939)
          ·
            refine ⟨25825338019571844745844909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17216892013047896497229939 25825338019571844745844909)
            ·
              refine ⟨9684501757339441779691841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25825338019571844745844909 9684501757339441779691841)
              ·
                refine ⟨7263376318004581334768881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9684501757339441779691841 7263376318004581334768881)
                ·
                  refine ⟨5447532238503436001076661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7263376318004581334768881 5447532238503436001076661)
                  ·
                    refine ⟨510706147359697125100937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5447532238503436001076661 510706147359697125100937)
                    ·
                      rfl

theorem cell22_1491895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_1491895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491895 prefixEnd_1491895 := by exact prefixLift 1491895
  have htrace : WordTrace (prefixWord ++ tailWord_1491895) baseStart_1491895 baseEnd_1491895 := by
    simpa [prefixWord, tailWord_1491895, baseEnd_1491895] using wordTrace_append hprefix tailTrace_1491895
  have hstable : (prefixWord ++ tailWord_1491895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491895).length < 2 ^ (prefixWord ++ tailWord_1491895).sum := by decide
  have hdescent : baseEnd_1491895 < baseStart_1491895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491897 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 5]
def baseStart_1491897 : Nat := 118140960795 + 1491897 * 2 ^ 59
def prefixEnd_1491897 : Nat := 4983230072969 + 3 ^ 40 * 1491897 * 2
def baseEnd_1491897 : Nat := 170235610666856595516977

theorem tailTrace_1491897 : CollatzResearch.WordTrace tailWord_1491897 prefixEnd_1491897 170235610666856595516977 := by
  unfold tailWord_1491897
  simp only [CollatzResearch.WordTrace]
  refine ⟨54413953876119439567385945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36275969250746293044923963 54413953876119439567385945)
  ·
    refine ⟨40810465407089579675539459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54413953876119439567385945 40810465407089579675539459)
    ·
      refine ⟨61215698110634369513309189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40810465407089579675539459 61215698110634369513309189)
      ·
        refine ⟨11477943395743944283745473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61215698110634369513309189 11477943395743944283745473)
        ·
          refine ⟨8608457546807958212809105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11477943395743944283745473 8608457546807958212809105)
          ·
            refine ⟨6456343160105968659606829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8608457546807958212809105 6456343160105968659606829)
            ·
              refine ⟨2421128685039738247352561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6456343160105968659606829 2421128685039738247352561)
              ·
                refine ⟨1815846513779803685514421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2421128685039738247352561 1815846513779803685514421)
                ·
                  refine ⟨170235610666856595516977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1815846513779803685514421 170235610666856595516977)
                  ·
                    rfl

theorem cell22_1491897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_1491897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491897 prefixEnd_1491897 := by exact prefixLift 1491897
  have htrace : WordTrace (prefixWord ++ tailWord_1491897) baseStart_1491897 baseEnd_1491897 := by
    simpa [prefixWord, tailWord_1491897, baseEnd_1491897] using wordTrace_append hprefix tailTrace_1491897
  have hstable : (prefixWord ++ tailWord_1491897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491897).length < 2 ^ (prefixWord ++ tailWord_1491897).sum := by decide
  have hdescent : baseEnd_1491897 < baseStart_1491897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491985 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_1491985 : Nat := 118140960795 + 1491985 * 2 ^ 59
def prefixEnd_1491985 : Nat := 4983230072969 + 3 ^ 40 * 1491985 * 2
def baseEnd_1491985 : Nat := 510736956198966890350661

theorem tailTrace_1491985 : CollatzResearch.WordTrace tailWord_1491985 prefixEnd_1491985 510736956198966890350661 := by
  unfold tailWord_1491985
  simp only [CollatzResearch.WordTrace]
  refine ⟨54417163499800630596589409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36278108999867087064392939 54417163499800630596589409)
  ·
    refine ⟨40812872624850472947442057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54417163499800630596589409 40812872624850472947442057)
    ·
      refine ⟨30609654468637854710581543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40812872624850472947442057 30609654468637854710581543)
      ·
        refine ⟨45914481702956782065872315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30609654468637854710581543 45914481702956782065872315)
        ·
          refine ⟨68871722554435173098808473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45914481702956782065872315 68871722554435173098808473)
          ·
            refine ⟨51653791915826379824106355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68871722554435173098808473 51653791915826379824106355)
            ·
              refine ⟨77480687873739569736159533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51653791915826379824106355 77480687873739569736159533)
              ·
                refine ⟨29055257952652338651059825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77480687873739569736159533 29055257952652338651059825)
                ·
                  refine ⟨21791443464489253988294869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29055257952652338651059825 21791443464489253988294869)
                  ·
                    refine ⟨510736956198966890350661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21791443464489253988294869 510736956198966890350661)
                    ·
                      rfl

theorem cell22_1491985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_1491985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491985 prefixEnd_1491985 := by exact prefixLift 1491985
  have htrace : WordTrace (prefixWord ++ tailWord_1491985) baseStart_1491985 baseEnd_1491985 := by
    simpa [prefixWord, tailWord_1491985, baseEnd_1491985] using wordTrace_append hprefix tailTrace_1491985
  have hstable : (prefixWord ++ tailWord_1491985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491985).length < 2 ^ (prefixWord ++ tailWord_1491985).sum := by decide
  have hdescent : baseEnd_1491985 < baseStart_1491985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491989 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_1491989 : Nat := 118140960795 + 1491989 * 2 ^ 59
def prefixEnd_1491989 : Nat := 4983230072969 + 3 ^ 40 * 1491989 * 2
def baseEnd_1491989 : Nat := 510738325480712213250649

theorem tailTrace_1491989 : CollatzResearch.WordTrace tailWord_1491989 prefixEnd_1491989 510738325480712213250649 := by
  unfold tailWord_1491989
  simp only [CollatzResearch.WordTrace]
  refine ⟨54417309391786139279735021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36278206261190759519823347 54417309391786139279735021)
  ·
    refine ⟨20406491021919802229900633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54417309391786139279735021 20406491021919802229900633)
    ·
      refine ⟨15304868266439851672425475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20406491021919802229900633 15304868266439851672425475)
      ·
        refine ⟨22957302399659777508638213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15304868266439851672425475 22957302399659777508638213)
        ·
          refine ⟨4304494199936208282869665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22957302399659777508638213 4304494199936208282869665)
          ·
            refine ⟨3228370649952156212152249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4304494199936208282869665 3228370649952156212152249)
            ·
              refine ⟨2421277987464117159114187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228370649952156212152249 2421277987464117159114187)
              ·
                refine ⟨3631916981196175738671281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421277987464117159114187 3631916981196175738671281)
                ·
                  refine ⟨2723937735897131804003461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3631916981196175738671281 2723937735897131804003461)
                  ·
                    refine ⟨510738325480712213250649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2723937735897131804003461 510738325480712213250649)
                    ·
                      rfl

theorem cell22_1491989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_1491989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1491989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1491989 prefixEnd_1491989 := by exact prefixLift 1491989
  have htrace : WordTrace (prefixWord ++ tailWord_1491989) baseStart_1491989 baseEnd_1491989 := by
    simpa [prefixWord, tailWord_1491989, baseEnd_1491989] using wordTrace_append hprefix tailTrace_1491989
  have hstable : (prefixWord ++ tailWord_1491989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491989).length < 2 ^ (prefixWord ++ tailWord_1491989).sum := by decide
  have hdescent : baseEnd_1491989 < baseStart_1491989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492010 : List Nat := [3, 1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_1492010 : Nat := 118140960795 + 1492010 * 2 ^ 59
def prefixEnd_1492010 : Nat := 4983230072969 + 3 ^ 40 * 1492010 * 2
def baseEnd_1492010 : Nat := 170248504736625052825195

theorem tailTrace_1492010 : CollatzResearch.WordTrace tailWord_1492010 prefixEnd_1492010 170248504736625052825195 := by
  unfold tailWord_1492010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13604518831177514966562371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36278716883140039910832989 13604518831177514966562371)
  ·
    refine ⟨20406778246766272449843557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13604518831177514966562371 20406778246766272449843557)
    ·
      refine ⟨3826270921268676084345667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20406778246766272449843557 3826270921268676084345667)
      ·
        refine ⟨5739406381903014126518501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3826270921268676084345667 5739406381903014126518501)
        ·
          refine ⟨1076138696606815148722219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5739406381903014126518501 1076138696606815148722219)
          ·
            refine ⟨1614208044910222723083329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076138696606815148722219 1614208044910222723083329)
            ·
              refine ⟨1210656033682667042312497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1614208044910222723083329 1210656033682667042312497)
              ·
                refine ⟨907992025262000281734373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1210656033682667042312497 907992025262000281734373)
                ·
                  refine ⟨170248504736625052825195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 907992025262000281734373 170248504736625052825195)
                  ·
                    rfl

theorem cell22_1492010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_1492010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492010 prefixEnd_1492010 := by exact prefixLift 1492010
  have htrace : WordTrace (prefixWord ++ tailWord_1492010) baseStart_1492010 baseEnd_1492010 := by
    simpa [prefixWord, tailWord_1492010, baseEnd_1492010] using wordTrace_append hprefix tailTrace_1492010
  have hstable : (prefixWord ++ tailWord_1492010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492010).length < 2 ^ (prefixWord ++ tailWord_1492010).sum := by decide
  have hdescent : baseEnd_1492010 < baseStart_1492010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492015 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 11]
def baseStart_1492015 : Nat := 118140960795 + 1492015 * 2 ^ 59
def prefixEnd_1492015 : Nat := 4983230072969 + 3 ^ 40 * 1492015 * 2
def baseEnd_1492015 : Nat := 170249075270685604033523

theorem tailTrace_1492015 : CollatzResearch.WordTrace tailWord_1492015 prefixEnd_1492015 170249075270685604033523 := by
  unfold tailWord_1492015
  simp only [CollatzResearch.WordTrace]
  refine ⟨54418257689691945720181499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36278838459794630480120999 54418257689691945720181499)
  ·
    refine ⟨81627386534537918580272249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54418257689691945720181499 81627386534537918580272249)
    ·
      refine ⟨61220539900903438935204187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81627386534537918580272249 61220539900903438935204187)
      ·
        refine ⟨91830809851355158402806281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61220539900903438935204187 91830809851355158402806281)
        ·
          refine ⟨68873107388516368802104711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91830809851355158402806281 68873107388516368802104711)
          ·
            refine ⟨103309661082774553203157067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68873107388516368802104711 103309661082774553203157067)
            ·
              refine ⟨154964491624161829804735601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103309661082774553203157067 154964491624161829804735601)
              ·
                refine ⟨116223368718121372353551701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154964491624161829804735601 116223368718121372353551701)
                ·
                  refine ⟨170249075270685604033523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 116223368718121372353551701 170249075270685604033523)
                  ·
                    rfl

theorem cell22_1492015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 11].length) (baseStart_1492015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492015 prefixEnd_1492015 := by exact prefixLift 1492015
  have htrace : WordTrace (prefixWord ++ tailWord_1492015) baseStart_1492015 baseEnd_1492015 := by
    simpa [prefixWord, tailWord_1492015, baseEnd_1492015] using wordTrace_append hprefix tailTrace_1492015
  have hstable : (prefixWord ++ tailWord_1492015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492015).length < 2 ^ (prefixWord ++ tailWord_1492015).sum := by decide
  have hdescent : baseEnd_1492015 < baseStart_1492015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492032 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 5]
def baseStart_1492032 : Nat := 118140960795 + 1492032 * 2 ^ 59
def prefixEnd_1492032 : Nat := 4983230072969 + 3 ^ 40 * 1492032 * 2
def baseEnd_1492032 : Nat := 170251015086491478141839

theorem tailTrace_1492032 : CollatzResearch.WordTrace tailWord_1492032 prefixEnd_1492032 170251015086491478141839 := by
  unfold tailWord_1492032
  simp only [CollatzResearch.WordTrace]
  refine ⟨27209438865315178811775175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36279251820420238415700233 27209438865315178811775175)
  ·
    refine ⟨40814158297972768217662763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27209438865315178811775175 40814158297972768217662763)
    ·
      refine ⟨61221237446959152326494145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40814158297972768217662763 61221237446959152326494145)
      ·
        refine ⟨45915928085219364244870609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61221237446959152326494145 45915928085219364244870609)
        ·
          refine ⟨34436946063914523183652957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45915928085219364244870609 34436946063914523183652957)
          ·
            refine ⟨12913854773967946193869859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34436946063914523183652957 12913854773967946193869859)
            ·
              refine ⟨19370782160951919290804789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12913854773967946193869859 19370782160951919290804789)
              ·
                refine ⟨1816010827589242433512949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19370782160951919290804789 1816010827589242433512949)
                ·
                  refine ⟨170251015086491478141839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1816010827589242433512949 170251015086491478141839)
                  ·
                    rfl

theorem cell22_1492032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_1492032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492032 prefixEnd_1492032 := by exact prefixLift 1492032
  have htrace : WordTrace (prefixWord ++ tailWord_1492032) baseStart_1492032 baseEnd_1492032 := by
    simpa [prefixWord, tailWord_1492032, baseEnd_1492032] using wordTrace_append hprefix tailTrace_1492032
  have hstable : (prefixWord ++ tailWord_1492032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492032).length < 2 ^ (prefixWord ++ tailWord_1492032).sum := by decide
  have hdescent : baseEnd_1492032 < baseStart_1492032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492066 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_1492066 : Nat := 118140960795 + 1492066 * 2 ^ 59
def prefixEnd_1492066 : Nat := 4983230072969 + 3 ^ 40 * 1492066 * 2
def baseEnd_1492066 : Nat := 170254894718103226358471

theorem tailTrace_1492066 : CollatzResearch.WordTrace tailWord_1492066 prefixEnd_1492066 170254894718103226358471 := by
  unfold tailWord_1492066
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605029453126795357572013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36280078541671454286858701 13605029453126795357572013)
  ·
    refine ⟨5101886044922548259089505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13605029453126795357572013 5101886044922548259089505)
    ·
      refine ⟨3826414533691911194317129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5101886044922548259089505 3826414533691911194317129)
      ·
        refine ⟨2869810900268933395737847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3826414533691911194317129 2869810900268933395737847)
        ·
          refine ⟨4304716350403400093606771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869810900268933395737847 4304716350403400093606771)
          ·
            refine ⟨6457074525605100140410157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304716350403400093606771 6457074525605100140410157)
            ·
              refine ⟨2421402947101912552653809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6457074525605100140410157 2421402947101912552653809)
              ·
                refine ⟨1816052210326434414490357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2421402947101912552653809 1816052210326434414490357)
                ·
                  refine ⟨170254894718103226358471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1816052210326434414490357 170254894718103226358471)
                  ·
                    rfl

theorem cell22_1492066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_1492066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492066 prefixEnd_1492066 := by exact prefixLift 1492066
  have htrace : WordTrace (prefixWord ++ tailWord_1492066) baseStart_1492066 baseEnd_1492066 := by
    simpa [prefixWord, tailWord_1492066, baseEnd_1492066] using wordTrace_append hprefix tailTrace_1492066
  have hstable : (prefixWord ++ tailWord_1492066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492066).length < 2 ^ (prefixWord ++ tailWord_1492066).sum := by decide
  have hdescent : baseEnd_1492066 < baseStart_1492066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492107 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 6, 4]
def baseStart_1492107 : Nat := 118140960795 + 1492107 * 2 ^ 59
def prefixEnd_1492107 : Nat := 4983230072969 + 3 ^ 40 * 1492107 * 2
def baseEnd_1492107 : Nat := 510778719292199238800287

theorem tailTrace_1492107 : CollatzResearch.WordTrace tailWord_1492107 prefixEnd_1492107 510778719292199238800287 := by
  unfold tailWord_1492107
  simp only [CollatzResearch.WordTrace]
  refine ⟨54421613205358645432530575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36281075470239096955020383 54421613205358645432530575)
  ·
    refine ⟨81632419808037968148795863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54421613205358645432530575 81632419808037968148795863)
    ·
      refine ⟨122448629712056952223193795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81632419808037968148795863 122448629712056952223193795)
      ·
        refine ⟨183672944568085428334790693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122448629712056952223193795 183672944568085428334790693)
        ·
          refine ⟨34438677106516017812773255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183672944568085428334790693 34438677106516017812773255)
          ·
            refine ⟨51658015659774026719159883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34438677106516017812773255 51658015659774026719159883)
            ·
              refine ⟨77487023489661040078739825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51658015659774026719159883 77487023489661040078739825)
              ·
                refine ⟨58115267617245780059054869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77487023489661040078739825 58115267617245780059054869)
                ·
                  refine ⟨2724153169558395940268197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58115267617245780059054869 2724153169558395940268197)
                  ·
                    refine ⟨510778719292199238800287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2724153169558395940268197 510778719292199238800287)
                    ·
                      rfl

theorem cell22_1492107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 4].length) (baseStart_1492107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492107 prefixEnd_1492107 := by exact prefixLift 1492107
  have htrace : WordTrace (prefixWord ++ tailWord_1492107) baseStart_1492107 baseEnd_1492107 := by
    simpa [prefixWord, tailWord_1492107, baseEnd_1492107] using wordTrace_append hprefix tailTrace_1492107
  have hstable : (prefixWord ++ tailWord_1492107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492107).length < 2 ^ (prefixWord ++ tailWord_1492107).sum := by decide
  have hdescent : baseEnd_1492107 < baseStart_1492107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492124 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1492124 : Nat := 118140960795 + 1492124 * 2 ^ 59
def prefixEnd_1492124 : Nat := 4983230072969 + 3 ^ 40 * 1492124 * 2
def baseEnd_1492124 : Nat := 510784538739616861125235

theorem tailTrace_1492124 : CollatzResearch.WordTrace tailWord_1492124 prefixEnd_1492124 510784538739616861125235 := by
  unfold tailWord_1492124
  simp only [CollatzResearch.WordTrace]
  refine ⟨27211116623148528667949713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36281488830864704890599617 27211116623148528667949713)
  ·
    refine ⟨20408337467361396500962285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27211116623148528667949713 20408337467361396500962285)
    ·
      refine ⟨7653126550260523687860857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20408337467361396500962285 7653126550260523687860857)
      ·
        refine ⟨5739844912695392765895643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7653126550260523687860857 5739844912695392765895643)
        ·
          refine ⟨8609767369043089148843465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739844912695392765895643 8609767369043089148843465)
          ·
            refine ⟨6457325526782316861632599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8609767369043089148843465 6457325526782316861632599)
            ·
              refine ⟨9685988290173475292448899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6457325526782316861632599 9685988290173475292448899)
              ·
                refine ⟨14528982435260212938673349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9685988290173475292448899 14528982435260212938673349)
                ·
                  refine ⟨2724184206611289926001253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14528982435260212938673349 2724184206611289926001253)
                  ·
                    refine ⟨510784538739616861125235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2724184206611289926001253 510784538739616861125235)
                    ·
                      rfl

theorem cell22_1492124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1492124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492124 prefixEnd_1492124 := by exact prefixLift 1492124
  have htrace : WordTrace (prefixWord ++ tailWord_1492124) baseStart_1492124 baseEnd_1492124 := by
    simpa [prefixWord, tailWord_1492124, baseEnd_1492124] using wordTrace_append hprefix tailTrace_1492124
  have hstable : (prefixWord ++ tailWord_1492124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492124).length < 2 ^ (prefixWord ++ tailWord_1492124).sum := by decide
  have hdescent : baseEnd_1492124 < baseStart_1492124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492152 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_1492152 : Nat := 118140960795 + 1492152 * 2 ^ 59
def prefixEnd_1492152 : Nat := 4983230072969 + 3 ^ 40 * 1492152 * 2
def baseEnd_1492152 : Nat := 510794123711834121425149

theorem tailTrace_1492152 : CollatzResearch.WordTrace tailWord_1492152 prefixEnd_1492152 510794123711834121425149 := by
  unfold tailWord_1492152
  simp only [CollatzResearch.WordTrace]
  refine ⟨27211627245097809058959355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36282169660130412078612473 27211627245097809058959355)
  ·
    refine ⟨40817440867646713588439033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27211627245097809058959355 40817440867646713588439033)
    ·
      refine ⟨30613080650735035191329275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40817440867646713588439033 30613080650735035191329275)
      ·
        refine ⟨45919620976102552786993913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30613080650735035191329275 45919620976102552786993913)
        ·
          refine ⟨34439715732076914590245435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45919620976102552786993913 34439715732076914590245435)
          ·
            refine ⟨51659573598115371885368153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34439715732076914590245435 51659573598115371885368153)
            ·
              refine ⟨38744680198586528914026115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51659573598115371885368153 38744680198586528914026115)
              ·
                refine ⟨58117020297879793371039173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38744680198586528914026115 58117020297879793371039173)
                ·
                  refine ⟨10896941305852461257069845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58117020297879793371039173 10896941305852461257069845)
                  ·
                    refine ⟨510794123711834121425149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10896941305852461257069845 510794123711834121425149)
                    ·
                      rfl

theorem cell22_1492152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_1492152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492152 prefixEnd_1492152 := by exact prefixLift 1492152
  have htrace : WordTrace (prefixWord ++ tailWord_1492152) baseStart_1492152 baseEnd_1492152 := by
    simpa [prefixWord, tailWord_1492152, baseEnd_1492152] using wordTrace_append hprefix tailTrace_1492152
  have hstable : (prefixWord ++ tailWord_1492152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492152).length < 2 ^ (prefixWord ++ tailWord_1492152).sum := by decide
  have hdescent : baseEnd_1492152 < baseStart_1492152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492154 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 5, 3]
def baseStart_1492154 : Nat := 118140960795 + 1492154 * 2 ^ 59
def prefixEnd_1492154 : Nat := 4983230072969 + 3 ^ 40 * 1492154 * 2
def baseEnd_1492154 : Nat := 510794808352706782875143

theorem tailTrace_1492154 : CollatzResearch.WordTrace tailWord_1492154 prefixEnd_1492154 510794808352706782875143 := by
  unfold tailWord_1492154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605831859047093114872879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36282218290792248306327677 13605831859047093114872879)
  ·
    refine ⟨20408747788570639672309319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13605831859047093114872879 20408747788570639672309319)
    ·
      refine ⟨30613121682855959508463979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20408747788570639672309319 30613121682855959508463979)
      ·
        refine ⟨45919682524283939262695969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30613121682855959508463979 45919682524283939262695969)
        ·
          refine ⟨34439761893212954447021977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45919682524283939262695969 34439761893212954447021977)
          ·
            refine ⟨25829821419909715835266483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34439761893212954447021977 25829821419909715835266483)
            ·
              refine ⟨38744732129864573752899725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25829821419909715835266483 38744732129864573752899725)
              ·
                refine ⟨14529274548699215157337397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38744732129864573752899725 14529274548699215157337397)
                ·
                  refine ⟨1362119488940551421000381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14529274548699215157337397 1362119488940551421000381)
                  ·
                    refine ⟨510794808352706782875143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1362119488940551421000381 510794808352706782875143)
                    ·
                      rfl

theorem cell22_1492154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_1492154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492154 prefixEnd_1492154 := by exact prefixLift 1492154
  have htrace : WordTrace (prefixWord ++ tailWord_1492154) baseStart_1492154 baseEnd_1492154 := by
    simpa [prefixWord, tailWord_1492154, baseEnd_1492154] using wordTrace_append hprefix tailTrace_1492154
  have hstable : (prefixWord ++ tailWord_1492154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492154).length < 2 ^ (prefixWord ++ tailWord_1492154).sum := by decide
  have hdescent : baseEnd_1492154 < baseStart_1492154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492167 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 9]
def baseStart_1492167 : Nat := 118140960795 + 1492167 * 2 ^ 59
def prefixEnd_1492167 : Nat := 4983230072969 + 3 ^ 40 * 1492167 * 2
def baseEnd_1492167 : Nat := 170266419506126360766701

theorem tailTrace_1492167 : CollatzResearch.WordTrace tailWord_1492167 prefixEnd_1492167 170266419506126360766701 := by
  unfold tailWord_1492167
  simp only [CollatzResearch.WordTrace]
  refine ⟨54423801585141275679714755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36282534390094183786476503 54423801585141275679714755)
  ·
    refine ⟨81635702377711913519572133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54423801585141275679714755 81635702377711913519572133)
    ·
      refine ⟨15306694195820983784919775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81635702377711913519572133 15306694195820983784919775)
      ·
        refine ⟨22960041293731475677379663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15306694195820983784919775 22960041293731475677379663)
        ·
          refine ⟨34440061940597213516069495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22960041293731475677379663 34440061940597213516069495)
          ·
            refine ⟨51660092910895820274104243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34440061940597213516069495 51660092910895820274104243)
            ·
              refine ⟨77490139366343730411156365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51660092910895820274104243 77490139366343730411156365)
              ·
                refine ⟨29058802262378898904183637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77490139366343730411156365 29058802262378898904183637)
                ·
                  refine ⟨170266419506126360766701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29058802262378898904183637 170266419506126360766701)
                  ·
                    rfl

theorem cell22_1492167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 9].length) (baseStart_1492167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492167 prefixEnd_1492167 := by exact prefixLift 1492167
  have htrace : WordTrace (prefixWord ++ tailWord_1492167) baseStart_1492167 baseEnd_1492167 := by
    simpa [prefixWord, tailWord_1492167, baseEnd_1492167] using wordTrace_append hprefix tailTrace_1492167
  have hstable : (prefixWord ++ tailWord_1492167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492167).length < 2 ^ (prefixWord ++ tailWord_1492167).sum := by decide
  have hdescent : baseEnd_1492167 < baseStart_1492167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492173 : List Nat := [1, 6, 2, 2, 2, 9]
def baseStart_1492173 : Nat := 118140960795 + 1492173 * 2 ^ 59
def prefixEnd_1492173 : Nat := 4983230072969 + 3 ^ 40 * 1492173 * 2
def baseEnd_1492173 : Nat := 6306189042481445267285

theorem tailTrace_1492173 : CollatzResearch.WordTrace tailWord_1492173 prefixEnd_1492173 6306189042481445267285 := by
  unfold tailWord_1492173
  simp only [CollatzResearch.WordTrace]
  refine ⟨54424020423119538704433173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36282680282079692469622115 54424020423119538704433173)
  ·
    refine ⟨2551125957333728376770305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54424020423119538704433173 2551125957333728376770305)
    ·
      refine ⟨1913344468000296282577729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2551125957333728376770305 1913344468000296282577729)
      ·
        refine ⟨1435008351000222211933297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1913344468000296282577729 1435008351000222211933297)
        ·
          refine ⟨1076256263250166658949973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1435008351000222211933297 1076256263250166658949973)
          ·
            refine ⟨6306189042481445267285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1076256263250166658949973 6306189042481445267285)
            ·
              rfl

theorem cell22_1492173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 9].length) (baseStart_1492173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492173 prefixEnd_1492173 := by exact prefixLift 1492173
  have htrace : WordTrace (prefixWord ++ tailWord_1492173) baseStart_1492173 baseEnd_1492173 := by
    simpa [prefixWord, tailWord_1492173, baseEnd_1492173] using wordTrace_append hprefix tailTrace_1492173
  have hstable : (prefixWord ++ tailWord_1492173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492173).length < 2 ^ (prefixWord ++ tailWord_1492173).sum := by decide
  have hdescent : baseEnd_1492173 < baseStart_1492173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492259 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 1, 6]
def baseStart_1492259 : Nat := 118140960795 + 1492259 * 2 ^ 59
def prefixEnd_1492259 : Nat := 4983230072969 + 3 ^ 40 * 1492259 * 2
def baseEnd_1492259 : Nat := 510830751998521508999821

theorem tailTrace_1492259 : CollatzResearch.WordTrace tailWord_1492259 prefixEnd_1492259 510830751998521508999821 := by
  unfold tailWord_1492259
  simp only [CollatzResearch.WordTrace]
  refine ⟨54427157100807975392063831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36284771400538650261375887 54427157100807975392063831)
  ·
    refine ⟨81640735651211963088095747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54427157100807975392063831 81640735651211963088095747)
    ·
      refine ⟨122461103476817944632143621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81640735651211963088095747 122461103476817944632143621)
      ·
        refine ⟨22961456901903364618526929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122461103476817944632143621 22961456901903364618526929)
        ·
          refine ⟨17221092676427523463895197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22961456901903364618526929 17221092676427523463895197)
          ·
            refine ⟨6457909753660321298960699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17221092676427523463895197 6457909753660321298960699)
            ·
              refine ⟨9686864630490481948441049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6457909753660321298960699 9686864630490481948441049)
              ·
                refine ⟨7265148472867861461330787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9686864630490481948441049 7265148472867861461330787)
                ·
                  refine ⟨10897722709301792191996181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7265148472867861461330787 10897722709301792191996181)
                  ·
                    refine ⟨510830751998521508999821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10897722709301792191996181 510830751998521508999821)
                    ·
                      rfl

theorem cell22_1492259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_1492259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492259 prefixEnd_1492259 := by exact prefixLift 1492259
  have htrace : WordTrace (prefixWord ++ tailWord_1492259) baseStart_1492259 baseEnd_1492259 := by
    simpa [prefixWord, tailWord_1492259, baseEnd_1492259] using wordTrace_append hprefix tailTrace_1492259
  have hstable : (prefixWord ++ tailWord_1492259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492259).length < 2 ^ (prefixWord ++ tailWord_1492259).sum := by decide
  have hdescent : baseEnd_1492259 < baseStart_1492259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492261 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_1492261 : Nat := 118140960795 + 1492261 * 2 ^ 59
def prefixEnd_1492261 : Nat := 4983230072969 + 3 ^ 40 * 1492261 * 2
def baseEnd_1492261 : Nat := 510831436639394170449815

theorem tailTrace_1492261 : CollatzResearch.WordTrace tailWord_1492261 prefixEnd_1492261 510831436639394170449815 := by
  unfold tailWord_1492261
  simp only [CollatzResearch.WordTrace]
  refine ⟨54427230046800729733636637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36284820031200486489091091 54427230046800729733636637)
  ·
    refine ⟨20410211267550273650113739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54427230046800729733636637 20410211267550273650113739)
    ·
      refine ⟨30615316901325410475170609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20410211267550273650113739 30615316901325410475170609)
      ·
        refine ⟨22961487675994057856377957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30615316901325410475170609 22961487675994057856377957)
        ·
          refine ⟨4305278939248885848070867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22961487675994057856377957 4305278939248885848070867)
          ·
            refine ⟨6457918408873328772106301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305278939248885848070867 6457918408873328772106301)
            ·
              refine ⟨2421719403327498289539863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6457918408873328772106301 2421719403327498289539863)
              ·
                refine ⟨3632579104991247434309795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421719403327498289539863 3632579104991247434309795)
                ·
                  refine ⟨5448868657486871151464693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632579104991247434309795 5448868657486871151464693)
                  ·
                    refine ⟨510831436639394170449815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5448868657486871151464693 510831436639394170449815)
                    ·
                      rfl

theorem cell22_1492261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_1492261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492261 prefixEnd_1492261 := by exact prefixLift 1492261
  have htrace : WordTrace (prefixWord ++ tailWord_1492261) baseStart_1492261 baseEnd_1492261 := by
    simpa [prefixWord, tailWord_1492261, baseEnd_1492261] using wordTrace_append hprefix tailTrace_1492261
  have hstable : (prefixWord ++ tailWord_1492261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492261).length < 2 ^ (prefixWord ++ tailWord_1492261).sum := by decide
  have hdescent : baseEnd_1492261 < baseStart_1492261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492276 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1492276 : Nat := 118140960795 + 1492276 * 2 ^ 59
def prefixEnd_1492276 : Nat := 4983230072969 + 3 ^ 40 * 1492276 * 2
def baseEnd_1492276 : Nat := 510836571445939131324769

theorem tailTrace_1492276 : CollatzResearch.WordTrace tailWord_1492276 prefixEnd_1492276 510836571445939131324769 := by
  unfold tailWord_1492276
  simp only [CollatzResearch.WordTrace]
  refine ⟨27213888570873193647716341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36285184761164258196955121 27213888570873193647716341)
  ·
    refine ⟨2551302053519361904473407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27213888570873193647716341 2551302053519361904473407)
    ·
      refine ⟨3826953080279042856710111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551302053519361904473407 3826953080279042856710111)
      ·
        refine ⟨5740429620418564285065167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3826953080279042856710111 5740429620418564285065167)
        ·
          refine ⟨8610644430627846427597751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5740429620418564285065167 8610644430627846427597751)
          ·
            refine ⟨12915966645941769641396627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8610644430627846427597751 12915966645941769641396627)
            ·
              refine ⟨19373949968912654462094941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12915966645941769641396627 19373949968912654462094941)
              ·
                refine ⟨7265231238342245423285603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19373949968912654462094941 7265231238342245423285603)
                ·
                  refine ⟨10897846857513368134928405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7265231238342245423285603 10897846857513368134928405)
                  ·
                    refine ⟨510836571445939131324769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10897846857513368134928405 510836571445939131324769)
                    ·
                      rfl

theorem cell22_1492276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1492276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492276 prefixEnd_1492276 := by exact prefixLift 1492276
  have htrace : WordTrace (prefixWord ++ tailWord_1492276) baseStart_1492276 baseEnd_1492276 := by
    simpa [prefixWord, tailWord_1492276, baseEnd_1492276] using wordTrace_append hprefix tailTrace_1492276
  have hstable : (prefixWord ++ tailWord_1492276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492276).length < 2 ^ (prefixWord ++ tailWord_1492276).sum := by decide
  have hdescent : baseEnd_1492276 < baseStart_1492276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492304 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_1492304 : Nat := 118140960795 + 1492304 * 2 ^ 59
def prefixEnd_1492304 : Nat := 4983230072969 + 3 ^ 40 * 1492304 * 2
def baseEnd_1492304 : Nat := 510846156418156391624683

theorem tailTrace_1492304 : CollatzResearch.WordTrace tailWord_1492304 prefixEnd_1492304 510846156418156391624683 := by
  unfold tailWord_1492304
  simp only [CollatzResearch.WordTrace]
  refine ⟨27214399192822474038725983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36285865590429965384967977 27214399192822474038725983)
  ·
    refine ⟨40821598789233711058088975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27214399192822474038725983 40821598789233711058088975)
    ·
      refine ⟨61232398183850566587133463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40821598789233711058088975 61232398183850566587133463)
      ·
        refine ⟨91848597275775849880700195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61232398183850566587133463 91848597275775849880700195)
        ·
          refine ⟨137772895913663774821050293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91848597275775849880700195 137772895913663774821050293)
          ·
            refine ⟨12916208991905978889473465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137772895913663774821050293 12916208991905978889473465)
            ·
              refine ⟨9687156743929484167105099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12916208991905978889473465 9687156743929484167105099)
              ·
                refine ⟨14530735115894226250657649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9687156743929484167105099 14530735115894226250657649)
                ·
                  refine ⟨10898051336920669687993237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14530735115894226250657649 10898051336920669687993237)
                  ·
                    refine ⟨510846156418156391624683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10898051336920669687993237 510846156418156391624683)
                    ·
                      rfl

theorem cell22_1492304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_1492304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492304 prefixEnd_1492304 := by exact prefixLift 1492304
  have htrace : WordTrace (prefixWord ++ tailWord_1492304) baseStart_1492304 baseEnd_1492304 := by
    simpa [prefixWord, tailWord_1492304, baseEnd_1492304] using wordTrace_append hprefix tailTrace_1492304
  have hstable : (prefixWord ++ tailWord_1492304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492304).length < 2 ^ (prefixWord ++ tailWord_1492304).sum := by decide
  have hdescent : baseEnd_1492304 < baseStart_1492304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492381 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 8]
def baseStart_1492381 : Nat := 118140960795 + 1492381 * 2 ^ 59
def prefixEnd_1492381 : Nat := 4983230072969 + 3 ^ 40 * 1492381 * 2
def baseEnd_1492381 : Nat := 170290838363917952483149

theorem tailTrace_1492381 : CollatzResearch.WordTrace tailWord_1492381 prefixEnd_1492381 170290838363917952483149 := by
  unfold tailWord_1492381
  simp only [CollatzResearch.WordTrace]
  refine ⟨54431606806365990228004997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36287737870910660152003331 54431606806365990228004997)
  ·
    refine ⟨10205926276193623167750937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54431606806365990228004997 10205926276193623167750937)
    ·
      refine ⟨7654444707145217375813203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10205926276193623167750937 7654444707145217375813203)
      ·
        refine ⟨11481667060717826063719805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7654444707145217375813203 11481667060717826063719805)
        ·
          refine ⟨4305625147769184773894927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11481667060717826063719805 4305625147769184773894927)
          ·
            refine ⟨6458437721653777160842391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305625147769184773894927 6458437721653777160842391)
            ·
              refine ⟨9687656582480665741263587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6458437721653777160842391 9687656582480665741263587)
              ·
                refine ⟨14531484873720998611895381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9687656582480665741263587 14531484873720998611895381)
                ·
                  refine ⟨170290838363917952483149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14531484873720998611895381 170290838363917952483149)
                  ·
                    rfl

theorem cell22_1492381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_1492381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492381 prefixEnd_1492381 := by exact prefixLift 1492381
  have htrace : WordTrace (prefixWord ++ tailWord_1492381) baseStart_1492381 baseEnd_1492381 := by
    simpa [prefixWord, tailWord_1492381, baseEnd_1492381] using wordTrace_append hprefix tailTrace_1492381
  have hstable : (prefixWord ++ tailWord_1492381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492381).length < 2 ^ (prefixWord ++ tailWord_1492381).sum := by decide
  have hdescent : baseEnd_1492381 < baseStart_1492381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492396 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_1492396 : Nat := 118140960795 + 1492396 * 2 ^ 59
def prefixEnd_1492396 : Nat := 4983230072969 + 3 ^ 40 * 1492396 * 2
def baseEnd_1492396 : Nat := 510877649898298818324401

theorem tailTrace_1492396 : CollatzResearch.WordTrace tailWord_1492396 prefixEnd_1492396 510877649898298818324401 := by
  unfold tailWord_1492396
  simp only [CollatzResearch.WordTrace]
  refine ⟨27216076950655823894900521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36288102600874431859867361 27216076950655823894900521)
  ·
    refine ⟨20412057712991867921175391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27216076950655823894900521 20412057712991867921175391)
    ·
      refine ⟨30618086569487801881763087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20412057712991867921175391 30618086569487801881763087)
      ·
        refine ⟨45927129854231702822644631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30618086569487801881763087 45927129854231702822644631)
        ·
          refine ⟨68890694781347554233966947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45927129854231702822644631 68890694781347554233966947)
          ·
            refine ⟨103336042172021331350950421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68890694781347554233966947 103336042172021331350950421)
            ·
              refine ⟨4843876976813499907075801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103336042172021331350950421 4843876976813499907075801)
              ·
                refine ⟨3632907732610124930306851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4843876976813499907075801 3632907732610124930306851)
                ·
                  refine ⟨5449361598915187395460277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632907732610124930306851 5449361598915187395460277)
                  ·
                    refine ⟨510877649898298818324401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5449361598915187395460277 510877649898298818324401)
                    ·
                      rfl

theorem cell22_1492396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_1492396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492396 prefixEnd_1492396 := by exact prefixLift 1492396
  have htrace : WordTrace (prefixWord ++ tailWord_1492396) baseStart_1492396 baseEnd_1492396 := by
    simpa [prefixWord, tailWord_1492396, baseEnd_1492396] using wordTrace_append hprefix tailTrace_1492396
  have hstable : (prefixWord ++ tailWord_1492396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492396).length < 2 ^ (prefixWord ++ tailWord_1492396).sum := by decide
  have hdescent : baseEnd_1492396 < baseStart_1492396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492413 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_1492413 : Nat := 118140960795 + 1492413 * 2 ^ 59
def prefixEnd_1492413 : Nat := 4983230072969 + 3 ^ 40 * 1492413 * 2
def baseEnd_1492413 : Nat := 510883469345716440649349

theorem tailTrace_1492413 : CollatzResearch.WordTrace tailWord_1492413 prefixEnd_1492413 510883469345716440649349 := by
  unfold tailWord_1492413
  simp only [CollatzResearch.WordTrace]
  refine ⟨54432773942250059693169893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36288515961500039795446595 54432773942250059693169893)
  ·
    refine ⟨10206145114171886192469355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54432773942250059693169893 10206145114171886192469355)
    ·
      refine ⟨15309217671257829288704033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10206145114171886192469355 15309217671257829288704033)
      ·
        refine ⟨11481913253443371966528025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15309217671257829288704033 11481913253443371966528025)
        ·
          refine ⟨8611434940082528974896019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11481913253443371966528025 8611434940082528974896019)
          ·
            refine ⟨12917152410123793462344029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8611434940082528974896019 12917152410123793462344029)
            ·
              refine ⟨4843932153796422548379011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12917152410123793462344029 4843932153796422548379011)
              ·
                refine ⟨7265898230694633822568517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4843932153796422548379011 7265898230694633822568517)
                ·
                  refine ⟨1362355918255243841731597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7265898230694633822568517 1362355918255243841731597)
                  ·
                    refine ⟨510883469345716440649349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1362355918255243841731597 510883469345716440649349)
                    ·
                      rfl

theorem cell22_1492413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_1492413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492413 prefixEnd_1492413 := by exact prefixLift 1492413
  have htrace : WordTrace (prefixWord ++ tailWord_1492413) baseStart_1492413 baseEnd_1492413 := by
    simpa [prefixWord, tailWord_1492413, baseEnd_1492413] using wordTrace_append hprefix tailTrace_1492413
  have hstable : (prefixWord ++ tailWord_1492413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492413).length < 2 ^ (prefixWord ++ tailWord_1492413).sum := by decide
  have hdescent : baseEnd_1492413 < baseStart_1492413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492526 : List Nat := [4, 1, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1492526 : Nat := 118140960795 + 1492526 * 2 ^ 59
def prefixEnd_1492526 : Nat := 4983230072969 + 3 ^ 40 * 1492526 * 2
def baseEnd_1492526 : Nat := 510922151555021812574003

theorem tailTrace_1492526 : CollatzResearch.WordTrace tailWord_1492526 prefixEnd_1492526 510922151555021812574003 := by
  unfold tailWord_1492526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804611923855084999004179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36291263593893786661355621 6804611923855084999004179)
  ·
    refine ⟨10206917885782627498506269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6804611923855084999004179 10206917885782627498506269)
    ·
      refine ⟨3827594207168485311939851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10206917885782627498506269 3827594207168485311939851)
      ·
        refine ⟨5741391310752727967909777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827594207168485311939851 5741391310752727967909777)
        ·
          refine ⟨4306043483064545975932333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5741391310752727967909777 4306043483064545975932333)
          ·
            refine ⟨1614766306149204740974625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4306043483064545975932333 1614766306149204740974625)
            ·
              refine ⟨1211074729611903555730969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1614766306149204740974625 1211074729611903555730969)
              ·
                refine ⟨908306047208927666798227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211074729611903555730969 908306047208927666798227)
                ·
                  refine ⟨1362459070813391500197341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908306047208927666798227 1362459070813391500197341)
                  ·
                    refine ⟨510922151555021812574003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1362459070813391500197341 510922151555021812574003)
                    ·
                      rfl

theorem cell22_1492526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1492526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492526 prefixEnd_1492526 := by exact prefixLift 1492526
  have htrace : WordTrace (prefixWord ++ tailWord_1492526) baseStart_1492526 baseEnd_1492526 := by
    simpa [prefixWord, tailWord_1492526, baseEnd_1492526] using wordTrace_append hprefix tailTrace_1492526
  have hstable : (prefixWord ++ tailWord_1492526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492526).length < 2 ^ (prefixWord ++ tailWord_1492526).sum := by decide
  have hdescent : baseEnd_1492526 < baseStart_1492526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492612 : List Nat := [2, 3, 2, 1, 4, 2, 2, 6]
def baseStart_1492612 : Nat := 118140960795 + 1492612 * 2 ^ 59
def prefixEnd_1492612 : Nat := 4983230072969 + 3 ^ 40 * 1492612 * 2
def baseEnd_1492612 : Nat := 56772399012505139435971

theorem tailTrace_1492612 : CollatzResearch.WordTrace tailWord_1492612 prefixEnd_1492612 56772399012505139435971 := by
  unfold tailWord_1492612
  simp only [CollatzResearch.WordTrace]
  refine ⟨27220016034264558339832045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36293354712352744453109393 27220016034264558339832045)
  ·
    refine ⟨10207506012849209377437017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27220016034264558339832045 10207506012849209377437017)
    ·
      refine ⟨7655629509636907033077763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10207506012849209377437017 7655629509636907033077763)
      ·
        refine ⟨11483444264455360549616645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7655629509636907033077763 11483444264455360549616645)
        ·
          refine ⟨2153145799585380103053121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11483444264455360549616645 2153145799585380103053121)
          ·
            refine ⟨1614859349689035077289841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153145799585380103053121 1614859349689035077289841)
            ·
              refine ⟨1211144512266776307967381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1614859349689035077289841 1211144512266776307967381)
              ·
                refine ⟨56772399012505139435971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1211144512266776307967381 56772399012505139435971)
                ·
                  rfl

theorem cell22_1492612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 6].length) (baseStart_1492612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492612 prefixEnd_1492612 := by exact prefixLift 1492612
  have htrace : WordTrace (prefixWord ++ tailWord_1492612) baseStart_1492612 baseEnd_1492612 := by
    simpa [prefixWord, tailWord_1492612, baseEnd_1492612] using wordTrace_append hprefix tailTrace_1492612
  have hstable : (prefixWord ++ tailWord_1492612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492612).length < 2 ^ (prefixWord ++ tailWord_1492612).sum := by decide
  have hdescent : baseEnd_1492612 < baseStart_1492612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492717 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_1492717 : Nat := 118140960795 + 1492717 * 2 ^ 59
def prefixEnd_1492717 : Nat := 4983230072969 + 3 ^ 40 * 1492717 * 2
def baseEnd_1492717 : Nat := 510987534758360981048417

theorem tailTrace_1492717 : CollatzResearch.WordTrace tailWord_1492717 prefixEnd_1492717 510987534758360981048417 := by
  unfold tailWord_1492717
  simp only [CollatzResearch.WordTrace]
  refine ⟨54443861733148719612236405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36295907822099146408157603 54443861733148719612236405)
  ·
    refine ⟨5104112037482692463647163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54443861733148719612236405 5104112037482692463647163)
    ·
      refine ⟨7656168056224038695470745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5104112037482692463647163 7656168056224038695470745)
      ·
        refine ⟨5742126042168029021603059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7656168056224038695470745 5742126042168029021603059)
        ·
          refine ⟨8613189063252043532404589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5742126042168029021603059 8613189063252043532404589)
          ·
            refine ⟨3229945898719516324651721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8613189063252043532404589 3229945898719516324651721)
            ·
              refine ⟨2422459424039637243488791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3229945898719516324651721 2422459424039637243488791)
              ·
                refine ⟨3633689136059455865233187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422459424039637243488791 3633689136059455865233187)
                ·
                  refine ⟨5450533704089183797849781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3633689136059455865233187 5450533704089183797849781)
                  ·
                    refine ⟨510987534758360981048417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5450533704089183797849781 510987534758360981048417)
                    ·
                      rfl

theorem cell22_1492717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_1492717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492717 prefixEnd_1492717 := by exact prefixLift 1492717
  have htrace : WordTrace (prefixWord ++ tailWord_1492717) baseStart_1492717 baseEnd_1492717 := by
    simpa [prefixWord, tailWord_1492717, baseEnd_1492717] using wordTrace_append hprefix tailTrace_1492717
  have hstable : (prefixWord ++ tailWord_1492717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492717).length < 2 ^ (prefixWord ++ tailWord_1492717).sum := by decide
  have hdescent : baseEnd_1492717 < baseStart_1492717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492728 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_1492728 : Nat := 118140960795 + 1492728 * 2 ^ 59
def prefixEnd_1492728 : Nat := 4983230072969 + 3 ^ 40 * 1492728 * 2
def baseEnd_1492728 : Nat := 510991300283160619023383

theorem tailTrace_1492728 : CollatzResearch.WordTrace tailWord_1492728 prefixEnd_1492728 510991300283160619023383 := by
  unfold tailWord_1492728
  simp only [CollatzResearch.WordTrace]
  refine ⟨27222131468054434245443419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36296175290739245660591225 27222131468054434245443419)
  ·
    refine ⟨40833197202081651368165129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27222131468054434245443419 40833197202081651368165129)
    ·
      refine ⟨30624897901561238526123847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40833197202081651368165129 30624897901561238526123847)
      ·
        refine ⟨45937346852341857789185771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30624897901561238526123847 45937346852341857789185771)
        ·
          refine ⟨68906020278512786683778657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45937346852341857789185771 68906020278512786683778657)
          ·
            refine ⟨51679515208884590012833993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68906020278512786683778657 51679515208884590012833993)
            ·
              refine ⟨38759636406663442509625495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51679515208884590012833993 38759636406663442509625495)
              ·
                refine ⟨58139454609995163764438243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38759636406663442509625495 58139454609995163764438243)
                ·
                  refine ⟨87209181914992745646657365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58139454609995163764438243 87209181914992745646657365)
                  ·
                    refine ⟨510991300283160619023383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 87209181914992745646657365 510991300283160619023383)
                    ·
                      rfl

theorem cell22_1492728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_1492728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492728 prefixEnd_1492728 := by exact prefixLift 1492728
  have htrace : WordTrace (prefixWord ++ tailWord_1492728) baseStart_1492728 baseEnd_1492728 := by
    simpa [prefixWord, tailWord_1492728, baseEnd_1492728] using wordTrace_append hprefix tailTrace_1492728
  have hstable : (prefixWord ++ tailWord_1492728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492728).length < 2 ^ (prefixWord ++ tailWord_1492728).sum := by decide
  have hdescent : baseEnd_1492728 < baseStart_1492728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492742 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1492742 : Nat := 118140960795 + 1492742 * 2 ^ 59
def prefixEnd_1492742 : Nat := 4983230072969 + 3 ^ 40 * 1492742 * 2
def baseEnd_1492742 : Nat := 170332030923089749724447

theorem tailTrace_1492742 : CollatzResearch.WordTrace tailWord_1492742 prefixEnd_1492742 170332030923089749724447 := by
  unfold tailWord_1492742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701399173689317152559265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36296515705372099254597653 1701399173689317152559265)
  ·
    refine ⟨1276049380266987864419449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1701399173689317152559265 1276049380266987864419449)
    ·
      refine ⟨957037035200240898314587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1276049380266987864419449 957037035200240898314587)
      ·
        refine ⟨1435555552800361347471881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957037035200240898314587 1435555552800361347471881)
        ·
          refine ⟨1076666664600271010603911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1435555552800361347471881 1076666664600271010603911)
          ·
            refine ⟨1614999996900406515905867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076666664600271010603911 1614999996900406515905867)
            ·
              refine ⟨2422499995350609773858801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614999996900406515905867 2422499995350609773858801)
              ·
                refine ⟨1816874996512957330394101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422499995350609773858801 1816874996512957330394101)
                ·
                  refine ⟨170332030923089749724447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1816874996512957330394101 170332030923089749724447)
                  ·
                    rfl

theorem cell22_1492742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1492742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492742 prefixEnd_1492742 := by exact prefixLift 1492742
  have htrace : WordTrace (prefixWord ++ tailWord_1492742) baseStart_1492742 baseEnd_1492742 := by
    simpa [prefixWord, tailWord_1492742, baseEnd_1492742] using wordTrace_append hprefix tailTrace_1492742
  have hstable : (prefixWord ++ tailWord_1492742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492742).length < 2 ^ (prefixWord ++ tailWord_1492742).sum := by decide
  have hdescent : baseEnd_1492742 < baseStart_1492742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492745 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 7, 3]
def baseStart_1492745 : Nat := 118140960795 + 1492745 * 2 ^ 59
def prefixEnd_1492745 : Nat := 4983230072969 + 3 ^ 40 * 1492745 * 2
def baseEnd_1492745 : Nat := 510997119730578241348331

theorem tailTrace_1492745 : CollatzResearch.WordTrace tailWord_1492745 prefixEnd_1492745 510997119730578241348331 := by
  unfold tailWord_1492745
  simp only [CollatzResearch.WordTrace]
  refine ⟨54444882977047280394255689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36296588651364853596170459 54444882977047280394255689)
  ·
    refine ⟨40833662232785460295691767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54444882977047280394255689 40833662232785460295691767)
    ·
      refine ⟨61250493349178190443537651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40833662232785460295691767 61250493349178190443537651)
      ·
        refine ⟨91875740023767285665306477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61250493349178190443537651 91875740023767285665306477)
        ·
          refine ⟨34453402508912732124489929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91875740023767285665306477 34453402508912732124489929)
          ·
            refine ⟨25840051881684549093367447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34453402508912732124489929 25840051881684549093367447)
            ·
              refine ⟨38760077822526823640051171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25840051881684549093367447 38760077822526823640051171)
              ·
                refine ⟨58140116733790235460076757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38760077822526823640051171 58140116733790235460076757)
                ·
                  refine ⟨1362658985948208643595549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 58140116733790235460076757 1362658985948208643595549)
                  ·
                    refine ⟨510997119730578241348331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1362658985948208643595549 510997119730578241348331)
                    ·
                      rfl

theorem cell22_1492745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 3].length) (baseStart_1492745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492745 prefixEnd_1492745 := by exact prefixLift 1492745
  have htrace : WordTrace (prefixWord ++ tailWord_1492745) baseStart_1492745 baseEnd_1492745 := by
    simpa [prefixWord, tailWord_1492745, baseEnd_1492745] using wordTrace_append hprefix tailTrace_1492745
  have hstable : (prefixWord ++ tailWord_1492745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492745).length < 2 ^ (prefixWord ++ tailWord_1492745).sum := by decide
  have hdescent : baseEnd_1492745 < baseStart_1492745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492762 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 3, 3]
def baseStart_1492762 : Nat := 118140960795 + 1492762 * 2 ^ 59
def prefixEnd_1492762 : Nat := 4983230072969 + 3 ^ 40 * 1492762 * 2
def baseEnd_1492762 : Nat := 511002939177995863673279

theorem tailTrace_1492762 : CollatzResearch.WordTrace tailWord_1492762 prefixEnd_1492762 511002939177995863673279 := by
  unfold tailWord_1492762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13611375754496423074406135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36297002011990461531749693 13611375754496423074406135)
  ·
    refine ⟨20417063631744634611609203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13611375754496423074406135 20417063631744634611609203)
    ·
      refine ⟨30625595447616951917413805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20417063631744634611609203 30625595447616951917413805)
      ·
        refine ⟨11484598292856356969030177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30625595447616951917413805 11484598292856356969030177)
        ·
          refine ⟨8613448719642267726772633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11484598292856356969030177 8613448719642267726772633)
          ·
            refine ⟨6460086539731700795079475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8613448719642267726772633 6460086539731700795079475)
            ·
              refine ⟨9690129809597551192619213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460086539731700795079475 9690129809597551192619213)
              ·
                refine ⟨3633798678599081697232205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9690129809597551192619213 3633798678599081697232205)
                ·
                  refine ⟨1362674504474655636462077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3633798678599081697232205 1362674504474655636462077)
                  ·
                    refine ⟨511002939177995863673279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1362674504474655636462077 511002939177995863673279)
                    ·
                      rfl

theorem cell22_1492762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_1492762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492762 prefixEnd_1492762 := by exact prefixLift 1492762
  have htrace : WordTrace (prefixWord ++ tailWord_1492762) baseStart_1492762 baseEnd_1492762 := by
    simpa [prefixWord, tailWord_1492762, baseEnd_1492762] using wordTrace_append hprefix tailTrace_1492762
  have hstable : (prefixWord ++ tailWord_1492762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492762).length < 2 ^ (prefixWord ++ tailWord_1492762).sum := by decide
  have hdescent : baseEnd_1492762 < baseStart_1492762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492867 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 2, 4]
def baseStart_1492867 : Nat := 118140960795 + 1492867 * 2 ^ 59
def prefixEnd_1492867 : Nat := 4983230072969 + 3 ^ 40 * 1492867 * 2
def baseEnd_1492867 : Nat := 511038882823810589797957

theorem tailTrace_1492867 : CollatzResearch.WordTrace tailWord_1492867 prefixEnd_1492867 511038882823810589797957 := by
  unfold tailWord_1492867
  simp only [CollatzResearch.WordTrace]
  refine ⟨54449332682605295230196855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36299555121736863486797903 54449332682605295230196855)
  ·
    refine ⟨81673999023907942845295283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54449332682605295230196855 81673999023907942845295283)
    ·
      refine ⟨122510998535861914267942925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81673999023907942845295283 122510998535861914267942925)
      ·
        refine ⟨45941624450948217850478597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122510998535861914267942925 45941624450948217850478597)
        ·
          refine ⟨8614054584552790846964737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45941624450948217850478597 8614054584552790846964737)
          ·
            refine ⟨6460540938414593135223553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8614054584552790846964737 6460540938414593135223553)
            ·
              refine ⟨4845405703810944851417665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6460540938414593135223553 4845405703810944851417665)
              ·
                refine ⟨3634054277858208638563249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4845405703810944851417665 3634054277858208638563249)
                ·
                  refine ⟨2725540708393656478922437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3634054277858208638563249 2725540708393656478922437)
                  ·
                    refine ⟨511038882823810589797957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2725540708393656478922437 511038882823810589797957)
                    ·
                      rfl

theorem cell22_1492867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 4].length) (baseStart_1492867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492867 prefixEnd_1492867 := by exact prefixLift 1492867
  have htrace : WordTrace (prefixWord ++ tailWord_1492867) baseStart_1492867 baseEnd_1492867 := by
    simpa [prefixWord, tailWord_1492867, baseEnd_1492867] using wordTrace_append hprefix tailTrace_1492867
  have hstable : (prefixWord ++ tailWord_1492867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492867).length < 2 ^ (prefixWord ++ tailWord_1492867).sum := by decide
  have hdescent : baseEnd_1492867 < baseStart_1492867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492869 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 2, 3]
def baseStart_1492869 : Nat := 118140960795 + 1492869 * 2 ^ 59
def prefixEnd_1492869 : Nat := 4983230072969 + 3 ^ 40 * 1492869 * 2
def baseEnd_1492869 : Nat := 511039567464683251247951

theorem tailTrace_1492869 : CollatzResearch.WordTrace tailWord_1492869 prefixEnd_1492869 511039567464683251247951 := by
  unfold tailWord_1492869
  simp only [CollatzResearch.WordTrace]
  refine ⟨54449405628598049571769661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36299603752398699714513107 54449405628598049571769661)
  ·
    refine ⟨20418527110724268589413623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54449405628598049571769661 20418527110724268589413623)
    ·
      refine ⟨30627790666086402884120435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20418527110724268589413623 30627790666086402884120435)
      ·
        refine ⟨45941685999129604326180653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30627790666086402884120435 45941685999129604326180653)
        ·
          refine ⟨17228132249673601622317745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45941685999129604326180653 17228132249673601622317745)
          ·
            refine ⟨12921099187255201216738309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17228132249673601622317745 12921099187255201216738309)
            ·
              refine ⟨2422706097610350228138433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12921099187255201216738309 2422706097610350228138433)
              ·
                refine ⟨1817029573207762671103825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422706097610350228138433 1817029573207762671103825)
                ·
                  refine ⟨1362772179905822003327869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1817029573207762671103825 1362772179905822003327869)
                  ·
                    refine ⟨511039567464683251247951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1362772179905822003327869 511039567464683251247951)
                    ·
                      rfl

theorem cell22_1492869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_1492869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492869 prefixEnd_1492869 := by exact prefixLift 1492869
  have htrace : WordTrace (prefixWord ++ tailWord_1492869) baseStart_1492869 baseEnd_1492869 := by
    simpa [prefixWord, tailWord_1492869, baseEnd_1492869] using wordTrace_append hprefix tailTrace_1492869
  have hstable : (prefixWord ++ tailWord_1492869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492869).length < 2 ^ (prefixWord ++ tailWord_1492869).sum := by decide
  have hdescent : baseEnd_1492869 < baseStart_1492869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492942 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1492942 : Nat := 118140960795 + 1492942 * 2 ^ 59
def prefixEnd_1492942 : Nat := 4983230072969 + 3 ^ 40 * 1492942 * 2
def baseEnd_1492942 : Nat := 511064556856535394172727

theorem tailTrace_1492942 : CollatzResearch.WordTrace tailWord_1492942 prefixEnd_1492942 511064556856535394172727 := by
  unfold tailWord_1492942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806508519666697879897135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36301378771555722026118053 6806508519666697879897135)
  ·
    refine ⟨10209762779500046819845703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6806508519666697879897135 10209762779500046819845703)
    ·
      refine ⟨15314644169250070229768555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10209762779500046819845703 15314644169250070229768555)
      ·
        refine ⟨22971966253875105344652833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15314644169250070229768555 22971966253875105344652833)
        ·
          refine ⟨17228974690406329008489625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22971966253875105344652833 17228974690406329008489625)
          ·
            refine ⟨12921731017804746756367219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17228974690406329008489625 12921731017804746756367219)
            ·
              refine ⟨19382596526707120134550829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12921731017804746756367219 19382596526707120134550829)
              ·
                refine ⟨7268473697515170050456561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19382596526707120134550829 7268473697515170050456561)
                ·
                  refine ⟨5451355273136377537842421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7268473697515170050456561 5451355273136377537842421)
                  ·
                    refine ⟨511064556856535394172727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5451355273136377537842421 511064556856535394172727)
                    ·
                      rfl

theorem cell22_1492942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1492942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492942 prefixEnd_1492942 := by exact prefixLift 1492942
  have htrace : WordTrace (prefixWord ++ tailWord_1492942) baseStart_1492942 baseEnd_1492942 := by
    simpa [prefixWord, tailWord_1492942, baseEnd_1492942] using wordTrace_append hprefix tailTrace_1492942
  have hstable : (prefixWord ++ tailWord_1492942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492942).length < 2 ^ (prefixWord ++ tailWord_1492942).sum := by decide
  have hdescent : baseEnd_1492942 < baseStart_1492942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492989 : List Nat := [1, 4, 1, 1, 1, 2, 2, 6, 4]
def baseStart_1492989 : Nat := 118140960795 + 1492989 * 2 ^ 59
def prefixEnd_1492989 : Nat := 4983230072969 + 3 ^ 40 * 1492989 * 2
def baseEnd_1492989 : Nat := 170360215305680979415861

theorem tailTrace_1492989 : CollatzResearch.WordTrace tailWord_1492989 prefixEnd_1492989 170360215305680979415861 := by
  unfold tailWord_1492989
  simp only [CollatzResearch.WordTrace]
  refine ⟨54453782388163310066138021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36302521592108873377425347 54453782388163310066138021)
  ·
    refine ⟨10210084197780620637400879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54453782388163310066138021 10210084197780620637400879)
    ·
      refine ⟨15315126296670930956101319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10210084197780620637400879 15315126296670930956101319)
      ·
        refine ⟨22972689445006396434151979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15315126296670930956101319 22972689445006396434151979)
        ·
          refine ⟨34459034167509594651227969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22972689445006396434151979 34459034167509594651227969)
          ·
            refine ⟨25844275625632195988420977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34459034167509594651227969 25844275625632195988420977)
            ·
              refine ⟨19383206719224146991315733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25844275625632195988420977 19383206719224146991315733)
              ·
                refine ⟨908587814963631890217925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19383206719224146991315733 908587814963631890217925)
                ·
                  refine ⟨170360215305680979415861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 908587814963631890217925 170360215305680979415861)
                  ·
                    rfl

theorem cell22_1492989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_1492989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1492989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1492989 prefixEnd_1492989 := by exact prefixLift 1492989
  have htrace : WordTrace (prefixWord ++ tailWord_1492989) baseStart_1492989 baseEnd_1492989 := by
    simpa [prefixWord, tailWord_1492989, baseEnd_1492989] using wordTrace_append hprefix tailTrace_1492989
  have hstable : (prefixWord ++ tailWord_1492989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492989).length < 2 ^ (prefixWord ++ tailWord_1492989).sum := by decide
  have hdescent : baseEnd_1492989 < baseStart_1492989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493038 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1493038 : Nat := 118140960795 + 1493038 * 2 ^ 59
def prefixEnd_1493038 : Nat := 4983230072969 + 3 ^ 40 * 1493038 * 2
def baseEnd_1493038 : Nat := 511097419618423143772433

theorem tailTrace_1493038 : CollatzResearch.WordTrace tailWord_1493038 prefixEnd_1493038 511097419618423143772433 := by
  unfold tailWord_1493038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806946195623223929333971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36303713043323860956447845 6806946195623223929333971)
  ·
    refine ⟨10210419293434835894000957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6806946195623223929333971 10210419293434835894000957)
    ·
      refine ⟨3828907235038063460250359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10210419293434835894000957 3828907235038063460250359)
      ·
        refine ⟨5743360852557095190375539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3828907235038063460250359 5743360852557095190375539)
        ·
          refine ⟨8615041278835642785563309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5743360852557095190375539 8615041278835642785563309)
          ·
            refine ⟨3230640479563366044586241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8615041278835642785563309 3230640479563366044586241)
            ·
              refine ⟨2422980359672524533439681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3230640479563366044586241 2422980359672524533439681)
              ·
                refine ⟨1817235269754393400079761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422980359672524533439681 1817235269754393400079761)
                ·
                  refine ⟨1362926452315795050059821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1817235269754393400079761 1362926452315795050059821)
                  ·
                    refine ⟨511097419618423143772433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1362926452315795050059821 511097419618423143772433)
                    ·
                      rfl

theorem cell22_1493038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1493038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493038 prefixEnd_1493038 := by exact prefixLift 1493038
  have htrace : WordTrace (prefixWord ++ tailWord_1493038) baseStart_1493038 baseEnd_1493038 := by
    simpa [prefixWord, tailWord_1493038, baseEnd_1493038] using wordTrace_append hprefix tailTrace_1493038
  have hstable : (prefixWord ++ tailWord_1493038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493038).length < 2 ^ (prefixWord ++ tailWord_1493038).sum := by decide
  have hdescent : baseEnd_1493038 < baseStart_1493038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493047 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1493047 : Nat := 118140960795 + 1493047 * 2 ^ 59
def prefixEnd_1493047 : Nat := 4983230072969 + 3 ^ 40 * 1493047 * 2
def baseEnd_1493047 : Nat := 511100500502350120297405

theorem tailTrace_1493047 : CollatzResearch.WordTrace tailWord_1493047 prefixEnd_1493047 511100500502350120297405 := by
  unfold tailWord_1493047
  simp only [CollatzResearch.WordTrace]
  refine ⟨54455897821953185971749395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36303931881302123981166263 54455897821953185971749395)
  ·
    refine ⟨81683846732929778957624093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54455897821953185971749395 81683846732929778957624093)
    ·
      refine ⟨30631442524848667109109035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81683846732929778957624093 30631442524848667109109035)
      ·
        refine ⟨45947163787273000663663553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30631442524848667109109035 45947163787273000663663553)
        ·
          refine ⟨34460372840454750497747665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45947163787273000663663553 34460372840454750497747665)
          ·
            refine ⟨25845279630341062873310749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34460372840454750497747665 25845279630341062873310749)
            ·
              refine ⟨9691979861377898577491531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25845279630341062873310749 9691979861377898577491531)
              ·
                refine ⟨14537969792066847866237297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9691979861377898577491531 14537969792066847866237297)
                ·
                  refine ⟨10903477344050135899677973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14537969792066847866237297 10903477344050135899677973)
                  ·
                    refine ⟨511100500502350120297405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10903477344050135899677973 511100500502350120297405)
                    ·
                      rfl

theorem cell22_1493047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1493047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493047 prefixEnd_1493047 := by exact prefixLift 1493047
  have htrace : WordTrace (prefixWord ++ tailWord_1493047) baseStart_1493047 baseEnd_1493047 := by
    simpa [prefixWord, tailWord_1493047, baseEnd_1493047] using wordTrace_append hprefix tailTrace_1493047
  have hstable : (prefixWord ++ tailWord_1493047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493047).length < 2 ^ (prefixWord ++ tailWord_1493047).sum := by decide
  have hdescent : baseEnd_1493047 < baseStart_1493047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493124 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 6]
def baseStart_1493124 : Nat := 118140960795 + 1493124 * 2 ^ 59
def prefixEnd_1493124 : Nat := 4983230072969 + 3 ^ 40 * 1493124 * 2
def baseEnd_1493124 : Nat := 170375619725315862040723

theorem tailTrace_1493124 : CollatzResearch.WordTrace tailWord_1493124 prefixEnd_1493124 170375619725315862040723 := by
  unfold tailWord_1493124
  simp only [CollatzResearch.WordTrace]
  refine ⟨27229353121337114061151213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36305804161782818748201617 27229353121337114061151213)
  ·
    refine ⟨10211007420501417772931705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27229353121337114061151213 10211007420501417772931705)
    ·
      refine ⟨7658255565376063329698779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10211007420501417772931705 7658255565376063329698779)
      ·
        refine ⟨11487383348064094994548169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7658255565376063329698779 11487383348064094994548169)
        ·
          refine ⟨8615537511048071245911127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11487383348064094994548169 8615537511048071245911127)
          ·
            refine ⟨12923306266572106868866691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8615537511048071245911127 12923306266572106868866691)
            ·
              refine ⟨19384959399858160303300037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12923306266572106868866691 19384959399858160303300037)
              ·
                refine ⟨3634679887473405056868757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19384959399858160303300037 3634679887473405056868757)
                ·
                  refine ⟨170375619725315862040723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3634679887473405056868757 170375619725315862040723)
                  ·
                    rfl

theorem cell22_1493124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_1493124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493124 prefixEnd_1493124 := by exact prefixLift 1493124
  have htrace : WordTrace (prefixWord ++ tailWord_1493124) baseStart_1493124 baseEnd_1493124 := by
    simpa [prefixWord, tailWord_1493124, baseEnd_1493124] using wordTrace_append hprefix tailTrace_1493124
  have hstable : (prefixWord ++ tailWord_1493124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493124).length < 2 ^ (prefixWord ++ tailWord_1493124).sum := by decide
  have hdescent : baseEnd_1493124 < baseStart_1493124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493188 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1493188 : Nat := 118140960795 + 1493188 * 2 ^ 59
def prefixEnd_1493188 : Nat := 4983230072969 + 3 ^ 40 * 1493188 * 2
def baseEnd_1493188 : Nat := 511148767683872752521973

theorem tailTrace_1493188 : CollatzResearch.WordTrace tailWord_1493188 prefixEnd_1493188 511148767683872752521973 := by
  unfold tailWord_1493188
  simp only [CollatzResearch.WordTrace]
  refine ⟨27230520257221183526316109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36307360342961578035088145 27230520257221183526316109)
  ·
    refine ⟨10211445096457943822368541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27230520257221183526316109 10211445096457943822368541)
    ·
      refine ⟨3829291911171728933388203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10211445096457943822368541 3829291911171728933388203)
      ·
        refine ⟨5743937866757593400082305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829291911171728933388203 5743937866757593400082305)
        ·
          refine ⟨4307953400068195050061729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5743937866757593400082305 4307953400068195050061729)
          ·
            refine ⟨3230965050051146287546297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4307953400068195050061729 3230965050051146287546297)
            ·
              refine ⟨2423223787538359715659723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3230965050051146287546297 2423223787538359715659723)
              ·
                refine ⟨3634835681307539573489585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423223787538359715659723 3634835681307539573489585)
                ·
                  refine ⟨2726126760980654680117189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3634835681307539573489585 2726126760980654680117189)
                  ·
                    refine ⟨511148767683872752521973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2726126760980654680117189 511148767683872752521973)
                    ·
                      rfl

theorem cell22_1493188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1493188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493188 prefixEnd_1493188 := by exact prefixLift 1493188
  have htrace : WordTrace (prefixWord ++ tailWord_1493188) baseStart_1493188 baseEnd_1493188 := by
    simpa [prefixWord, tailWord_1493188, baseEnd_1493188] using wordTrace_append hprefix tailTrace_1493188
  have hstable : (prefixWord ++ tailWord_1493188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493188).length < 2 ^ (prefixWord ++ tailWord_1493188).sum := by decide
  have hdescent : baseEnd_1493188 < baseStart_1493188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493231 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 5]
def baseStart_1493231 : Nat := 118140960795 + 1493231 * 2 ^ 59
def prefixEnd_1493231 : Nat := 4983230072969 + 3 ^ 40 * 1493231 * 2
def baseEnd_1493231 : Nat := 170387829154211657898947

theorem tailTrace_1493231 : CollatzResearch.WordTrace tailWord_1493231 prefixEnd_1493231 170387829154211657898947 := by
  unfold tailWord_1493231
  simp only [CollatzResearch.WordTrace]
  refine ⟨54462608853286585396447547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36308405902191056930965031 54462608853286585396447547)
  ·
    refine ⟨81693913279929878094671321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54462608853286585396447547 81693913279929878094671321)
    ·
      refine ⟨61270434959947408571003491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81693913279929878094671321 61270434959947408571003491)
      ·
        refine ⟨91905652439921112856505237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61270434959947408571003491 91905652439921112856505237)
        ·
          refine ⟨4308077458121302165148683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91905652439921112856505237 4308077458121302165148683)
          ·
            refine ⟨6462116187181953247723025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308077458121302165148683 6462116187181953247723025)
            ·
              refine ⟨4846587140386464935792269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6462116187181953247723025 4846587140386464935792269)
              ·
                refine ⟨1817470177644924350922101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4846587140386464935792269 1817470177644924350922101)
                ·
                  refine ⟨170387829154211657898947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1817470177644924350922101 170387829154211657898947)
                  ·
                    rfl

theorem cell22_1493231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 5].length) (baseStart_1493231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493231 prefixEnd_1493231 := by exact prefixLift 1493231
  have htrace : WordTrace (prefixWord ++ tailWord_1493231) baseStart_1493231 baseEnd_1493231 := by
    simpa [prefixWord, tailWord_1493231, baseEnd_1493231] using wordTrace_append hprefix tailTrace_1493231
  have hstable : (prefixWord ++ tailWord_1493231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493231).length < 2 ^ (prefixWord ++ tailWord_1493231).sum := by decide
  have hdescent : baseEnd_1493231 < baseStart_1493231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493246 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1493246 : Nat := 118140960795 + 1493246 * 2 ^ 59
def prefixEnd_1493246 : Nat := 4983230072969 + 3 ^ 40 * 1493246 * 2
def baseEnd_1493246 : Nat := 511168622269179934571795

theorem tailTrace_1493246 : CollatzResearch.WordTrace tailWord_1493246 prefixEnd_1493246 511168622269179934571795 := by
  unfold tailWord_1493246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6807894493529030369780449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36308770632154828638829061 6807894493529030369780449)
  ·
    refine ⟨5105920870146772777335337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6807894493529030369780449 5105920870146772777335337)
    ·
      refine ⟨3829440652610079583001503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5105920870146772777335337 3829440652610079583001503)
      ·
        refine ⟨5744160978915119374502255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829440652610079583001503 5744160978915119374502255)
        ·
          refine ⟨8616241468372679061753383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744160978915119374502255 8616241468372679061753383)
          ·
            refine ⟨12924362202559018592630075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8616241468372679061753383 12924362202559018592630075)
            ·
              refine ⟨19386543303838527888945113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12924362202559018592630075 19386543303838527888945113)
              ·
                refine ⟨14539907477878895916708835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19386543303838527888945113 14539907477878895916708835)
                ·
                  refine ⟨21809861216818343875063253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14539907477878895916708835 21809861216818343875063253)
                  ·
                    refine ⟨511168622269179934571795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21809861216818343875063253 511168622269179934571795)
                    ·
                      rfl

theorem cell22_1493246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1493246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493246 prefixEnd_1493246 := by exact prefixLift 1493246
  have htrace : WordTrace (prefixWord ++ tailWord_1493246) baseStart_1493246 baseEnd_1493246 := by
    simpa [prefixWord, tailWord_1493246, baseEnd_1493246] using wordTrace_append hprefix tailTrace_1493246
  have hstable : (prefixWord ++ tailWord_1493246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493246).length < 2 ^ (prefixWord ++ tailWord_1493246).sum := by decide
  have hdescent : baseEnd_1493246 < baseStart_1493246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493252 : List Nat := [2, 3, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_1493252 : Nat := 118140960795 + 1493252 * 2 ^ 59
def prefixEnd_1493252 : Nat := 4983230072969 + 3 ^ 40 * 1493252 * 2
def baseEnd_1493252 : Nat := 511170676191797918921777

theorem tailTrace_1493252 : CollatzResearch.WordTrace tailWord_1493252 prefixEnd_1493252 511170676191797918921777 := by
  unfold tailWord_1493252
  simp only [CollatzResearch.WordTrace]
  refine ⟨27231687393105252991481005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36308916524140337321974673 27231687393105252991481005)
  ·
    refine ⟨10211882772414469871805377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27231687393105252991481005 10211882772414469871805377)
    ·
      refine ⟨7658912079310852403854033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10211882772414469871805377 7658912079310852403854033)
      ·
        refine ⟨5744184059483139302890525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7658912079310852403854033 5744184059483139302890525)
        ·
          refine ⟨2154069022306177238583947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5744184059483139302890525 2154069022306177238583947)
          ·
            refine ⟨3231103533459265857875921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154069022306177238583947 3231103533459265857875921)
            ·
              refine ⟨2423327650094449393406941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3231103533459265857875921 2423327650094449393406941)
              ·
                refine ⟨908747868785418522527603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2423327650094449393406941 908747868785418522527603)
                ·
                  refine ⟨1363121803178127783791405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908747868785418522527603 1363121803178127783791405)
                  ·
                    refine ⟨511170676191797918921777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1363121803178127783791405 511170676191797918921777)
                    ·
                      rfl

theorem cell22_1493252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_1493252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493252 prefixEnd_1493252 := by exact prefixLift 1493252
  have htrace : WordTrace (prefixWord ++ tailWord_1493252) baseStart_1493252 baseEnd_1493252 := by
    simpa [prefixWord, tailWord_1493252, baseEnd_1493252] using wordTrace_append hprefix tailTrace_1493252
  have hstable : (prefixWord ++ tailWord_1493252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493252).length < 2 ^ (prefixWord ++ tailWord_1493252).sum := by decide
  have hdescent : baseEnd_1493252 < baseStart_1493252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493259 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 8]
def baseStart_1493259 : Nat := 118140960795 + 1493259 * 2 ^ 59
def prefixEnd_1493259 : Nat := 4983230072969 + 3 ^ 40 * 1493259 * 2
def baseEnd_1493259 : Nat := 170391024144950744665585

theorem tailTrace_1493259 : CollatzResearch.WordTrace tailWord_1493259 prefixEnd_1493259 170391024144950744665585 := by
  unfold tailWord_1493259
  simp only [CollatzResearch.WordTrace]
  refine ⟨54463630097185146178466831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36309086731456764118977887 54463630097185146178466831)
  ·
    refine ⟨81695445145777719267700247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54463630097185146178466831 81695445145777719267700247)
    ·
      refine ⟨122543167718666578901550371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81695445145777719267700247 122543167718666578901550371)
      ·
        refine ⟨183814751577999868352325557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122543167718666578901550371 183814751577999868352325557)
        ·
          refine ⟨17232632960437487658030521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183814751577999868352325557 17232632960437487658030521)
          ·
            refine ⟨12924474720328115743522891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17232632960437487658030521 12924474720328115743522891)
            ·
              refine ⟨19386712080492173615284337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12924474720328115743522891 19386712080492173615284337)
              ·
                refine ⟨14540034060369130211463253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19386712080492173615284337 14540034060369130211463253)
                ·
                  refine ⟨170391024144950744665585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14540034060369130211463253 170391024144950744665585)
                  ·
                    rfl

theorem cell22_1493259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 8].length) (baseStart_1493259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493259 prefixEnd_1493259 := by exact prefixLift 1493259
  have htrace : WordTrace (prefixWord ++ tailWord_1493259) baseStart_1493259 baseEnd_1493259 := by
    simpa [prefixWord, tailWord_1493259, baseEnd_1493259] using wordTrace_append hprefix tailTrace_1493259
  have hstable : (prefixWord ++ tailWord_1493259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493259).length < 2 ^ (prefixWord ++ tailWord_1493259).sum := by decide
  have hdescent : baseEnd_1493259 < baseStart_1493259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493306 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_1493306 : Nat := 118140960795 + 1493306 * 2 ^ 59
def prefixEnd_1493306 : Nat := 4983230072969 + 3 ^ 40 * 1493306 * 2
def baseEnd_1493306 : Nat := 511189161495359778071611

theorem tailTrace_1493306 : CollatzResearch.WordTrace tailWord_1493306 prefixEnd_1493306 511189161495359778071611 := by
  unfold tailWord_1493306
  simp only [CollatzResearch.WordTrace]
  refine ⟨13616336082003718301356943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36310229552009915470285181 13616336082003718301356943)
  ·
    refine ⟨20424504123005577452035415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13616336082003718301356943 20424504123005577452035415)
    ·
      refine ⟨30636756184508366178053123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20424504123005577452035415 30636756184508366178053123)
      ·
        refine ⟨45955134276762549267079685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30636756184508366178053123 45955134276762549267079685)
        ·
          refine ⟨8616587676892977987577441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45955134276762549267079685 8616587676892977987577441)
          ·
            refine ⟨6462440757669733490683081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8616587676892977987577441 6462440757669733490683081)
            ·
              refine ⟨4846830568252300118012311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6462440757669733490683081 4846830568252300118012311)
              ·
                refine ⟨7270245852378450177018467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846830568252300118012311 7270245852378450177018467)
                ·
                  refine ⟨10905368778567675265527701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7270245852378450177018467 10905368778567675265527701)
                  ·
                    refine ⟨511189161495359778071611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10905368778567675265527701 511189161495359778071611)
                    ·
                      rfl

theorem cell22_1493306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_1493306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493306 prefixEnd_1493306 := by exact prefixLift 1493306
  have htrace : WordTrace (prefixWord ++ tailWord_1493306) baseStart_1493306 baseEnd_1493306 := by
    simpa [prefixWord, tailWord_1493306, baseEnd_1493306] using wordTrace_append hprefix tailTrace_1493306
  have hstable : (prefixWord ++ tailWord_1493306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493306).length < 2 ^ (prefixWord ++ tailWord_1493306).sum := by decide
  have hdescent : baseEnd_1493306 < baseStart_1493306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493310 : List Nat := [4, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_1493310 : Nat := 118140960795 + 1493310 * 2 ^ 59
def prefixEnd_1493310 : Nat := 4983230072969 + 3 ^ 40 * 1493310 * 2
def baseEnd_1493310 : Nat := 170396843592368366990533

theorem tailTrace_1493310 : CollatzResearch.WordTrace tailWord_1493310 prefixEnd_1493310 170396843592368366990533 := by
  unfold tailWord_1493310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6808186277500047736071673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36310326813333587925715589 6808186277500047736071673)
  ·
    refine ⟨5106139708125035802053755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6808186277500047736071673 5106139708125035802053755)
    ·
      refine ⟨7659209562187553703080633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5106139708125035802053755 7659209562187553703080633)
      ·
        refine ⟨5744407171640665277310475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7659209562187553703080633 5744407171640665277310475)
        ·
          refine ⟨8616610757460997915965713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744407171640665277310475 8616610757460997915965713)
          ·
            refine ⟨6462458068095748436974285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8616610757460997915965713 6462458068095748436974285)
            ·
              refine ⟨2423421775535905663865357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6462458068095748436974285 2423421775535905663865357)
              ·
                refine ⟨908783165825964623949509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2423421775535905663865357 908783165825964623949509)
                ·
                  refine ⟨170396843592368366990533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 908783165825964623949509 170396843592368366990533)
                  ·
                    rfl

theorem cell22_1493310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_1493310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493310 prefixEnd_1493310 := by exact prefixLift 1493310
  have htrace : WordTrace (prefixWord ++ tailWord_1493310) baseStart_1493310 baseEnd_1493310 := by
    simpa [prefixWord, tailWord_1493310, baseEnd_1493310] using wordTrace_append hprefix tailTrace_1493310
  have hstable : (prefixWord ++ tailWord_1493310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493310).length < 2 ^ (prefixWord ++ tailWord_1493310).sum := by decide
  have hdescent : baseEnd_1493310 < baseStart_1493310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493381 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_1493381 : Nat := 118140960795 + 1493381 * 2 ^ 59
def prefixEnd_1493381 : Nat := 4983230072969 + 3 ^ 40 * 1493381 * 2
def baseEnd_1493381 : Nat := 511214835528084582446381

theorem tailTrace_1493381 : CollatzResearch.WordTrace tailWord_1493381 prefixEnd_1493381 511214835528084582446381 := by
  unfold tailWord_1493381
  simp only [CollatzResearch.WordTrace]
  refine ⟨54468079802743161014407997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36312053201828774009605331 54468079802743161014407997)
  ·
    refine ⟨20425529926028685380402999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54468079802743161014407997 20425529926028685380402999)
    ·
      refine ⟨30638294889043028070604499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20425529926028685380402999 30638294889043028070604499)
      ·
        refine ⟨45957442333564542105906749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30638294889043028070604499 45957442333564542105906749)
        ·
          refine ⟨17234040875086703289715031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45957442333564542105906749 17234040875086703289715031)
          ·
            refine ⟨25851061312630054934572547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17234040875086703289715031 25851061312630054934572547)
            ·
              refine ⟨38776591968945082401858821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25851061312630054934572547 38776591968945082401858821)
              ·
                refine ⟨7270610994177202950348529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38776591968945082401858821 7270610994177202950348529)
                ·
                  refine ⟨5452958245632902212761397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270610994177202950348529 5452958245632902212761397)
                  ·
                    refine ⟨511214835528084582446381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5452958245632902212761397 511214835528084582446381)
                    ·
                      rfl

theorem cell22_1493381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_1493381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493381 prefixEnd_1493381 := by exact prefixLift 1493381
  have htrace : WordTrace (prefixWord ++ tailWord_1493381) baseStart_1493381 baseEnd_1493381 := by
    simpa [prefixWord, tailWord_1493381, baseEnd_1493381] using wordTrace_append hprefix tailTrace_1493381
  have hstable : (prefixWord ++ tailWord_1493381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493381).length < 2 ^ (prefixWord ++ tailWord_1493381).sum := by decide
  have hdescent : baseEnd_1493381 < baseStart_1493381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493383 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 5]
def baseStart_1493383 : Nat := 118140960795 + 1493383 * 2 ^ 59
def prefixEnd_1493383 : Nat := 4983230072969 + 3 ^ 40 * 1493383 * 2
def baseEnd_1493383 : Nat := 170405173389652414632125

theorem tailTrace_1493383 : CollatzResearch.WordTrace tailWord_1493383 prefixEnd_1493383 170405173389652414632125 := by
  unfold tailWord_1493383
  simp only [CollatzResearch.WordTrace]
  refine ⟨54468152748735915355980803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36312101832490610237320535 54468152748735915355980803)
  ·
    refine ⟨81702229123103873033971205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54468152748735915355980803 81702229123103873033971205)
    ·
      refine ⟨15319167960581976193869601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81702229123103873033971205 15319167960581976193869601)
      ·
        refine ⟨11489375970436482145402201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15319167960581976193869601 11489375970436482145402201)
        ·
          refine ⟨8617031977827361609051651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11489375970436482145402201 8617031977827361609051651)
          ·
            refine ⟨12925547966741042413577477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617031977827361609051651 12925547966741042413577477)
            ·
              refine ⟨2423540243763945452545777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12925547966741042413577477 2423540243763945452545777)
              ·
                refine ⟨1817655182822959089409333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423540243763945452545777 1817655182822959089409333)
                ·
                  refine ⟨170405173389652414632125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1817655182822959089409333 170405173389652414632125)
                  ·
                    rfl

theorem cell22_1493383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 5].length) (baseStart_1493383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493383 prefixEnd_1493383 := by exact prefixLift 1493383
  have htrace : WordTrace (prefixWord ++ tailWord_1493383) baseStart_1493383 baseEnd_1493383 := by
    simpa [prefixWord, tailWord_1493383, baseEnd_1493383] using wordTrace_append hprefix tailTrace_1493383
  have hstable : (prefixWord ++ tailWord_1493383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493383).length < 2 ^ (prefixWord ++ tailWord_1493383).sum := by decide
  have hdescent : baseEnd_1493383 < baseStart_1493383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493387 : List Nat := [1, 1, 1, 1, 4, 4, 4, 2, 1, 3]
def baseStart_1493387 : Nat := 118140960795 + 1493387 * 2 ^ 59
def prefixEnd_1493387 : Nat := 4983230072969 + 3 ^ 40 * 1493387 * 2
def baseEnd_1493387 : Nat := 511216889450702566796363

theorem tailTrace_1493387 : CollatzResearch.WordTrace tailWord_1493387 prefixEnd_1493387 511216889450702566796363 := by
  unfold tailWord_1493387
  simp only [CollatzResearch.WordTrace]
  refine ⟨54468298640721424039126415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36312199093814282692750943 54468298640721424039126415)
  ·
    refine ⟨81702447961082136058689623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54468298640721424039126415 81702447961082136058689623)
    ·
      refine ⟨122553671941623204088034435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81702447961082136058689623 122553671941623204088034435)
      ·
        refine ⟨183830507912434806132051653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122553671941623204088034435 183830507912434806132051653)
        ·
          refine ⟨34468220233581526149759685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183830507912434806132051653 34468220233581526149759685)
          ·
            refine ⟨6462791293796536153079941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34468220233581526149759685 6462791293796536153079941)
            ·
              refine ⟨1211773367586850528702489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6462791293796536153079941 1211773367586850528702489)
              ·
                refine ⟨908830025690137896526867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211773367586850528702489 908830025690137896526867)
                ·
                  refine ⟨1363245038535206844790301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908830025690137896526867 1363245038535206844790301)
                  ·
                    refine ⟨511216889450702566796363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1363245038535206844790301 511216889450702566796363)
                    ·
                      rfl

theorem cell22_1493387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 1, 3].length) (baseStart_1493387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493387 prefixEnd_1493387 := by exact prefixLift 1493387
  have htrace : WordTrace (prefixWord ++ tailWord_1493387) baseStart_1493387 baseEnd_1493387 := by
    simpa [prefixWord, tailWord_1493387, baseEnd_1493387] using wordTrace_append hprefix tailTrace_1493387
  have hstable : (prefixWord ++ tailWord_1493387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493387).length < 2 ^ (prefixWord ++ tailWord_1493387).sum := by decide
  have hdescent : baseEnd_1493387 < baseStart_1493387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493411 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 8]
def baseStart_1493411 : Nat := 118140960795 + 1493411 * 2 ^ 59
def prefixEnd_1493411 : Nat := 4983230072969 + 3 ^ 40 * 1493411 * 2
def baseEnd_1493411 : Nat := 170408368380391501398763

theorem tailTrace_1493411 : CollatzResearch.WordTrace tailWord_1493411 prefixEnd_1493411 170408368380391501398763 := by
  unfold tailWord_1493411
  simp only [CollatzResearch.WordTrace]
  refine ⟨54469173992634476138000087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36312782661756317425333391 54469173992634476138000087)
  ·
    refine ⟨81703760988951714207000131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54469173992634476138000087 81703760988951714207000131)
    ·
      refine ⟨122555641483427571310500197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81703760988951714207000131 122555641483427571310500197)
      ·
        refine ⟨22979182778142669620718787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122555641483427571310500197 22979182778142669620718787)
        ·
          refine ⟨34468774167214004431078181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22979182778142669620718787 34468774167214004431078181)
          ·
            refine ⟨6462895156352625830827159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34468774167214004431078181 6462895156352625830827159)
            ·
              refine ⟨9694342734528938746240739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6462895156352625830827159 9694342734528938746240739)
              ·
                refine ⟨14541514101793408119361109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9694342734528938746240739 14541514101793408119361109)
                ·
                  refine ⟨170408368380391501398763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14541514101793408119361109 170408368380391501398763)
                  ·
                    rfl

theorem cell22_1493411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 8].length) (baseStart_1493411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493411 prefixEnd_1493411 := by exact prefixLift 1493411
  have htrace : WordTrace (prefixWord ++ tailWord_1493411) baseStart_1493411 baseEnd_1493411 := by
    simpa [prefixWord, tailWord_1493411, baseEnd_1493411] using wordTrace_append hprefix tailTrace_1493411
  have hstable : (prefixWord ++ tailWord_1493411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493411).length < 2 ^ (prefixWord ++ tailWord_1493411).sum := by decide
  have hdescent : baseEnd_1493411 < baseStart_1493411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493413 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_1493413 : Nat := 118140960795 + 1493413 * 2 ^ 59
def prefixEnd_1493413 : Nat := 4983230072969 + 3 ^ 40 * 1493413 * 2
def baseEnd_1493413 : Nat := 511225789782047165646283

theorem tailTrace_1493413 : CollatzResearch.WordTrace tailWord_1493413 prefixEnd_1493413 511225789782047165646283 := by
  unfold tailWord_1493413
  simp only [CollatzResearch.WordTrace]
  refine ⟨54469246938627230479572893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36312831292418153653048595 54469246938627230479572893)
  ·
    refine ⟨20425967601985211429839835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54469246938627230479572893 20425967601985211429839835)
    ·
      refine ⟨30638951402977817144759753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20425967601985211429839835 30638951402977817144759753)
      ·
        refine ⟨22979213552233362858569815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30638951402977817144759753 22979213552233362858569815)
        ·
          refine ⟨34468820328350044287854723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22979213552233362858569815 34468820328350044287854723)
          ·
            refine ⟨51703230492525066431782085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34468820328350044287854723 51703230492525066431782085)
            ·
              refine ⟨9694355717348449955959141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51703230492525066431782085 9694355717348449955959141)
              ·
                refine ⟨1817691697002834366742339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9694355717348449955959141 1817691697002834366742339)
                ·
                  refine ⟨2726537545504251550113509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817691697002834366742339 2726537545504251550113509)
                  ·
                    refine ⟨511225789782047165646283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2726537545504251550113509 511225789782047165646283)
                    ·
                      rfl

theorem cell22_1493413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_1493413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493413 prefixEnd_1493413 := by exact prefixLift 1493413
  have htrace : WordTrace (prefixWord ++ tailWord_1493413) baseStart_1493413 baseEnd_1493413 := by
    simpa [prefixWord, tailWord_1493413, baseEnd_1493413] using wordTrace_append hprefix tailTrace_1493413
  have hstable : (prefixWord ++ tailWord_1493413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493413).length < 2 ^ (prefixWord ++ tailWord_1493413).sum := by decide
  have hdescent : baseEnd_1493413 < baseStart_1493413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493460 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1493460 : Nat := 118140960795 + 1493460 * 2 ^ 59
def prefixEnd_1493460 : Nat := 4983230072969 + 3 ^ 40 * 1493460 * 2
def baseEnd_1493460 : Nat := 511241878842554709721139

theorem tailTrace_1493460 : CollatzResearch.WordTrace tailWord_1493460 prefixEnd_1493460 511241878842554709721139 := by
  unfold tailWord_1493460
  simp only [CollatzResearch.WordTrace]
  refine ⟨27235480584728478753266917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36313974112971305004355889 27235480584728478753266917)
  ·
    refine ⟨5106652609636589766237547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27235480584728478753266917 5106652609636589766237547)
    ·
      refine ⟨7659978914454884649356321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5106652609636589766237547 7659978914454884649356321)
      ·
        refine ⟨5744984185841163487017241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7659978914454884649356321 5744984185841163487017241)
        ·
          refine ⟨4308738139380872615262931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5744984185841163487017241 4308738139380872615262931)
          ·
            refine ⟨6463107209071308922894397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308738139380872615262931 6463107209071308922894397)
            ·
              refine ⟨2423665203401740846085399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6463107209071308922894397 2423665203401740846085399)
              ·
                refine ⟨3635497805102611269128099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423665203401740846085399 3635497805102611269128099)
                ·
                  refine ⟨5453246707653916903692149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635497805102611269128099 5453246707653916903692149)
                  ·
                    refine ⟨511241878842554709721139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5453246707653916903692149 511241878842554709721139)
                    ·
                      rfl

theorem cell22_1493460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1493460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493460 prefixEnd_1493460 := by exact prefixLift 1493460
  have htrace : WordTrace (prefixWord ++ tailWord_1493460) baseStart_1493460 baseEnd_1493460 := by
    simpa [prefixWord, tailWord_1493460, baseEnd_1493460] using wordTrace_append hprefix tailTrace_1493460
  have hstable : (prefixWord ++ tailWord_1493460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493460).length < 2 ^ (prefixWord ++ tailWord_1493460).sum := by decide
  have hdescent : baseEnd_1493460 < baseStart_1493460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493490 : List Nat := [3, 2, 1, 4, 2, 2, 8]
def baseStart_1493490 : Nat := 118140960795 + 1493490 * 2 ^ 59
def prefixEnd_1493490 : Nat := 4983230072969 + 3 ^ 40 * 1493490 * 2
def baseEnd_1493490 : Nat := 18935264757616467832261

theorem tailTrace_1493490 : CollatzResearch.WordTrace tailWord_1493490 prefixEnd_1493490 18935264757616467832261 := by
  unfold tailWord_1493490
  simp only [CollatzResearch.WordTrace]
  refine ⟨13618013839837068157531481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36314703572898848420083949 13618013839837068157531481)
  ·
    refine ⟨10213510379877801118148611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13618013839837068157531481 10213510379877801118148611)
    ·
      refine ⟨15320265569816701677222917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213510379877801118148611 15320265569816701677222917)
      ·
        refine ⟨2872549794340631564479297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15320265569816701677222917 2872549794340631564479297)
        ·
          refine ⟨2154412345755473673359473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2872549794340631564479297 2154412345755473673359473)
          ·
            refine ⟨1615809259316605255019605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2154412345755473673359473 1615809259316605255019605)
            ·
              refine ⟨18935264757616467832261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1615809259316605255019605 18935264757616467832261)
              ·
                rfl

theorem cell22_1493490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 8].length) (baseStart_1493490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493490 prefixEnd_1493490 := by exact prefixLift 1493490
  have htrace : WordTrace (prefixWord ++ tailWord_1493490) baseStart_1493490 baseEnd_1493490 := by
    simpa [prefixWord, tailWord_1493490, baseEnd_1493490] using wordTrace_append hprefix tailTrace_1493490
  have hstable : (prefixWord ++ tailWord_1493490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493490).length < 2 ^ (prefixWord ++ tailWord_1493490).sum := by decide
  have hdescent : baseEnd_1493490 < baseStart_1493490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493511 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 2, 3]
def baseStart_1493511 : Nat := 118140960795 + 1493511 * 2 ^ 59
def prefixEnd_1493511 : Nat := 4983230072969 + 3 ^ 40 * 1493511 * 2
def baseEnd_1493511 : Nat := 511259337184807576695983

theorem tailTrace_1493511 : CollatzResearch.WordTrace tailWord_1493511 prefixEnd_1493511 511259337184807576695983 := by
  unfold tailWord_1493511
  simp only [CollatzResearch.WordTrace]
  refine ⟨54472821292272193216640387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36315214194848128811093591 54472821292272193216640387)
  ·
    refine ⟨81709231938408289824960581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54472821292272193216640387 81709231938408289824960581)
    ·
      refine ⟨15320480988451554342180109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81709231938408289824960581 15320480988451554342180109)
      ·
        refine ⟨5745180370669332878317541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15320480988451554342180109 5745180370669332878317541)
        ·
          refine ⟨1077221319500499914684539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5745180370669332878317541 1077221319500499914684539)
          ·
            refine ⟨1615831979250749872026809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077221319500499914684539 1615831979250749872026809)
            ·
              refine ⟨1211873984438062404020107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615831979250749872026809 1211873984438062404020107)
              ·
                refine ⟨1817810976657093606030161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211873984438062404020107 1817810976657093606030161)
                ·
                  refine ⟨1363358232492820204522621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1817810976657093606030161 1363358232492820204522621)
                  ·
                    refine ⟨511259337184807576695983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1363358232492820204522621 511259337184807576695983)
                    ·
                      rfl

theorem cell22_1493511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_1493511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493511 prefixEnd_1493511 := by exact prefixLift 1493511
  have htrace : WordTrace (prefixWord ++ tailWord_1493511) baseStart_1493511 baseEnd_1493511 := by
    simpa [prefixWord, tailWord_1493511, baseEnd_1493511] using wordTrace_append hprefix tailTrace_1493511
  have hstable : (prefixWord ++ tailWord_1493511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493511).length < 2 ^ (prefixWord ++ tailWord_1493511).sum := by decide
  have hdescent : baseEnd_1493511 < baseStart_1493511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493565 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1493565 : Nat := 118140960795 + 1493565 * 2 ^ 59
def prefixEnd_1493565 : Nat := 4983230072969 + 3 ^ 40 * 1493565 * 2
def baseEnd_1493565 : Nat := 511277822488369435845817

theorem tailTrace_1493565 : CollatzResearch.WordTrace tailWord_1493565 prefixEnd_1493565 511277822488369435845817 := by
  unfold tailWord_1493565
  simp only [CollatzResearch.WordTrace]
  refine ⟨54474790834076560439106149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36316527222717706959404099 54474790834076560439106149)
  ·
    refine ⟨10214023281389355082332403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54474790834076560439106149 10214023281389355082332403)
    ·
      refine ⟨15321034922084032623498605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10214023281389355082332403 15321034922084032623498605)
      ·
        refine ⟨5745388095781512233811977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15321034922084032623498605 5745388095781512233811977)
        ·
          refine ⟨4309041071836134175358983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5745388095781512233811977 4309041071836134175358983)
          ·
            refine ⟨6463561607754201263038475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309041071836134175358983 6463561607754201263038475)
            ·
              refine ⟨9695342411631301894557713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463561607754201263038475 9695342411631301894557713)
              ·
                refine ⟨7271506808723476420918285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9695342411631301894557713 7271506808723476420918285)
                ·
                  refine ⟨2726815053271303657844357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7271506808723476420918285 2726815053271303657844357)
                  ·
                    refine ⟨511277822488369435845817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2726815053271303657844357 511277822488369435845817)
                    ·
                      rfl

theorem cell22_1493565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1493565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493565 prefixEnd_1493565 := by exact prefixLift 1493565
  have htrace : WordTrace (prefixWord ++ tailWord_1493565) baseStart_1493565 baseEnd_1493565 := by
    simpa [prefixWord, tailWord_1493565, baseEnd_1493565] using wordTrace_append hprefix tailTrace_1493565
  have hstable : (prefixWord ++ tailWord_1493565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493565).length < 2 ^ (prefixWord ++ tailWord_1493565).sum := by decide
  have hdescent : baseEnd_1493565 < baseStart_1493565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493610 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1493610 : Nat := 118140960795 + 1493610 * 2 ^ 59
def prefixEnd_1493610 : Nat := 4983230072969 + 3 ^ 40 * 1493610 * 2
def baseEnd_1493610 : Nat := 511293226908004318470679

theorem tailTrace_1493610 : CollatzResearch.WordTrace tailWord_1493610 prefixEnd_1493610 511293226908004318470679 := by
  unfold tailWord_1493610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13619108029728383281123571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36317621412609022082996189 13619108029728383281123571)
  ·
    refine ⟨20428662044592574921685357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13619108029728383281123571 20428662044592574921685357)
    ·
      refine ⟨7660748266722215595632009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20428662044592574921685357 7660748266722215595632009)
      ·
        refine ⟨5745561200041661696724007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7660748266722215595632009 5745561200041661696724007)
        ·
          refine ⟨8618341800062492545086011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5745561200041661696724007 8618341800062492545086011)
          ·
            refine ⟨12927512700093738817629017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8618341800062492545086011 12927512700093738817629017)
            ·
              refine ⟨9695634525070304113221763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12927512700093738817629017 9695634525070304113221763)
              ·
                refine ⟨14543451787605456169832645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9695634525070304113221763 14543451787605456169832645)
                ·
                  refine ⟨2726897210176023031843621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14543451787605456169832645 2726897210176023031843621)
                  ·
                    refine ⟨511293226908004318470679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2726897210176023031843621 511293226908004318470679)
                    ·
                      rfl

theorem cell22_1493610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1493610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493610 prefixEnd_1493610 := by exact prefixLift 1493610
  have htrace : WordTrace (prefixWord ++ tailWord_1493610) baseStart_1493610 baseEnd_1493610 := by
    simpa [prefixWord, tailWord_1493610, baseEnd_1493610] using wordTrace_append hprefix tailTrace_1493610
  have hstable : (prefixWord ++ tailWord_1493610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493610).length < 2 ^ (prefixWord ++ tailWord_1493610).sum := by decide
  have hdescent : baseEnd_1493610 < baseStart_1493610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493612 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 2, 3]
def baseStart_1493612 : Nat := 118140960795 + 1493612 * 2 ^ 59
def prefixEnd_1493612 : Nat := 4983230072969 + 3 ^ 40 * 1493612 * 2
def baseEnd_1493612 : Nat := 511293911548876979920673

theorem tailTrace_1493612 : CollatzResearch.WordTrace tailWord_1493612 prefixEnd_1493612 511293911548876979920673 := by
  unfold tailWord_1493612
  simp only [CollatzResearch.WordTrace]
  refine ⟨27238252532453143733033545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36317670043270858310711393 27238252532453143733033545)
  ·
    refine ⟨20428689399339857799775159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27238252532453143733033545 20428689399339857799775159)
    ·
      refine ⟨30643034099009786699662739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20428689399339857799775159 30643034099009786699662739)
      ·
        refine ⟨45964551148514680049494109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30643034099009786699662739 45964551148514680049494109)
        ·
          refine ⟨17236706680693005018560291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45964551148514680049494109 17236706680693005018560291)
          ·
            refine ⟨25855060021039507527840437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17236706680693005018560291 25855060021039507527840437)
            ·
              refine ⟨2423911876972453830735041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25855060021039507527840437 2423911876972453830735041)
              ·
                refine ⟨1817933907729340373051281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423911876972453830735041 1817933907729340373051281)
                ·
                  refine ⟨1363450430797005279788461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1817933907729340373051281 1363450430797005279788461)
                  ·
                    refine ⟨511293911548876979920673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1363450430797005279788461 511293911548876979920673)
                    ·
                      rfl

theorem cell22_1493612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_1493612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493612 prefixEnd_1493612 := by exact prefixLift 1493612
  have htrace : WordTrace (prefixWord ++ tailWord_1493612) baseStart_1493612 baseEnd_1493612 := by
    simpa [prefixWord, tailWord_1493612, baseEnd_1493612] using wordTrace_append hprefix tailTrace_1493612
  have hstable : (prefixWord ++ tailWord_1493612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493612).length < 2 ^ (prefixWord ++ tailWord_1493612).sum := by decide
  have hdescent : baseEnd_1493612 < baseStart_1493612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493629 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_1493629 : Nat := 118140960795 + 1493629 * 2 ^ 59
def prefixEnd_1493629 : Nat := 4983230072969 + 3 ^ 40 * 1493629 * 2
def baseEnd_1493629 : Nat := 511299730996294602245621

theorem tailTrace_1493629 : CollatzResearch.WordTrace tailWord_1493629 prefixEnd_1493629 511299730996294602245621 := by
  unfold tailWord_1493629
  simp only [CollatzResearch.WordTrace]
  refine ⟨54477125105844699369435941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36318083403896466246290627 54477125105844699369435941)
  ·
    refine ⟨10214460957345881131769239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54477125105844699369435941 10214460957345881131769239)
    ·
      refine ⟨15321691436018821697653859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10214460957345881131769239 15321691436018821697653859)
      ·
        refine ⟨22982537154028232546480789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15321691436018821697653859 22982537154028232546480789)
        ·
          refine ⟨1077306429095073400616287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22982537154028232546480789 1077306429095073400616287)
          ·
            refine ⟨1615959643642610100924431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077306429095073400616287 1615959643642610100924431)
            ·
              refine ⟨2423939465463915151386647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615959643642610100924431 2423939465463915151386647)
              ·
                refine ⟨3635909198195872727079971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423939465463915151386647 3635909198195872727079971)
                ·
                  refine ⟨5453863797293809090619957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635909198195872727079971 5453863797293809090619957)
                  ·
                    refine ⟨511299730996294602245621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5453863797293809090619957 511299730996294602245621)
                    ·
                      rfl

theorem cell22_1493629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_1493629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493629 prefixEnd_1493629 := by exact prefixLift 1493629
  have htrace : WordTrace (prefixWord ++ tailWord_1493629) baseStart_1493629 baseEnd_1493629 := by
    simpa [prefixWord, tailWord_1493629, baseEnd_1493629] using wordTrace_append hprefix tailTrace_1493629
  have hstable : (prefixWord ++ tailWord_1493629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493629).length < 2 ^ (prefixWord ++ tailWord_1493629).sum := by decide
  have hdescent : baseEnd_1493629 < baseStart_1493629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493687 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 5]
def baseStart_1493687 : Nat := 118140960795 + 1493687 * 2 ^ 59
def prefixEnd_1493687 : Nat := 4983230072969 + 3 ^ 40 * 1493687 * 2
def baseEnd_1493687 : Nat := 170439861860533928098481

theorem tailTrace_1493687 : CollatzResearch.WordTrace tailWord_1493687 prefixEnd_1493687 170439861860533928098481 := by
  unfold tailWord_1493687
  simp only [CollatzResearch.WordTrace]
  refine ⟨54479240539634575275047315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36319493693089716850031543 54479240539634575275047315)
  ·
    refine ⟨81718860809451862912570973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54479240539634575275047315 81718860809451862912570973)
    ·
      refine ⟨30644572803544448592214115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81718860809451862912570973 30644572803544448592214115)
      ·
        refine ⟨45966859205316672888321173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30644572803544448592214115 45966859205316672888321173)
        ·
          refine ⟨2154696525249219041640055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45966859205316672888321173 2154696525249219041640055)
          ·
            refine ⟨3232044787873828562460083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154696525249219041640055 3232044787873828562460083)
            ·
              refine ⟨4848067181810742843690125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232044787873828562460083 4848067181810742843690125)
              ·
                refine ⟨1818025193179028566383797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4848067181810742843690125 1818025193179028566383797)
                ·
                  refine ⟨170439861860533928098481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1818025193179028566383797 170439861860533928098481)
                  ·
                    rfl

theorem cell22_1493687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 5].length) (baseStart_1493687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493687 prefixEnd_1493687 := by exact prefixLift 1493687
  have htrace : WordTrace (prefixWord ++ tailWord_1493687) baseStart_1493687 baseEnd_1493687 := by
    simpa [prefixWord, tailWord_1493687, baseEnd_1493687] using wordTrace_append hprefix tailTrace_1493687
  have hstable : (prefixWord ++ tailWord_1493687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493687).length < 2 ^ (prefixWord ++ tailWord_1493687).sum := by decide
  have hdescent : baseEnd_1493687 < baseStart_1493687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493745 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_1493745 : Nat := 118140960795 + 1493745 * 2 ^ 59
def prefixEnd_1493745 : Nat := 4983230072969 + 3 ^ 40 * 1493745 * 2
def baseEnd_1493745 : Nat := 511339440166908966345265

theorem tailTrace_1493745 : CollatzResearch.WordTrace tailWord_1493745 prefixEnd_1493745 511339440166908966345265 := by
  unfold tailWord_1493745
  simp only [CollatzResearch.WordTrace]
  refine ⟨54481355973424451180658689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36320903982282967453772459 54481355973424451180658689)
  ·
    refine ⟨40861016980068338385494017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54481355973424451180658689 40861016980068338385494017)
    ·
      refine ⟨30645762735051253789120513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40861016980068338385494017 30645762735051253789120513)
      ·
        refine ⟨22984322051288440341840385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30645762735051253789120513 22984322051288440341840385)
        ·
          refine ⟨17238241538466330256380289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22984322051288440341840385 17238241538466330256380289)
          ·
            refine ⟨12928681153849747692285217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17238241538466330256380289 12928681153849747692285217)
            ·
              refine ⟨9696510865387310769213913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12928681153849747692285217 9696510865387310769213913)
              ·
                refine ⟨7272383149040483076910435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9696510865387310769213913 7272383149040483076910435)
                ·
                  refine ⟨10908574723560724615365653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7272383149040483076910435 10908574723560724615365653)
                  ·
                    refine ⟨511339440166908966345265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10908574723560724615365653 511339440166908966345265)
                    ·
                      rfl

theorem cell22_1493745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_1493745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493745 prefixEnd_1493745 := by exact prefixLift 1493745
  have htrace : WordTrace (prefixWord ++ tailWord_1493745) baseStart_1493745 baseEnd_1493745 := by
    simpa [prefixWord, tailWord_1493745, baseEnd_1493745] using wordTrace_append hprefix tailTrace_1493745
  have hstable : (prefixWord ++ tailWord_1493745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493745).length < 2 ^ (prefixWord ++ tailWord_1493745).sum := by decide
  have hdescent : baseEnd_1493745 < baseStart_1493745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493899 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 2, 3]
def baseStart_1493899 : Nat := 118140960795 + 1493899 * 2 ^ 59
def prefixEnd_1493899 : Nat := 4983230072969 + 3 ^ 40 * 1493899 * 2
def baseEnd_1493899 : Nat := 511392157514103897994793

theorem tailTrace_1493899 : CollatzResearch.WordTrace tailWord_1493899 prefixEnd_1493899 511392157514103897994793 := by
  unfold tailWord_1493899
  simp only [CollatzResearch.WordTrace]
  refine ⟨54486972814866535481764751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36324648543244356987843167 54486972814866535481764751)
  ·
    refine ⟨81730459222299803222647127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54486972814866535481764751 81730459222299803222647127)
    ·
      refine ⟨122595688833449704833970691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81730459222299803222647127 122595688833449704833970691)
      ·
        refine ⟨183893533250174557250956037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122595688833449704833970691 183893533250174557250956037)
        ·
          refine ⟨34480037484407729484554257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183893533250174557250956037 34480037484407729484554257)
          ·
            refine ⟨25860028113305797113415693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34480037484407729484554257 25860028113305797113415693)
            ·
              refine ⟨9697510542489673917530885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25860028113305797113415693 9697510542489673917530885)
              ·
                refine ⟨1818283226716813859537041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9697510542489673917530885 1818283226716813859537041)
                ·
                  refine ⟨1363712420037610394652781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1818283226716813859537041 1363712420037610394652781)
                  ·
                    refine ⟨511392157514103897994793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1363712420037610394652781 511392157514103897994793)
                    ·
                      rfl

theorem cell22_1493899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 3].length) (baseStart_1493899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493899 prefixEnd_1493899 := by exact prefixLift 1493899
  have htrace : WordTrace (prefixWord ++ tailWord_1493899) baseStart_1493899 baseEnd_1493899 := by
    simpa [prefixWord, tailWord_1493899, baseEnd_1493899] using wordTrace_append hprefix tailTrace_1493899
  have hstable : (prefixWord ++ tailWord_1493899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493899).length < 2 ^ (prefixWord ++ tailWord_1493899).sum := by decide
  have hdescent : baseEnd_1493899 < baseStart_1493899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493916 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1493916 : Nat := 118140960795 + 1493916 * 2 ^ 59
def prefixEnd_1493916 : Nat := 4983230072969 + 3 ^ 40 * 1493916 * 2
def baseEnd_1493916 : Nat := 511397976961521520319741

theorem tailTrace_1493916 : CollatzResearch.WordTrace tailWord_1493916 prefixEnd_1493916 511397976961521520319741 := by
  unfold tailWord_1493916
  simp only [CollatzResearch.WordTrace]
  refine ⟨27243796427902473692566801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36325061903869964923422401 27243796427902473692566801)
  ·
    refine ⟨20432847320926855269425101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27243796427902473692566801 20432847320926855269425101)
    ·
      refine ⟨7662317745347570726034413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20432847320926855269425101 7662317745347570726034413)
      ·
        refine ⟨2873369154505339022262905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7662317745347570726034413 2873369154505339022262905)
        ·
          refine ⟨2155026865879004266697179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2873369154505339022262905 2155026865879004266697179)
          ·
            refine ⟨3232540298818506400045769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155026865879004266697179 3232540298818506400045769)
            ·
              refine ⟨2424405224113879800034327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232540298818506400045769 2424405224113879800034327)
              ·
                refine ⟨3636607836170819700051491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424405224113879800034327 3636607836170819700051491)
                ·
                  refine ⟨5454911754256229550077237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636607836170819700051491 5454911754256229550077237)
                  ·
                    refine ⟨511397976961521520319741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5454911754256229550077237 511397976961521520319741)
                    ·
                      rfl

theorem cell22_1493916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1493916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1493916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1493916 prefixEnd_1493916 := by exact prefixLift 1493916
  have htrace : WordTrace (prefixWord ++ tailWord_1493916) baseStart_1493916 baseEnd_1493916 := by
    simpa [prefixWord, tailWord_1493916, baseEnd_1493916] using wordTrace_append hprefix tailTrace_1493916
  have hstable : (prefixWord ++ tailWord_1493916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493916).length < 2 ^ (prefixWord ++ tailWord_1493916).sum := by decide
  have hdescent : baseEnd_1493916 < baseStart_1493916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494055 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1494055 : Nat := 118140960795 + 1494055 * 2 ^ 59
def prefixEnd_1494055 : Nat := 4983230072969 + 3 ^ 40 * 1494055 * 2
def baseEnd_1494055 : Nat := 511445559502171491094315

theorem tailTrace_1494055 : CollatzResearch.WordTrace tailWord_1494055 prefixEnd_1494055 511445559502171491094315 := by
  unfold tailWord_1494055
  simp only [CollatzResearch.WordTrace]
  refine ⟨54492662602301374124443619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36328441734867582749629079 54492662602301374124443619)
  ·
    refine ⟨81738993903452061186665429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54492662602301374124443619 81738993903452061186665429)
    ·
      refine ⟨1915757669612157684062471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 81738993903452061186665429 1915757669612157684062471)
      ·
        refine ⟨2873636504418236526093707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915757669612157684062471 2873636504418236526093707)
        ·
          refine ⟨4310454756627354789140561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873636504418236526093707 4310454756627354789140561)
          ·
            refine ⟨3232841067470516091855421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4310454756627354789140561 3232841067470516091855421)
            ·
              refine ⟨1212315400301443534445783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3232841067470516091855421 1212315400301443534445783)
              ·
                refine ⟨1818473100452165301668675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212315400301443534445783 1818473100452165301668675)
                ·
                  refine ⟨2727709650678247952503013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818473100452165301668675 2727709650678247952503013)
                  ·
                    refine ⟨511445559502171491094315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2727709650678247952503013 511445559502171491094315)
                    ·
                      rfl

theorem cell22_1494055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1494055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494055 prefixEnd_1494055 := by exact prefixLift 1494055
  have htrace : WordTrace (prefixWord ++ tailWord_1494055) baseStart_1494055 baseEnd_1494055 := by
    simpa [prefixWord, tailWord_1494055, baseEnd_1494055] using wordTrace_append hprefix tailTrace_1494055
  have hstable : (prefixWord ++ tailWord_1494055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494055).length < 2 ^ (prefixWord ++ tailWord_1494055).sum := by decide
  have hdescent : baseEnd_1494055 < baseStart_1494055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494070 : List Nat := [5, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_1494070 : Nat := 118140960795 + 1494070 * 2 ^ 59
def prefixEnd_1494070 : Nat := 4983230072969 + 3 ^ 40 * 1494070 * 2
def baseEnd_1494070 : Nat := 170483564769572150656423

theorem tailTrace_1494070 : CollatzResearch.WordTrace tailWord_1494070 prefixEnd_1494070 170483564769572150656423 := by
  unfold tailWord_1494070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3405825606077939480389979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36328806464831354457493109 3405825606077939480389979)
  ·
    refine ⟨5108738409116909220584969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3405825606077939480389979 5108738409116909220584969)
    ·
      refine ⟨3831553806837681915438727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5108738409116909220584969 3831553806837681915438727)
      ·
        refine ⟨5747330710256522873158091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3831553806837681915438727 5747330710256522873158091)
        ·
          refine ⟨8620996065384784309737137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747330710256522873158091 8620996065384784309737137)
          ·
            refine ⟨6465747049038588232302853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8620996065384784309737137 6465747049038588232302853)
            ·
              refine ⟨1212327571694735293556785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6465747049038588232302853 1212327571694735293556785)
              ·
                refine ⟨909245678771051470167589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212327571694735293556785 909245678771051470167589)
                ·
                  refine ⟨170483564769572150656423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909245678771051470167589 170483564769572150656423)
                  ·
                    rfl

theorem cell22_1494070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1494070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494070 prefixEnd_1494070 := by exact prefixLift 1494070
  have htrace : WordTrace (prefixWord ++ tailWord_1494070) baseStart_1494070 baseEnd_1494070 := by
    simpa [prefixWord, tailWord_1494070, baseEnd_1494070] using wordTrace_append hprefix tailTrace_1494070
  have hstable : (prefixWord ++ tailWord_1494070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494070).length < 2 ^ (prefixWord ++ tailWord_1494070).sum := by decide
  have hdescent : baseEnd_1494070 < baseStart_1494070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494094 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1494094 : Nat := 118140960795 + 1494094 * 2 ^ 59
def prefixEnd_1494094 : Nat := 4983230072969 + 3 ^ 40 * 1494094 * 2
def baseEnd_1494094 : Nat := 511458909999188389369195

theorem tailTrace_1494094 : CollatzResearch.WordTrace tailWord_1494094 prefixEnd_1494094 511458909999188389369195 := by
  unfold tailWord_1494094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811760631145010473139167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36329390032773389190075557 6811760631145010473139167)
  ·
    refine ⟨10217640946717515709708751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6811760631145010473139167 10217640946717515709708751)
    ·
      refine ⟨15326461420076273564563127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10217640946717515709708751 15326461420076273564563127)
      ·
        refine ⟨22989692130114410346844691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15326461420076273564563127 22989692130114410346844691)
        ·
          refine ⟨34484538195171615520267037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22989692130114410346844691 34484538195171615520267037)
          ·
            refine ⟨12931701823189355820100139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34484538195171615520267037 12931701823189355820100139)
            ·
              refine ⟨19397552734784033730150209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12931701823189355820100139 19397552734784033730150209)
              ·
                refine ⟨14548164551088025297612657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19397552734784033730150209 14548164551088025297612657)
                ·
                  refine ⟨10911123413316018973209493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14548164551088025297612657 10911123413316018973209493)
                  ·
                    refine ⟨511458909999188389369195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10911123413316018973209493 511458909999188389369195)
                    ·
                      rfl

theorem cell22_1494094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1494094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494094 prefixEnd_1494094 := by exact prefixLift 1494094
  have htrace : WordTrace (prefixWord ++ tailWord_1494094) baseStart_1494094 baseEnd_1494094 := by
    simpa [prefixWord, tailWord_1494094, baseEnd_1494094] using wordTrace_append hprefix tailTrace_1494094
  have hstable : (prefixWord ++ tailWord_1494094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494094).length < 2 ^ (prefixWord ++ tailWord_1494094).sum := by decide
  have hdescent : baseEnd_1494094 < baseStart_1494094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494113 : List Nat := [1, 2, 3, 1, 1, 2, 3, 5, 1, 3]
def baseStart_1494113 : Nat := 118140960795 + 1494113 * 2 ^ 59
def prefixEnd_1494113 : Nat := 4983230072969 + 3 ^ 40 * 1494113 * 2
def baseEnd_1494113 : Nat := 511465414087478673144137

theorem tailTrace_1494113 : CollatzResearch.WordTrace tailWord_1494113 prefixEnd_1494113 511465414087478673144137 := by
  unfold tailWord_1494113
  simp only [CollatzResearch.WordTrace]
  refine ⟨54494778036091250030054993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36329852024060833353369995 54494778036091250030054993)
  ·
    refine ⟨40871083527068437522541245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54494778036091250030054993 40871083527068437522541245)
    ·
      refine ⟨15326656322650664070952967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40871083527068437522541245 15326656322650664070952967)
      ·
        refine ⟨22989984483975996106429451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15326656322650664070952967 22989984483975996106429451)
        ·
          refine ⟨34484976725963994159644177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22989984483975996106429451 34484976725963994159644177)
          ·
            refine ⟨25863732544472995619733133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34484976725963994159644177 25863732544472995619733133)
            ·
              refine ⟨9698899704177373357399925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25863732544472995619733133 9698899704177373357399925)
              ·
                refine ⟨909271847266628752256243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9698899704177373357399925 909271847266628752256243)
                ·
                  refine ⟨1363907770899943128384365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909271847266628752256243 1363907770899943128384365)
                  ·
                    refine ⟨511465414087478673144137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1363907770899943128384365 511465414087478673144137)
                    ·
                      rfl

theorem cell22_1494113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_1494113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494113 prefixEnd_1494113 := by exact prefixLift 1494113
  have htrace : WordTrace (prefixWord ++ tailWord_1494113) baseStart_1494113 baseEnd_1494113 := by
    simpa [prefixWord, tailWord_1494113, baseEnd_1494113] using wordTrace_append hprefix tailTrace_1494113
  have hstable : (prefixWord ++ tailWord_1494113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494113).length < 2 ^ (prefixWord ++ tailWord_1494113).sum := by decide
  have hdescent : baseEnd_1494113 < baseStart_1494113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494124 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_1494124 : Nat := 118140960795 + 1494124 * 2 ^ 59
def prefixEnd_1494124 : Nat := 4983230072969 + 3 ^ 40 * 1494124 * 2
def baseEnd_1494124 : Nat := 511469179612278311119103

theorem tailTrace_1494124 : CollatzResearch.WordTrace tailWord_1494124 prefixEnd_1494124 511469179612278311119103 := by
  unfold tailWord_1494124
  simp only [CollatzResearch.WordTrace]
  refine ⟨27247589619525699454352713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36330119492700932605803617 27247589619525699454352713)
  ·
    refine ⟨20435692214644274590764535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27247589619525699454352713 20435692214644274590764535)
    ·
      refine ⟨30653538321966411886146803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20435692214644274590764535 30653538321966411886146803)
      ·
        refine ⟨45980307482949617829220205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30653538321966411886146803 45980307482949617829220205)
        ·
          refine ⟨17242615306106106685957577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45980307482949617829220205 17242615306106106685957577)
          ·
            refine ⟨12931961479579580014468183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17242615306106106685957577 12931961479579580014468183)
            ·
              refine ⟨19397942219369370021702275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12931961479579580014468183 19397942219369370021702275)
              ·
                refine ⟨29096913329054055032553413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19397942219369370021702275 29096913329054055032553413)
                ·
                  refine ⟨5455671249197635318603765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29096913329054055032553413 5455671249197635318603765)
                  ·
                    refine ⟨511469179612278311119103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5455671249197635318603765 511469179612278311119103)
                    ·
                      rfl

theorem cell22_1494124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_1494124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494124 prefixEnd_1494124 := by exact prefixLift 1494124
  have htrace : WordTrace (prefixWord ++ tailWord_1494124) baseStart_1494124 baseEnd_1494124 := by
    simpa [prefixWord, tailWord_1494124, baseEnd_1494124] using wordTrace_append hprefix tailTrace_1494124
  have hstable : (prefixWord ++ tailWord_1494124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494124).length < 2 ^ (prefixWord ++ tailWord_1494124).sum := by decide
  have hdescent : baseEnd_1494124 < baseStart_1494124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494126 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_1494126 : Nat := 118140960795 + 1494126 * 2 ^ 59
def prefixEnd_1494126 : Nat := 4983230072969 + 3 ^ 40 * 1494126 * 2
def baseEnd_1494126 : Nat := 170489954751050324189699

theorem tailTrace_1494126 : CollatzResearch.WordTrace tailWord_1494126 prefixEnd_1494126 170489954751050324189699 := by
  unfold tailWord_1494126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811906523130519156284779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36330168123362768833518821 6811906523130519156284779)
  ·
    refine ⟨10217859784695778734427169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6811906523130519156284779 10217859784695778734427169)
    ·
      refine ⟨7663394838521834050820377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10217859784695778734427169 7663394838521834050820377)
      ·
        refine ⟨5747546128891375538115283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7663394838521834050820377 5747546128891375538115283)
        ·
          refine ⟨8621319193337063307172925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747546128891375538115283 8621319193337063307172925)
          ·
            refine ⟨3232994697501398740189847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8621319193337063307172925 3232994697501398740189847)
            ·
              refine ⟨4849492046252098110284771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232994697501398740189847 4849492046252098110284771)
              ·
                refine ⟨7274238069378147165427157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4849492046252098110284771 7274238069378147165427157)
                ·
                  refine ⟨170489954751050324189699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7274238069378147165427157 170489954751050324189699)
                  ·
                    rfl

theorem cell22_1494126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_1494126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494126 prefixEnd_1494126 := by exact prefixLift 1494126
  have htrace : WordTrace (prefixWord ++ tailWord_1494126) baseStart_1494126 baseEnd_1494126 := by
    simpa [prefixWord, tailWord_1494126, baseEnd_1494126] using wordTrace_append hprefix tailTrace_1494126
  have hstable : (prefixWord ++ tailWord_1494126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494126).length < 2 ^ (prefixWord ++ tailWord_1494126).sum := by decide
  have hdescent : baseEnd_1494126 < baseStart_1494126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494139 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 5, 4]
def baseStart_1494139 : Nat := 118140960795 + 1494139 * 2 ^ 59
def prefixEnd_1494139 : Nat := 4983230072969 + 3 ^ 40 * 1494139 * 2
def baseEnd_1494139 : Nat := 511474314418823271994057

theorem tailTrace_1494139 : CollatzResearch.WordTrace tailWord_1494139 prefixEnd_1494139 511474314418823271994057 := by
  unfold tailWord_1494139
  simp only [CollatzResearch.WordTrace]
  refine ⟨54495726333997056470501471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36330484222664704313667647 54495726333997056470501471)
  ·
    refine ⟨81743589500995584705752207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54495726333997056470501471 81743589500995584705752207)
    ·
      refine ⟨122615384251493377058628311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81743589500995584705752207 122615384251493377058628311)
      ·
        refine ⟨183923076377240065587942467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122615384251493377058628311 183923076377240065587942467)
        ·
          refine ⟨275884614565860098381913701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183923076377240065587942467 275884614565860098381913701)
          ·
            refine ⟨51728365231098768446608819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275884614565860098381913701 51728365231098768446608819)
            ·
              refine ⟨77592547846648152669913229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51728365231098768446608819 77592547846648152669913229)
              ·
                refine ⟨29097205442493057251217461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77592547846648152669913229 29097205442493057251217461)
                ·
                  refine ⟨2727863010233724117301637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29097205442493057251217461 2727863010233724117301637)
                  ·
                    refine ⟨511474314418823271994057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2727863010233724117301637 511474314418823271994057)
                    ·
                      rfl

theorem cell22_1494139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 4].length) (baseStart_1494139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494139 prefixEnd_1494139 := by exact prefixLift 1494139
  have htrace : WordTrace (prefixWord ++ tailWord_1494139) baseStart_1494139 baseEnd_1494139 := by
    simpa [prefixWord, tailWord_1494139, baseEnd_1494139] using wordTrace_append hprefix tailTrace_1494139
  have hstable : (prefixWord ++ tailWord_1494139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494139).length < 2 ^ (prefixWord ++ tailWord_1494139).sum := by decide
  have hdescent : baseEnd_1494139 < baseStart_1494139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494218 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_1494218 : Nat := 118140960795 + 1494218 * 2 ^ 59
def prefixEnd_1494218 : Nat := 4983230072969 + 3 ^ 40 * 1494218 * 2
def baseEnd_1494218 : Nat := 511501357733293399268815

theorem tailTrace_1494218 : CollatzResearch.WordTrace tailWord_1494218 prefixEnd_1494218 511501357733293399268815 := by
  unfold tailWord_1494218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13624651925177713240656827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36332405133807235308418205 13624651925177713240656827)
  ·
    refine ⟨20436977887766569860985241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13624651925177713240656827 20436977887766569860985241)
    ·
      refine ⟨15327733415824927395738931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20436977887766569860985241 15327733415824927395738931)
      ·
        refine ⟨22991600123737391093608397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15327733415824927395738931 22991600123737391093608397)
        ·
          refine ⟨8621850046401521660103149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22991600123737391093608397 8621850046401521660103149)
          ·
            refine ⟨3233193767400570622538681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8621850046401521660103149 3233193767400570622538681)
            ·
              refine ⟨2424895325550427966904011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3233193767400570622538681 2424895325550427966904011)
              ·
                refine ⟨3637342988325641950356017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424895325550427966904011 3637342988325641950356017)
                ·
                  refine ⟨2728007241244231462767013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3637342988325641950356017 2728007241244231462767013)
                  ·
                    refine ⟨511501357733293399268815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2728007241244231462767013 511501357733293399268815)
                    ·
                      rfl

theorem cell22_1494218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_1494218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494218 prefixEnd_1494218 := by exact prefixLift 1494218
  have htrace : WordTrace (prefixWord ++ tailWord_1494218) baseStart_1494218 baseEnd_1494218 := by
    simpa [prefixWord, tailWord_1494218, baseEnd_1494218] using wordTrace_append hprefix tailTrace_1494218
  have hstable : (prefixWord ++ tailWord_1494218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494218).length < 2 ^ (prefixWord ++ tailWord_1494218).sum := by decide
  have hdescent : baseEnd_1494218 < baseStart_1494218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494237 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1494237 : Nat := 118140960795 + 1494237 * 2 ^ 59
def prefixEnd_1494237 : Nat := 4983230072969 + 3 ^ 40 * 1494237 * 2
def baseEnd_1494237 : Nat := 511507861821583683043757

theorem tailTrace_1494237 : CollatzResearch.WordTrace tailWord_1494237 prefixEnd_1494237 511507861821583683043757 := by
  unfold tailWord_1494237
  simp only [CollatzResearch.WordTrace]
  refine ⟨54499300687642019207568965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36332867125094679471712643 54499300687642019207568965)
  ·
    refine ⟨10218618878932878601419181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54499300687642019207568965 10218618878932878601419181)
    ·
      refine ⟨3831982079599829475532193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10218618878932878601419181 3831982079599829475532193)
      ·
        refine ⟨2873986559699872106649145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3831982079599829475532193 2873986559699872106649145)
        ·
          refine ⟨2155489919774904079986859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2873986559699872106649145 2155489919774904079986859)
          ·
            refine ⟨3233234879662356119980289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155489919774904079986859 3233234879662356119980289)
            ·
              refine ⟨2424926159746767089985217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3233234879662356119980289 2424926159746767089985217)
              ·
                refine ⟨1818694619810075317488913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2424926159746767089985217 1818694619810075317488913)
                ·
                  refine ⟨1364020964857556488116685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1818694619810075317488913 1364020964857556488116685)
                  ·
                    refine ⟨511507861821583683043757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364020964857556488116685 511507861821583683043757)
                    ·
                      rfl

theorem cell22_1494237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1494237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494237 prefixEnd_1494237 := by exact prefixLift 1494237
  have htrace : WordTrace (prefixWord ++ tailWord_1494237) baseStart_1494237 baseEnd_1494237 := by
    simpa [prefixWord, tailWord_1494237, baseEnd_1494237] using wordTrace_append hprefix tailTrace_1494237
  have hstable : (prefixWord ++ tailWord_1494237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494237).length < 2 ^ (prefixWord ++ tailWord_1494237).sum := by decide
  have hdescent : baseEnd_1494237 < baseStart_1494237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494248 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1494248 : Nat := 118140960795 + 1494248 * 2 ^ 59
def prefixEnd_1494248 : Nat := 4983230072969 + 3 ^ 40 * 1494248 * 2
def baseEnd_1494248 : Nat := 511511627346383321018723

theorem tailTrace_1494248 : CollatzResearch.WordTrace tailWord_1494248 prefixEnd_1494248 511511627346383321018723 := by
  unfold tailWord_1494248
  simp only [CollatzResearch.WordTrace]
  refine ⟨27249850945301084043109699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36333134593734778724146265 27249850945301084043109699)
  ·
    refine ⟨40874776417951626064664549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27249850945301084043109699 40874776417951626064664549)
    ·
      refine ⟨7664020578365929887124603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40874776417951626064664549 7664020578365929887124603)
      ·
        refine ⟨11496030867548894830686905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7664020578365929887124603 11496030867548894830686905)
        ·
          refine ⟨8622023150661671123015179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11496030867548894830686905 8622023150661671123015179)
          ·
            refine ⟨12933034725992506684522769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8622023150661671123015179 12933034725992506684522769)
            ·
              refine ⟨9699776044494380013392077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12933034725992506684522769 9699776044494380013392077)
              ·
                refine ⟨3637416016685392505022029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9699776044494380013392077 3637416016685392505022029)
                ·
                  refine ⟨1364031006257022189383261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3637416016685392505022029 1364031006257022189383261)
                  ·
                    refine ⟨511511627346383321018723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364031006257022189383261 511511627346383321018723)
                    ·
                      rfl

theorem cell22_1494248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1494248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494248 prefixEnd_1494248 := by exact prefixLift 1494248
  have htrace : WordTrace (prefixWord ++ tailWord_1494248) baseStart_1494248 baseEnd_1494248 := by
    simpa [prefixWord, tailWord_1494248, baseEnd_1494248] using wordTrace_append hprefix tailTrace_1494248
  have hstable : (prefixWord ++ tailWord_1494248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494248).length < 2 ^ (prefixWord ++ tailWord_1494248).sum := by decide
  have hdescent : baseEnd_1494248 < baseStart_1494248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494325 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1494325 : Nat := 118140960795 + 1494325 * 2 ^ 59
def prefixEnd_1494325 : Nat := 4983230072969 + 3 ^ 40 * 1494325 * 2
def baseEnd_1494325 : Nat := 511537986019980786843487

theorem tailTrace_1494325 : CollatzResearch.WordTrace tailWord_1494325 prefixEnd_1494325 511537986019980786843487 := by
  unfold tailWord_1494325
  simp only [CollatzResearch.WordTrace]
  refine ⟨54502510311323210236772429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36335006874215473491181619 54502510311323210236772429)
  ·
    refine ⟨20438441366746203838789661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54502510311323210236772429 20438441366746203838789661)
    ·
      refine ⟨7664415512529826439546123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20438441366746203838789661 7664415512529826439546123)
      ·
        refine ⟨11496623268794739659319185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7664415512529826439546123 11496623268794739659319185)
        ·
          refine ⟨8622467451596054744489389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11496623268794739659319185 8622467451596054744489389)
          ·
            refine ⟨3233425294348520529183521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8622467451596054744489389 3233425294348520529183521)
            ·
              refine ⟨2425068970761390396887641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3233425294348520529183521 2425068970761390396887641)
              ·
                refine ⟨1818801728071042797665731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2425068970761390396887641 1818801728071042797665731)
                ·
                  refine ⟨2728202592106564196498597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818801728071042797665731 2728202592106564196498597)
                  ·
                    refine ⟨511537986019980786843487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2728202592106564196498597 511537986019980786843487)
                    ·
                      rfl

theorem cell22_1494325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1494325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494325 prefixEnd_1494325 := by exact prefixLift 1494325
  have htrace : WordTrace (prefixWord ++ tailWord_1494325) baseStart_1494325 baseEnd_1494325 := by
    simpa [prefixWord, tailWord_1494325, baseEnd_1494325] using wordTrace_append hprefix tailTrace_1494325
  have hstable : (prefixWord ++ tailWord_1494325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494325).length < 2 ^ (prefixWord ++ tailWord_1494325).sum := by decide
  have hdescent : baseEnd_1494325 < baseStart_1494325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494336 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_1494336 : Nat := 118140960795 + 1494336 * 2 ^ 59
def prefixEnd_1494336 : Nat := 4983230072969 + 3 ^ 40 * 1494336 * 2
def baseEnd_1494336 : Nat := 511541751544780424818453

theorem tailTrace_1494336 : CollatzResearch.WordTrace tailWord_1494336 prefixEnd_1494336 511541751544780424818453 := by
  unfold tailWord_1494336
  simp only [CollatzResearch.WordTrace]
  refine ⟨27251455757141679557711431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36335274342855572743615241 27251455757141679557711431)
  ·
    refine ⟨40877183635712519336567147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27251455757141679557711431 40877183635712519336567147)
    ·
      refine ⟨61315775453568779004850721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40877183635712519336567147 61315775453568779004850721)
      ·
        refine ⟨45986831590176584253638041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61315775453568779004850721 45986831590176584253638041)
        ·
          refine ⟨34490123692632438190228531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45986831590176584253638041 34490123692632438190228531)
          ·
            refine ⟨51735185538948657285342797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34490123692632438190228531 51735185538948657285342797)
            ·
              refine ⟨19400694577105746482003549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51735185538948657285342797 19400694577105746482003549)
              ·
                refine ⟨7275260466414654930751331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19400694577105746482003549 7275260466414654930751331)
                ·
                  refine ⟨10912890699621982396126997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7275260466414654930751331 10912890699621982396126997)
                  ·
                    refine ⟨511541751544780424818453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10912890699621982396126997 511541751544780424818453)
                    ·
                      rfl

theorem cell22_1494336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_1494336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494336 prefixEnd_1494336 := by exact prefixLift 1494336
  have htrace : WordTrace (prefixWord ++ tailWord_1494336) baseStart_1494336 baseEnd_1494336 := by
    simpa [prefixWord, tailWord_1494336, baseEnd_1494336] using wordTrace_append hprefix tailTrace_1494336
  have hstable : (prefixWord ++ tailWord_1494336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494336).length < 2 ^ (prefixWord ++ tailWord_1494336).sum := by decide
  have hdescent : baseEnd_1494336 < baseStart_1494336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494353 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_1494353 : Nat := 118140960795 + 1494353 * 2 ^ 59
def prefixEnd_1494353 : Nat := 4983230072969 + 3 ^ 40 * 1494353 * 2
def baseEnd_1494353 : Nat := 511547570992198047143401

theorem tailTrace_1494353 : CollatzResearch.WordTrace tailWord_1494353 prefixEnd_1494353 511547570992198047143401 := by
  unfold tailWord_1494353
  simp only [CollatzResearch.WordTrace]
  refine ⟨54503531555221771018791713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36335687703481180679194475 54503531555221771018791713)
  ·
    refine ⟨40877648666416328264093785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54503531555221771018791713 40877648666416328264093785)
    ·
      refine ⟨30658236499812246198070339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40877648666416328264093785 30658236499812246198070339)
      ·
        refine ⟨45987354749718369297105509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30658236499812246198070339 45987354749718369297105509)
        ·
          refine ⟨8622629015572194243207283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45987354749718369297105509 8622629015572194243207283)
          ·
            refine ⟨12933943523358291364810925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8622629015572194243207283 12933943523358291364810925)
            ·
              refine ⟨4850228821259359261804097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12933943523358291364810925 4850228821259359261804097)
              ·
                refine ⟨3637671615944519446353073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4850228821259359261804097 3637671615944519446353073)
                ·
                  refine ⟨2728253711958389584764805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3637671615944519446353073 2728253711958389584764805)
                  ·
                    refine ⟨511547570992198047143401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2728253711958389584764805 511547570992198047143401)
                    ·
                      rfl

theorem cell22_1494353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_1494353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494353 prefixEnd_1494353 := by exact prefixLift 1494353
  have htrace : WordTrace (prefixWord ++ tailWord_1494353) baseStart_1494353 baseEnd_1494353 := by
    simpa [prefixWord, tailWord_1494353, baseEnd_1494353] using wordTrace_append hprefix tailTrace_1494353
  have hstable : (prefixWord ++ tailWord_1494353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494353).length < 2 ^ (prefixWord ++ tailWord_1494353).sum := by decide
  have hdescent : baseEnd_1494353 < baseStart_1494353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494357 : List Nat := [1, 3, 2, 2, 3, 2, 3, 2, 4]
def baseStart_1494357 : Nat := 118140960795 + 1494357 * 2 ^ 59
def prefixEnd_1494357 : Nat := 4983230072969 + 3 ^ 40 * 1494357 * 2
def baseEnd_1494357 : Nat := 170516313424647790014463

theorem tailTrace_1494357 : CollatzResearch.WordTrace tailWord_1494357 prefixEnd_1494357 170516313424647790014463 := by
  unfold tailWord_1494357
  simp only [CollatzResearch.WordTrace]
  refine ⟨54503677447207279701937325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36335784964804853134624883 54503677447207279701937325)
  ·
    refine ⟨20438879042702729888226497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54503677447207279701937325 20438879042702729888226497)
    ·
      refine ⟨15329159282027047416169873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20438879042702729888226497 15329159282027047416169873)
      ·
        refine ⟨11496869461520285562127405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15329159282027047416169873 11496869461520285562127405)
        ·
          refine ⟨4311326048070107085797777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11496869461520285562127405 4311326048070107085797777)
          ·
            refine ⟨3233494536052580314348333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4311326048070107085797777 3233494536052580314348333)
            ·
              refine ⟨1212560451019717617880625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3233494536052580314348333 1212560451019717617880625)
              ·
                refine ⟨909420338264788213410469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212560451019717617880625 909420338264788213410469)
                ·
                  refine ⟨170516313424647790014463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909420338264788213410469 170516313424647790014463)
                  ·
                    rfl

theorem cell22_1494357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_1494357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494357 prefixEnd_1494357 := by exact prefixLift 1494357
  have htrace : WordTrace (prefixWord ++ tailWord_1494357) baseStart_1494357 baseEnd_1494357 := by
    simpa [prefixWord, tailWord_1494357, baseEnd_1494357] using wordTrace_append hprefix tailTrace_1494357
  have hstable : (prefixWord ++ tailWord_1494357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494357).length < 2 ^ (prefixWord ++ tailWord_1494357).sum := by decide
  have hdescent : baseEnd_1494357 < baseStart_1494357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494368 : List Nat := [2, 1, 1, 3, 4, 2, 2, 7]
def baseStart_1494368 : Nat := 118140960795 + 1494368 * 2 ^ 59
def prefixEnd_1494368 : Nat := 4983230072969 + 3 ^ 40 * 1494368 * 2
def baseEnd_1494368 : Nat := 56839189533193667557595

theorem tailTrace_1494368 : CollatzResearch.WordTrace tailWord_1494368 prefixEnd_1494368 56839189533193667557595 := by
  unfold tailWord_1494368
  simp only [CollatzResearch.WordTrace]
  refine ⟨27252039325083714290293879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36336052433444952387058505 27252039325083714290293879)
  ·
    refine ⟨40878058987625571435440819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27252039325083714290293879 40878058987625571435440819)
    ·
      refine ⟨61317088481438357153161229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40878058987625571435440819 61317088481438357153161229)
      ·
        refine ⟨22993908180539383932435461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61317088481438357153161229 22993908180539383932435461)
        ·
          refine ⟨4311357783851134487331649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22993908180539383932435461 4311357783851134487331649)
          ·
            refine ⟨3233518337888350865498737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4311357783851134487331649 3233518337888350865498737)
            ·
              refine ⟨2425138753416263149124053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3233518337888350865498737 2425138753416263149124053)
              ·
                refine ⟨56839189533193667557595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2425138753416263149124053 56839189533193667557595)
                ·
                  rfl

theorem cell22_1494368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 7].length) (baseStart_1494368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494368 prefixEnd_1494368 := by exact prefixLift 1494368
  have htrace : WordTrace (prefixWord ++ tailWord_1494368) baseStart_1494368 baseEnd_1494368 := by
    simpa [prefixWord, tailWord_1494368, baseEnd_1494368] using wordTrace_append hprefix tailTrace_1494368
  have hstable : (prefixWord ++ tailWord_1494368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494368).length < 2 ^ (prefixWord ++ tailWord_1494368).sum := by decide
  have hdescent : baseEnd_1494368 < baseStart_1494368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494372 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_1494372 : Nat := 118140960795 + 1494372 * 2 ^ 59
def prefixEnd_1494372 : Nat := 4983230072969 + 3 ^ 40 * 1494372 * 2
def baseEnd_1494372 : Nat := 511554075080488330918343

theorem tailTrace_1494372 : CollatzResearch.WordTrace tailWord_1494372 prefixEnd_1494372 511554075080488330918343 := by
  unfold tailWord_1494372
  simp only [CollatzResearch.WordTrace]
  refine ⟨27252112271076468631866685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36336149694768624842488913 27252112271076468631866685)
  ·
    refine ⟨10219542101653675736950007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27252112271076468631866685 10219542101653675736950007)
    ·
      refine ⟨15329313152480513605425011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10219542101653675736950007 15329313152480513605425011)
      ·
        refine ⟨22993969728720770408137517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15329313152480513605425011 22993969728720770408137517)
        ·
          refine ⟨8622738648270288903051569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22993969728720770408137517 8622738648270288903051569)
          ·
            refine ⟨6467053986202716677288677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8622738648270288903051569 6467053986202716677288677)
            ·
              refine ⟨1212572622413009376991627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6467053986202716677288677 1212572622413009376991627)
              ·
                refine ⟨1818858933619514065487441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212572622413009376991627 1818858933619514065487441)
                ·
                  refine ⟨1364144200214635549115581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1818858933619514065487441 1364144200214635549115581)
                  ·
                    refine ⟨511554075080488330918343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364144200214635549115581 511554075080488330918343)
                    ·
                      rfl

theorem cell22_1494372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_1494372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494372 prefixEnd_1494372 := by exact prefixLift 1494372
  have htrace : WordTrace (prefixWord ++ tailWord_1494372) baseStart_1494372 baseEnd_1494372 := by
    simpa [prefixWord, tailWord_1494372, baseEnd_1494372] using wordTrace_append hprefix tailTrace_1494372
  have hstable : (prefixWord ++ tailWord_1494372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494372).length < 2 ^ (prefixWord ++ tailWord_1494372).sum := by decide
  have hdescent : baseEnd_1494372 < baseStart_1494372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494383 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 5, 3]
def baseStart_1494383 : Nat := 118140960795 + 1494383 * 2 ^ 59
def prefixEnd_1494383 : Nat := 4983230072969 + 3 ^ 40 * 1494383 * 2
def baseEnd_1494383 : Nat := 511557840605287968893309

theorem tailTrace_1494383 : CollatzResearch.WordTrace tailWord_1494383 prefixEnd_1494383 511557840605287968893309 := by
  unfold tailWord_1494383
  simp only [CollatzResearch.WordTrace]
  refine ⟨54504625745113086142383803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36336417163408724094922535 54504625745113086142383803)
  ·
    refine ⟨81756938617669629213575705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54504625745113086142383803 81756938617669629213575705)
    ·
      refine ⟨61317703963252221910181779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81756938617669629213575705 61317703963252221910181779)
      ·
        refine ⟨91976555944878332865272669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61317703963252221910181779 91976555944878332865272669)
        ·
          refine ⟨34491208479329374824477251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91976555944878332865272669 34491208479329374824477251)
          ·
            refine ⟨51736812718994062236715877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34491208479329374824477251 51736812718994062236715877)
            ·
              refine ⟨9700652384811386669384227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51736812718994062236715877 9700652384811386669384227)
              ·
                refine ⟨14550978577217080004076341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9700652384811386669384227 14550978577217080004076341)
                ·
                  refine ⟨1364154241614101250382157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14550978577217080004076341 1364154241614101250382157)
                  ·
                    refine ⟨511557840605287968893309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364154241614101250382157 511557840605287968893309)
                    ·
                      rfl

theorem cell22_1494383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 3].length) (baseStart_1494383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494383 prefixEnd_1494383 := by exact prefixLift 1494383
  have htrace : WordTrace (prefixWord ++ tailWord_1494383) baseStart_1494383 baseEnd_1494383 := by
    simpa [prefixWord, tailWord_1494383, baseEnd_1494383] using wordTrace_append hprefix tailTrace_1494383
  have hstable : (prefixWord ++ tailWord_1494383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494383).length < 2 ^ (prefixWord ++ tailWord_1494383).sum := by decide
  have hdescent : baseEnd_1494383 < baseStart_1494383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494475 : List Nat := [1, 1, 1, 1, 3, 3, 4, 4, 4]
def baseStart_1494475 : Nat := 118140960795 + 1494475 * 2 ^ 59
def prefixEnd_1494475 : Nat := 4983230072969 + 3 ^ 40 * 1494475 * 2
def baseEnd_1494475 : Nat := 170529778028476798531009

theorem tailTrace_1494475 : CollatzResearch.WordTrace tailWord_1494475 prefixEnd_1494475 170529778028476798531009 := by
  unfold tailWord_1494475
  simp only [CollatzResearch.WordTrace]
  refine ⟨54507981260779785854732879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36338654173853190569821919 54507981260779785854732879)
  ·
    refine ⟨81761971891169678782099319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54507981260779785854732879 81761971891169678782099319)
    ·
      refine ⟨122642957836754518173148979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81761971891169678782099319 122642957836754518173148979)
      ·
        refine ⟨183964436755131777259723469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122642957836754518173148979 183964436755131777259723469)
        ·
          refine ⟨68986663783174416472396301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183964436755131777259723469 68986663783174416472396301)
          ·
            refine ⟨25869998918690406177148613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68986663783174416472396301 25869998918690406177148613)
            ·
              refine ⟨4850624797254451158215365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25869998918690406177148613 4850624797254451158215365)
              ·
                refine ⟨909492149485209592165381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4850624797254451158215365 909492149485209592165381)
                ·
                  refine ⟨170529778028476798531009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909492149485209592165381 170529778028476798531009)
                  ·
                    rfl

theorem cell22_1494475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 4].length) (baseStart_1494475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494475 prefixEnd_1494475 := by exact prefixLift 1494475
  have htrace : WordTrace (prefixWord ++ tailWord_1494475) baseStart_1494475 baseEnd_1494475 := by
    simpa [prefixWord, tailWord_1494475, baseEnd_1494475] using wordTrace_append hprefix tailTrace_1494475
  have hstable : (prefixWord ++ tailWord_1494475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494475).length < 2 ^ (prefixWord ++ tailWord_1494475).sum := by decide
  have hdescent : baseEnd_1494475 < baseStart_1494475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494488 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_1494488 : Nat := 118140960795 + 1494488 * 2 ^ 59
def prefixEnd_1494488 : Nat := 4983230072969 + 3 ^ 40 * 1494488 * 2
def baseEnd_1494488 : Nat := 511593784251102695017987

theorem tailTrace_1494488 : CollatzResearch.WordTrace tailWord_1494488 prefixEnd_1494488 511593784251102695017987 := by
  unfold tailWord_1494488
  simp only [CollatzResearch.WordTrace]
  refine ⟨27254227704866344537478059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36338970273155126049970745 27254227704866344537478059)
  ·
    refine ⟨40881341557299516806217089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27254227704866344537478059 40881341557299516806217089)
    ·
      refine ⟨30661006167974637604662817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40881341557299516806217089 30661006167974637604662817)
      ·
        refine ⟨22995754625980978203497113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30661006167974637604662817 22995754625980978203497113)
        ·
          refine ⟨17246815969485733652622835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22995754625980978203497113 17246815969485733652622835)
          ·
            refine ⟨25870223954228600478934253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17246815969485733652622835 25870223954228600478934253)
            ·
              refine ⟨9701333982835725179600345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25870223954228600478934253 9701333982835725179600345)
              ·
                refine ⟨7276000487126793884700259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9701333982835725179600345 7276000487126793884700259)
                ·
                  refine ⟨10914000730690190827050389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7276000487126793884700259 10914000730690190827050389)
                  ·
                    refine ⟨511593784251102695017987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10914000730690190827050389 511593784251102695017987)
                    ·
                      rfl

theorem cell22_1494488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_1494488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494488 prefixEnd_1494488 := by exact prefixLift 1494488
  have htrace : WordTrace (prefixWord ++ tailWord_1494488) baseStart_1494488 baseEnd_1494488 := by
    simpa [prefixWord, tailWord_1494488, baseEnd_1494488] using wordTrace_append hprefix tailTrace_1494488
  have hstable : (prefixWord ++ tailWord_1494488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494488).length < 2 ^ (prefixWord ++ tailWord_1494488).sum := by decide
  have hdescent : baseEnd_1494488 < baseStart_1494488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494490 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_1494490 : Nat := 118140960795 + 1494490 * 2 ^ 59
def prefixEnd_1494490 : Nat := 4983230072969 + 3 ^ 40 * 1494490 * 2
def baseEnd_1494490 : Nat := 511594468891975356467981

theorem tailTrace_1494490 : CollatzResearch.WordTrace tailWord_1494490 prefixEnd_1494490 511594468891975356467981 := by
  unfold tailWord_1494490
  simp only [CollatzResearch.WordTrace]
  refine ⟨13627132088931360854132231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36339018903816962277685949 13627132088931360854132231)
  ·
    refine ⟨20440698133397041281198347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13627132088931360854132231 20440698133397041281198347)
    ·
      refine ⟨30661047200095561921797521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20440698133397041281198347 30661047200095561921797521)
      ·
        refine ⟨22995785400071671441348141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30661047200095561921797521 22995785400071671441348141)
        ·
          refine ⟨8623419525026876790505553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22995785400071671441348141 8623419525026876790505553)
          ·
            refine ⟨6467564643770157592879165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8623419525026876790505553 6467564643770157592879165)
            ·
              refine ⟨2425336741413809097329687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6467564643770157592879165 2425336741413809097329687)
              ·
                refine ⟨3638005112120713645994531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425336741413809097329687 3638005112120713645994531)
                ·
                  refine ⟨5457007668181070468991797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3638005112120713645994531 5457007668181070468991797)
                  ·
                    refine ⟨511594468891975356467981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5457007668181070468991797 511594468891975356467981)
                    ·
                      rfl

theorem cell22_1494490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_1494490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494490 prefixEnd_1494490 := by exact prefixLift 1494490
  have htrace : WordTrace (prefixWord ++ tailWord_1494490) baseStart_1494490 baseEnd_1494490 := by
    simpa [prefixWord, tailWord_1494490, baseEnd_1494490] using wordTrace_append hprefix tailTrace_1494490
  have hstable : (prefixWord ++ tailWord_1494490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494490).length < 2 ^ (prefixWord ++ tailWord_1494490).sum := by decide
  have hdescent : baseEnd_1494490 < baseStart_1494490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494526 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_1494526 : Nat := 118140960795 + 1494526 * 2 ^ 59
def prefixEnd_1494526 : Nat := 4983230072969 + 3 ^ 40 * 1494526 * 2
def baseEnd_1494526 : Nat := 170535597475894420855957

theorem tailTrace_1494526 : CollatzResearch.WordTrace tailWord_1494526 prefixEnd_1494526 170535597475894420855957 := by
  unfold tailWord_1494526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6813730172949377695604929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36339894255730014376559621 6813730172949377695604929)
  ·
    refine ⟨5110297629712033271703697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6813730172949377695604929 5110297629712033271703697)
    ·
      refine ⟨3832723222284024953777773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5110297629712033271703697 3832723222284024953777773)
      ·
        refine ⟨1437271208356509357666665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3832723222284024953777773 1437271208356509357666665)
        ·
          refine ⟨1077953406267382018249999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437271208356509357666665 1077953406267382018249999)
          ·
            refine ⟨1616930109401073027374999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077953406267382018249999 1616930109401073027374999)
            ·
              refine ⟨2425395164101609541062499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616930109401073027374999 2425395164101609541062499)
              ·
                refine ⟨3638092746152414311593749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425395164101609541062499 3638092746152414311593749)
                ·
                  refine ⟨170535597475894420855957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3638092746152414311593749 170535597475894420855957)
                  ·
                    rfl

theorem cell22_1494526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_1494526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494526 prefixEnd_1494526 := by exact prefixLift 1494526
  have htrace : WordTrace (prefixWord ++ tailWord_1494526) baseStart_1494526 baseEnd_1494526 := by
    simpa [prefixWord, tailWord_1494526, baseEnd_1494526] using wordTrace_append hprefix tailTrace_1494526
  have hstable : (prefixWord ++ tailWord_1494526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494526).length < 2 ^ (prefixWord ++ tailWord_1494526).sum := by decide
  have hdescent : baseEnd_1494526 < baseStart_1494526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494533 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_1494533 : Nat := 118140960795 + 1494533 * 2 ^ 59
def prefixEnd_1494533 : Nat := 4983230072969 + 3 ^ 40 * 1494533 * 2
def baseEnd_1494533 : Nat := 511609188670737577642849

theorem tailTrace_1494533 : CollatzResearch.WordTrace tailWord_1494533 prefixEnd_1494533 511609188670737577642849 := by
  unfold tailWord_1494533
  simp only [CollatzResearch.WordTrace]
  refine ⟨54510096694569661760344253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36340064463046441173562835 54510096694569661760344253)
  ·
    refine ⟨20441286260463623160129095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54510096694569661760344253 20441286260463623160129095)
    ·
      refine ⟨30661929390695434740193643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20441286260463623160129095 30661929390695434740193643)
      ·
        refine ⟨45992894086043152110290465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30661929390695434740193643 45992894086043152110290465)
        ·
          refine ⟨34494670564532364082717849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45992894086043152110290465 34494670564532364082717849)
          ·
            refine ⟨25871002923399273062038387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34494670564532364082717849 25871002923399273062038387)
            ·
              refine ⟨38806504385098909593057581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25871002923399273062038387 38806504385098909593057581)
              ·
                refine ⟨14552439144412091097396593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38806504385098909593057581 14552439144412091097396593)
                ·
                  refine ⟨10914329358309068323047445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14552439144412091097396593 10914329358309068323047445)
                  ·
                    refine ⟨511609188670737577642849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10914329358309068323047445 511609188670737577642849)
                    ·
                      rfl

theorem cell22_1494533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_1494533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494533 prefixEnd_1494533 := by exact prefixLift 1494533
  have htrace : WordTrace (prefixWord ++ tailWord_1494533) baseStart_1494533 baseEnd_1494533 := by
    simpa [prefixWord, tailWord_1494533, baseEnd_1494533] using wordTrace_append hprefix tailTrace_1494533
  have hstable : (prefixWord ++ tailWord_1494533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494533).length < 2 ^ (prefixWord ++ tailWord_1494533).sum := by decide
  have hdescent : baseEnd_1494533 < baseStart_1494533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494610 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1494610 : Nat := 118140960795 + 1494610 * 2 ^ 59
def prefixEnd_1494610 : Nat := 4983230072969 + 3 ^ 40 * 1494610 * 2
def baseEnd_1494610 : Nat := 170545182448111681155871

theorem tailTrace_1494610 : CollatzResearch.WordTrace tailWord_1494610 prefixEnd_1494610 170545182448111681155871 := by
  unfold tailWord_1494610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13628226278822675977724321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36341936743527135940598189 13628226278822675977724321)
  ·
    refine ⟨10221169709117006983293241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13628226278822675977724321 10221169709117006983293241)
    ·
      refine ⟨7665877281837755237469931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10221169709117006983293241 7665877281837755237469931)
      ·
        refine ⟨11498815922756632856204897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7665877281837755237469931 11498815922756632856204897)
        ·
          refine ⟨8624111942067474642153673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11498815922756632856204897 8624111942067474642153673)
          ·
            refine ⟨6468083956550605981615255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8624111942067474642153673 6468083956550605981615255)
            ·
              refine ⟨9702125934825908972422883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468083956550605981615255 9702125934825908972422883)
              ·
                refine ⟨14553188902238863458634325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9702125934825908972422883 14553188902238863458634325)
                ·
                  refine ⟨170545182448111681155871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14553188902238863458634325 170545182448111681155871)
                  ·
                    rfl

theorem cell22_1494610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1494610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494610 prefixEnd_1494610 := by exact prefixLift 1494610
  have htrace : WordTrace (prefixWord ++ tailWord_1494610) baseStart_1494610 baseEnd_1494610 := by
    simpa [prefixWord, tailWord_1494610, baseEnd_1494610] using wordTrace_append hprefix tailTrace_1494610
  have hstable : (prefixWord ++ tailWord_1494610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494610).length < 2 ^ (prefixWord ++ tailWord_1494610).sum := by decide
  have hdescent : baseEnd_1494610 < baseStart_1494610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494612 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1494612 : Nat := 118140960795 + 1494612 * 2 ^ 59
def prefixEnd_1494612 : Nat := 4983230072969 + 3 ^ 40 * 1494612 * 2
def baseEnd_1494612 : Nat := 511636231985207704917607

theorem tailTrace_1494612 : CollatzResearch.WordTrace tailWord_1494612 prefixEnd_1494612 511636231985207704917607 := by
  unfold tailWord_1494612
  simp only [CollatzResearch.WordTrace]
  refine ⟨27256489030641729126235045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36341985374188972168313393 27256489030641729126235045)
  ·
    refine ⟨5110591693245324211169071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27256489030641729126235045 5110591693245324211169071)
    ·
      refine ⟨7665887539867986316753607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5110591693245324211169071 7665887539867986316753607)
      ·
        refine ⟨11498831309801979475130411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7665887539867986316753607 11498831309801979475130411)
        ·
          refine ⟨17248246964702969212695617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11498831309801979475130411 17248246964702969212695617)
          ·
            refine ⟨12936185223527226909521713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17248246964702969212695617 12936185223527226909521713)
            ·
              refine ⟨9702138917645420182141285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12936185223527226909521713 9702138917645420182141285)
              ·
                refine ⟨1819151047058516284151491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9702138917645420182141285 1819151047058516284151491)
                ·
                  refine ⟨2728726570587774426227237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819151047058516284151491 2728726570587774426227237)
                  ·
                    refine ⟨511636231985207704917607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2728726570587774426227237 511636231985207704917607)
                    ·
                      rfl

theorem cell22_1494612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1494612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494612 prefixEnd_1494612 := by exact prefixLift 1494612
  have htrace : WordTrace (prefixWord ++ tailWord_1494612) baseStart_1494612 baseEnd_1494612 := by
    simpa [prefixWord, tailWord_1494612, baseEnd_1494612] using wordTrace_append hprefix tailTrace_1494612
  have hstable : (prefixWord ++ tailWord_1494612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494612).length < 2 ^ (prefixWord ++ tailWord_1494612).sum := by decide
  have hdescent : baseEnd_1494612 < baseStart_1494612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494625 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_1494625 : Nat := 118140960795 + 1494625 * 2 ^ 59
def prefixEnd_1494625 : Nat := 4983230072969 + 3 ^ 40 * 1494625 * 2
def baseEnd_1494625 : Nat := 511640682150880004342567

theorem tailTrace_1494625 : CollatzResearch.WordTrace tailWord_1494625 prefixEnd_1494625 511640682150880004342567 := by
  unfold tailWord_1494625
  simp only [CollatzResearch.WordTrace]
  refine ⟨54513452210236361472693329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36342301473490907648462219 54513452210236361472693329)
  ·
    refine ⟨40885089157677271104519997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54513452210236361472693329 40885089157677271104519997)
    ·
      refine ⟨15331908434128976664194999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40885089157677271104519997 15331908434128976664194999)
      ·
        refine ⟨22997862651193464996292499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15331908434128976664194999 22997862651193464996292499)
        ·
          refine ⟨34496793976790197494438749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22997862651193464996292499 34496793976790197494438749)
          ·
            refine ⟨12936297741296324060414531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34496793976790197494438749 12936297741296324060414531)
            ·
              refine ⟨19404446611944486090621797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12936297741296324060414531 19404446611944486090621797)
              ·
                refine ⟨3638333739739591141991587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19404446611944486090621797 3638333739739591141991587)
                ·
                  refine ⟨5457500609609386712987381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3638333739739591141991587 5457500609609386712987381)
                  ·
                    refine ⟨511640682150880004342567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5457500609609386712987381 511640682150880004342567)
                    ·
                      rfl

theorem cell22_1494625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_1494625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494625 prefixEnd_1494625 := by exact prefixLift 1494625
  have htrace : WordTrace (prefixWord ++ tailWord_1494625) baseStart_1494625 baseEnd_1494625 := by
    simpa [prefixWord, tailWord_1494625, baseEnd_1494625] using wordTrace_append hprefix tailTrace_1494625
  have hstable : (prefixWord ++ tailWord_1494625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494625).length < 2 ^ (prefixWord ++ tailWord_1494625).sum := by decide
  have hdescent : baseEnd_1494625 < baseStart_1494625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494627 : List Nat := [1, 1, 1, 5, 1, 3, 1, 5, 4]
def baseStart_1494627 : Nat := 118140960795 + 1494627 * 2 ^ 59
def prefixEnd_1494627 : Nat := 4983230072969 + 3 ^ 40 * 1494627 * 2
def baseEnd_1494627 : Nat := 170547122263917555264187

theorem tailTrace_1494627 : CollatzResearch.WordTrace tailWord_1494627 prefixEnd_1494627 170547122263917555264187 := by
  unfold tailWord_1494627
  simp only [CollatzResearch.WordTrace]
  refine ⟨54513525156229115814266135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36342350104152743876177423 54513525156229115814266135)
  ·
    refine ⟨81770287734343673721399203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54513525156229115814266135 81770287734343673721399203)
    ·
      refine ⟨122655431601515510582098805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81770287734343673721399203 122655431601515510582098805)
      ·
        refine ⟨11498946712642079117071763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122655431601515510582098805 11498946712642079117071763)
        ·
          refine ⟨17248420068963118675607645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11498946712642079117071763 17248420068963118675607645)
          ·
            refine ⟨6468157525861169503352867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17248420068963118675607645 6468157525861169503352867)
            ·
              refine ⟨9702236288791754255029301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468157525861169503352867 9702236288791754255029301)
              ·
                refine ⟨909584652074226961408997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9702236288791754255029301 909584652074226961408997)
                ·
                  refine ⟨170547122263917555264187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909584652074226961408997 170547122263917555264187)
                  ·
                    rfl

theorem cell22_1494627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 4].length) (baseStart_1494627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494627 prefixEnd_1494627 := by exact prefixLift 1494627
  have htrace : WordTrace (prefixWord ++ tailWord_1494627) baseStart_1494627 baseEnd_1494627 := by
    simpa [prefixWord, tailWord_1494627, baseEnd_1494627] using wordTrace_append hprefix tailTrace_1494627
  have hstable : (prefixWord ++ tailWord_1494627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494627).length < 2 ^ (prefixWord ++ tailWord_1494627).sum := by decide
  have hdescent : baseEnd_1494627 < baseStart_1494627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494629 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 1, 4]
def baseStart_1494629 : Nat := 118140960795 + 1494629 * 2 ^ 59
def prefixEnd_1494629 : Nat := 4983230072969 + 3 ^ 40 * 1494629 * 2
def baseEnd_1494629 : Nat := 511642051432625327242555

theorem tailTrace_1494629 : CollatzResearch.WordTrace tailWord_1494629 prefixEnd_1494629 511642051432625327242555 := by
  unfold tailWord_1494629
  simp only [CollatzResearch.WordTrace]
  refine ⟨54513598102221870155838941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36342398734814580103892627 54513598102221870155838941)
  ·
    refine ⟨20442599288333201308439603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54513598102221870155838941 20442599288333201308439603)
    ·
      refine ⟨30663898932499801962659405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20442599288333201308439603 30663898932499801962659405)
      ·
        refine ⟨11498962099687425735997277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30663898932499801962659405 11498962099687425735997277)
        ·
          refine ⟨4312110787382784650998979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11498962099687425735997277 4312110787382784650998979)
          ·
            refine ⟨6468166181074176976498469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312110787382784650998979 6468166181074176976498469)
            ·
              refine ⟨1212781158951408183093463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6468166181074176976498469 1212781158951408183093463)
              ·
                refine ⟨1819171738427112274640195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212781158951408183093463 1819171738427112274640195)
                ·
                  refine ⟨2728757607640668411960293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819171738427112274640195 2728757607640668411960293)
                  ·
                    refine ⟨511642051432625327242555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2728757607640668411960293 511642051432625327242555)
                    ·
                      rfl

theorem cell22_1494629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_1494629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494629 prefixEnd_1494629 := by exact prefixLift 1494629
  have htrace : WordTrace (prefixWord ++ tailWord_1494629) baseStart_1494629 baseEnd_1494629 := by
    simpa [prefixWord, tailWord_1494629, baseEnd_1494629] using wordTrace_append hprefix tailTrace_1494629
  have hstable : (prefixWord ++ tailWord_1494629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494629).length < 2 ^ (prefixWord ++ tailWord_1494629).sum := by decide
  have hdescent : baseEnd_1494629 < baseStart_1494629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494685 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1494685 : Nat := 118140960795 + 1494685 * 2 ^ 59
def prefixEnd_1494685 : Nat := 4983230072969 + 3 ^ 40 * 1494685 * 2
def baseEnd_1494685 : Nat := 511661221377059847842383

theorem tailTrace_1494685 : CollatzResearch.WordTrace tailWord_1494685 prefixEnd_1494685 511661221377059847842383 := by
  unfold tailWord_1494685
  simp only [CollatzResearch.WordTrace]
  refine ⟨54515640590018991719877509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36343760393345994479918339 54515640590018991719877509)
  ·
    refine ⟨10221682610628560947477033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54515640590018991719877509 10221682610628560947477033)
    ·
      refine ⟨7666261957971420710607775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10221682610628560947477033 7666261957971420710607775)
      ·
        refine ⟨11499392936957131065911663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7666261957971420710607775 11499392936957131065911663)
        ·
          refine ⟨17249089405435696598867495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11499392936957131065911663 17249089405435696598867495)
          ·
            refine ⟨25873634108153544898301243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17249089405435696598867495 25873634108153544898301243)
            ·
              refine ⟨38810451162230317347451865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25873634108153544898301243 38810451162230317347451865)
              ·
                refine ⟨29107838371672738010588899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38810451162230317347451865 29107838371672738010588899)
                ·
                  refine ⟨43661757557509107015883349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29107838371672738010588899 43661757557509107015883349)
                  ·
                    refine ⟨511661221377059847842383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43661757557509107015883349 511661221377059847842383)
                    ·
                      rfl

theorem cell22_1494685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1494685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494685 prefixEnd_1494685 := by exact prefixLift 1494685
  have htrace : WordTrace (prefixWord ++ tailWord_1494685) baseStart_1494685 baseEnd_1494685 := by
    simpa [prefixWord, tailWord_1494685, baseEnd_1494685] using wordTrace_append hprefix tailTrace_1494685
  have hstable : (prefixWord ++ tailWord_1494685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494685).length < 2 ^ (prefixWord ++ tailWord_1494685).sum := by decide
  have hdescent : baseEnd_1494685 < baseStart_1494685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494704 : List Nat := [2, 1, 1, 1, 2, 1, 4, 6, 1, 3]
def baseStart_1494704 : Nat := 118140960795 + 1494704 * 2 ^ 59
def prefixEnd_1494704 : Nat := 4983230072969 + 3 ^ 40 * 1494704 * 2
def baseEnd_1494704 : Nat := 511667725465350131617325

theorem tailTrace_1494704 : CollatzResearch.WordTrace tailWord_1494704 prefixEnd_1494704 511667725465350131617325 := by
  unfold tailWord_1494704
  simp only [CollatzResearch.WordTrace]
  refine ⟨27258166788475078982409583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36344222384633438643212777 27258166788475078982409583)
  ·
    refine ⟨40887250182712618473614375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27258166788475078982409583 40887250182712618473614375)
    ·
      refine ⟨61330875274068927710421563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40887250182712618473614375 61330875274068927710421563)
      ·
        refine ⟨91996312911103391565632345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61330875274068927710421563 91996312911103391565632345)
        ·
          refine ⟨68997234683327543674224259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91996312911103391565632345 68997234683327543674224259)
          ·
            refine ⟨103495852024991315511336389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68997234683327543674224259 103495852024991315511336389)
            ·
              refine ⟨19405472254685871658375573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103495852024991315511336389 19405472254685871658375573)
              ·
                refine ⟨909631511938400233986355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19405472254685871658375573 909631511938400233986355)
                ·
                  refine ⟨1364447267907600350979533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909631511938400233986355 1364447267907600350979533)
                  ·
                    refine ⟨511667725465350131617325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364447267907600350979533 511667725465350131617325)
                    ·
                      rfl

theorem cell22_1494704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 1, 3].length) (baseStart_1494704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494704 prefixEnd_1494704 := by exact prefixLift 1494704
  have htrace : WordTrace (prefixWord ++ tailWord_1494704) baseStart_1494704 baseEnd_1494704 := by
    simpa [prefixWord, tailWord_1494704, baseEnd_1494704] using wordTrace_append hprefix tailTrace_1494704
  have hstable : (prefixWord ++ tailWord_1494704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494704).length < 2 ^ (prefixWord ++ tailWord_1494704).sum := by decide
  have hdescent : baseEnd_1494704 < baseStart_1494704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494710 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1494710 : Nat := 118140960795 + 1494710 * 2 ^ 59
def prefixEnd_1494710 : Nat := 4983230072969 + 3 ^ 40 * 1494710 * 2
def baseEnd_1494710 : Nat := 511669779387968115967307

theorem tailTrace_1494710 : CollatzResearch.WordTrace tailWord_1494710 prefixEnd_1494710 511669779387968115967307 := by
  unfold tailWord_1494710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3407284525933026311846099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36344368276618947326358389 3407284525933026311846099)
  ·
    refine ⟨5110926788899539467769149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3407284525933026311846099 5110926788899539467769149)
    ·
      refine ⟨1916597545837327300413431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5110926788899539467769149 1916597545837327300413431)
      ·
        refine ⟨2874896318755990950620147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916597545837327300413431 2874896318755990950620147)
        ·
          refine ⟨4312344478133986425930221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874896318755990950620147 4312344478133986425930221)
          ·
            refine ⟨1617129179300244909723833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4312344478133986425930221 1617129179300244909723833)
            ·
              refine ⟨1212846884475183682292875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617129179300244909723833 1212846884475183682292875)
              ·
                refine ⟨1819270326712775523439313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212846884475183682292875 1819270326712775523439313)
                ·
                  refine ⟨1364452745034581642579485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1819270326712775523439313 1364452745034581642579485)
                  ·
                    refine ⟨511669779387968115967307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364452745034581642579485 511669779387968115967307)
                    ·
                      rfl

theorem cell22_1494710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1494710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494710 prefixEnd_1494710 := by exact prefixLift 1494710
  have htrace : WordTrace (prefixWord ++ tailWord_1494710) baseStart_1494710 baseEnd_1494710 := by
    simpa [prefixWord, tailWord_1494710, baseEnd_1494710] using wordTrace_append hprefix tailTrace_1494710
  have hstable : (prefixWord ++ tailWord_1494710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494710).length < 2 ^ (prefixWord ++ tailWord_1494710).sum := by decide
  have hdescent : baseEnd_1494710 < baseStart_1494710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494715 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 2, 5]
def baseStart_1494715 : Nat := 118140960795 + 1494715 * 2 ^ 59
def prefixEnd_1494715 : Nat := 4983230072969 + 3 ^ 40 * 1494715 * 2
def baseEnd_1494715 : Nat := 511671490990149769592291

theorem tailTrace_1494715 : CollatzResearch.WordTrace tailWord_1494715 prefixEnd_1494715 511671490990149769592291 := by
  unfold tailWord_1494715
  simp only [CollatzResearch.WordTrace]
  refine ⟨54516734779910306843469599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36344489853273537895646399 54516734779910306843469599)
  ·
    refine ⟨81775102169865460265204399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54516734779910306843469599 81775102169865460265204399)
    ·
      refine ⟨122662653254798190397806599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81775102169865460265204399 122662653254798190397806599)
      ·
        refine ⟨183993979882197285596709899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122662653254798190397806599 183993979882197285596709899)
        ·
          refine ⟨275990969823295928395064849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183993979882197285596709899 275990969823295928395064849)
          ·
            refine ⟨206993227367471946296298637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275990969823295928395064849 206993227367471946296298637)
            ·
              refine ⟨77622460262801979861111989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206993227367471946296298637 77622460262801979861111989)
              ·
                refine ⟨7277105649637685611979249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77622460262801979861111989 7277105649637685611979249)
                ·
                  refine ⟨5457829237228264208984437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7277105649637685611979249 5457829237228264208984437)
                  ·
                    refine ⟨511671490990149769592291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5457829237228264208984437 511671490990149769592291)
                    ·
                      rfl

theorem cell22_1494715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_1494715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494715 prefixEnd_1494715 := by exact prefixLift 1494715
  have htrace : WordTrace (prefixWord ++ tailWord_1494715) baseStart_1494715 baseEnd_1494715 := by
    simpa [prefixWord, tailWord_1494715, baseEnd_1494715] using wordTrace_append hprefix tailTrace_1494715
  have hstable : (prefixWord ++ tailWord_1494715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494715).length < 2 ^ (prefixWord ++ tailWord_1494715).sum := by decide
  have hdescent : baseEnd_1494715 < baseStart_1494715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494717 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 5]
def baseStart_1494717 : Nat := 118140960795 + 1494717 * 2 ^ 59
def prefixEnd_1494717 : Nat := 4983230072969 + 3 ^ 40 * 1494717 * 2
def baseEnd_1494717 : Nat := 170557391877007477014095

theorem tailTrace_1494717 : CollatzResearch.WordTrace tailWord_1494717 prefixEnd_1494717 170557391877007477014095 := by
  unfold tailWord_1494717
  simp only [CollatzResearch.WordTrace]
  refine ⟨54516807725903061185042405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36344538483935374123361603 54516807725903061185042405)
  ·
    refine ⟨10221901448606823972195451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54516807725903061185042405 10221901448606823972195451)
    ·
      refine ⟨15332852172910235958293177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10221901448606823972195451 15332852172910235958293177)
      ·
        refine ⟨11499639129682676968719883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15332852172910235958293177 11499639129682676968719883)
        ·
          refine ⟨17249458694524015453079825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11499639129682676968719883 17249458694524015453079825)
          ·
            refine ⟨12937094020893011589809869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17249458694524015453079825 12937094020893011589809869)
            ·
              refine ⟨4851410257834879346178701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12937094020893011589809869 4851410257834879346178701)
              ·
                refine ⟨1819278846688079754817013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4851410257834879346178701 1819278846688079754817013)
                ·
                  refine ⟨170557391877007477014095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1819278846688079754817013 170557391877007477014095)
                  ·
                    rfl

theorem cell22_1494717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_1494717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494717 prefixEnd_1494717 := by exact prefixLift 1494717
  have htrace : WordTrace (prefixWord ++ tailWord_1494717) baseStart_1494717 baseEnd_1494717 := by
    simpa [prefixWord, tailWord_1494717, baseEnd_1494717] using wordTrace_append hprefix tailTrace_1494717
  have hstable : (prefixWord ++ tailWord_1494717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494717).length < 2 ^ (prefixWord ++ tailWord_1494717).sum := by decide
  have hdescent : baseEnd_1494717 < baseStart_1494717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494755 : List Nat := [1, 1, 1, 7, 2, 2, 2, 2, 1, 3]
def baseStart_1494755 : Nat := 118140960795 + 1494755 * 2 ^ 59
def prefixEnd_1494755 : Nat := 4983230072969 + 3 ^ 40 * 1494755 * 2
def baseEnd_1494755 : Nat := 511685183807602998592169

theorem tailTrace_1494755 : CollatzResearch.WordTrace tailWord_1494755 prefixEnd_1494755 511685183807602998592169 := by
  unfold tailWord_1494755
  simp only [CollatzResearch.WordTrace]
  refine ⟨54518193699765393674925719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36345462466510262449950479 54518193699765393674925719)
  ·
    refine ⟨81777290549648090512388579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54518193699765393674925719 81777290549648090512388579)
    ·
      refine ⟨122665935824472135768582869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81777290549648090512388579 122665935824472135768582869)
      ·
        refine ⟨2874982870886065682076161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 122665935824472135768582869 2874982870886065682076161)
        ·
          refine ⟨2156237153164549261557121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2874982870886065682076161 2156237153164549261557121)
          ·
            refine ⟨1617177864873411946167841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2156237153164549261557121 1617177864873411946167841)
            ·
              refine ⟨1212883398655058959625881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617177864873411946167841 1212883398655058959625881)
              ·
                refine ⟨909662548991294219719411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212883398655058959625881 909662548991294219719411)
                ·
                  refine ⟨1364493823486941329579117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909662548991294219719411 1364493823486941329579117)
                  ·
                    refine ⟨511685183807602998592169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364493823486941329579117 511685183807602998592169)
                    ·
                      rfl

theorem cell22_1494755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 1, 3].length) (baseStart_1494755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494755 prefixEnd_1494755 := by exact prefixLift 1494755
  have htrace : WordTrace (prefixWord ++ tailWord_1494755) baseStart_1494755 baseEnd_1494755 := by
    simpa [prefixWord, tailWord_1494755, baseEnd_1494755] using wordTrace_append hprefix tailTrace_1494755
  have hstable : (prefixWord ++ tailWord_1494755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494755).length < 2 ^ (prefixWord ++ tailWord_1494755).sum := by decide
  have hdescent : baseEnd_1494755 < baseStart_1494755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494777 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 8, 3]
def baseStart_1494777 : Nat := 118140960795 + 1494777 * 2 ^ 59
def prefixEnd_1494777 : Nat := 4983230072969 + 3 ^ 40 * 1494777 * 2
def baseEnd_1494777 : Nat := 511692714857202274542101

theorem tailTrace_1494777 : CollatzResearch.WordTrace tailWord_1494777 prefixEnd_1494777 511692714857202274542101 := by
  unfold tailWord_1494777
  simp only [CollatzResearch.WordTrace]
  refine ⟨54518996105685691432226585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36345997403790460954817723 54518996105685691432226585)
  ·
    refine ⟨40889247079264268574169939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54518996105685691432226585 40889247079264268574169939)
    ·
      refine ⟨61333870618896402861254909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40889247079264268574169939 61333870618896402861254909)
      ·
        refine ⟨23000201482086151072970591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61333870618896402861254909 23000201482086151072970591)
        ·
          refine ⟨34500302223129226609455887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23000201482086151072970591 34500302223129226609455887)
          ·
            refine ⟨51750453334693839914183831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34500302223129226609455887 51750453334693839914183831)
            ·
              refine ⟨77625680002040759871275747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51750453334693839914183831 77625680002040759871275747)
              ·
                refine ⟨116438520003061139806913621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77625680002040759871275747 116438520003061139806913621)
                ·
                  refine ⟨1364513906285872732112269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 116438520003061139806913621 1364513906285872732112269)
                  ·
                    refine ⟨511692714857202274542101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364513906285872732112269 511692714857202274542101)
                    ·
                      rfl

theorem cell22_1494777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 3].length) (baseStart_1494777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494777 prefixEnd_1494777 := by exact prefixLift 1494777
  have htrace : WordTrace (prefixWord ++ tailWord_1494777) baseStart_1494777 baseEnd_1494777 := by
    simpa [prefixWord, tailWord_1494777, baseEnd_1494777] using wordTrace_append hprefix tailTrace_1494777
  have hstable : (prefixWord ++ tailWord_1494777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494777).length < 2 ^ (prefixWord ++ tailWord_1494777).sum := by decide
  have hdescent : baseEnd_1494777 < baseStart_1494777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494792 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_1494792 : Nat := 118140960795 + 1494792 * 2 ^ 59
def prefixEnd_1494792 : Nat := 4983230072969 + 3 ^ 40 * 1494792 * 2
def baseEnd_1494792 : Nat := 511697849663747235417055

theorem tailTrace_1494792 : CollatzResearch.WordTrace tailWord_1494792 prefixEnd_1494792 511697849663747235417055 := by
  unfold tailWord_1494792
  simp only [CollatzResearch.WordTrace]
  refine ⟨27259771600315674497011315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36346362133754232662681753 27259771600315674497011315)
  ·
    refine ⟨40889657400473511745516973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27259771600315674497011315 40889657400473511745516973)
    ·
      refine ⟨15333621525177566904568865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40889657400473511745516973 15333621525177566904568865)
      ·
        refine ⟨11500216143883175178426649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15333621525177566904568865 11500216143883175178426649)
        ·
          refine ⟨8625162107912381383819987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11500216143883175178426649 8625162107912381383819987)
          ·
            refine ⟨12937743161868572075729981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8625162107912381383819987 12937743161868572075729981)
            ·
              refine ⟨4851653685700714528398743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12937743161868572075729981 4851653685700714528398743)
              ·
                refine ⟨7277480528551071792598115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851653685700714528398743 7277480528551071792598115)
                ·
                  refine ⟨10916220792826607688897173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7277480528551071792598115 10916220792826607688897173)
                  ·
                    refine ⟨511697849663747235417055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10916220792826607688897173 511697849663747235417055)
                    ·
                      rfl

theorem cell22_1494792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_1494792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494792 prefixEnd_1494792 := by exact prefixLift 1494792
  have htrace : WordTrace (prefixWord ++ tailWord_1494792) baseStart_1494792 baseEnd_1494792 := by
    simpa [prefixWord, tailWord_1494792, baseEnd_1494792] using wordTrace_append hprefix tailTrace_1494792
  have hstable : (prefixWord ++ tailWord_1494792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494792).length < 2 ^ (prefixWord ++ tailWord_1494792).sum := by decide
  have hdescent : baseEnd_1494792 < baseStart_1494792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494807 : List Nat := [1, 1, 3, 4, 2, 2, 9]
def baseStart_1494807 : Nat := 118140960795 + 1494807 * 2 ^ 59
def prefixEnd_1494807 : Nat := 4983230072969 + 3 ^ 40 * 1494807 * 2
def baseEnd_1494807 : Nat := 18951962387788599862667

theorem tailTrace_1494807 : CollatzResearch.WordTrace tailWord_1494807 prefixEnd_1494807 18951962387788599862667 := by
  unfold tailWord_1494807
  simp only [CollatzResearch.WordTrace]
  refine ⟨54520090295577006555818675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36346726863718004370545783 54520090295577006555818675)
  ·
    refine ⟨81780135443365509833728013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54520090295577006555818675 81780135443365509833728013)
    ·
      refine ⟨30667550791262066187648005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81780135443365509833728013 30667550791262066187648005)
      ·
        refine ⟨5750165773361637410184001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30667550791262066187648005 5750165773361637410184001)
        ·
          refine ⟨4312624330021228057638001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5750165773361637410184001 4312624330021228057638001)
          ·
            refine ⟨3234468247515921043228501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4312624330021228057638001 3234468247515921043228501)
            ·
              refine ⟨18951962387788599862667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3234468247515921043228501 18951962387788599862667)
              ·
                rfl

theorem cell22_1494807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 9].length) (baseStart_1494807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494807 prefixEnd_1494807 := by exact prefixLift 1494807
  have htrace : WordTrace (prefixWord ++ tailWord_1494807) baseStart_1494807 baseEnd_1494807 := by
    simpa [prefixWord, tailWord_1494807, baseEnd_1494807] using wordTrace_append hprefix tailTrace_1494807
  have hstable : (prefixWord ++ tailWord_1494807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494807).length < 2 ^ (prefixWord ++ tailWord_1494807).sum := by decide
  have hdescent : baseEnd_1494807 < baseStart_1494807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494873 : List Nat := [1, 2, 1, 2, 2, 3, 5, 2, 1, 3]
def baseStart_1494873 : Nat := 118140960795 + 1494873 * 2 ^ 59
def prefixEnd_1494873 : Nat := 4983230072969 + 3 ^ 40 * 1494873 * 2
def baseEnd_1494873 : Nat := 511725577619090024141807

theorem tailTrace_1494873 : CollatzResearch.WordTrace tailWord_1494873 prefixEnd_1494873 511725577619090024141807 := by
  unfold tailWord_1494873
  simp only [CollatzResearch.WordTrace]
  refine ⟨54522497513337899827721273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36348331675558599885147515 54522497513337899827721273)
  ·
    refine ⟨40891873135003424870790955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54522497513337899827721273 40891873135003424870790955)
    ·
      refine ⟨61337809702505137306186433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40891873135003424870790955 61337809702505137306186433)
      ·
        refine ⟨46003357276878852979639825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61337809702505137306186433 46003357276878852979639825)
        ·
          refine ⟨34502517957659139734729869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46003357276878852979639825 34502517957659139734729869)
          ·
            refine ⟨12938444234122177400523701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34502517957659139734729869 12938444234122177400523701)
            ·
              refine ⟨1212979146948954131299097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12938444234122177400523701 1212979146948954131299097)
              ·
                refine ⟨909734360211715598474323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212979146948954131299097 909734360211715598474323)
                ·
                  refine ⟨1364601540317573397711485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909734360211715598474323 1364601540317573397711485)
                  ·
                    refine ⟨511725577619090024141807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364601540317573397711485 511725577619090024141807)
                    ·
                      rfl

theorem cell22_1494873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 1, 3].length) (baseStart_1494873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494873 prefixEnd_1494873 := by exact prefixLift 1494873
  have htrace : WordTrace (prefixWord ++ tailWord_1494873) baseStart_1494873 baseEnd_1494873 := by
    simpa [prefixWord, tailWord_1494873, baseEnd_1494873] using wordTrace_append hprefix tailTrace_1494873
  have hstable : (prefixWord ++ tailWord_1494873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494873).length < 2 ^ (prefixWord ++ tailWord_1494873).sum := by decide
  have hdescent : baseEnd_1494873 < baseStart_1494873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494897 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 8]
def baseStart_1494897 : Nat := 118140960795 + 1494897 * 2 ^ 59
def prefixEnd_1494897 : Nat := 4983230072969 + 3 ^ 40 * 1494897 * 2
def baseEnd_1494897 : Nat := 170577931103187320513911

theorem tailTrace_1494897 : CollatzResearch.WordTrace tailWord_1494897 prefixEnd_1494897 170577931103187320513911 := by
  unfold tailWord_1494897
  simp only [CollatzResearch.WordTrace]
  refine ⟨54523372865250951926594945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36348915243500634617729963 54523372865250951926594945)
  ·
    refine ⟨40892529648938213944946209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54523372865250951926594945 40892529648938213944946209)
    ·
      refine ⟨30669397236703660458709657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40892529648938213944946209 30669397236703660458709657)
      ·
        refine ⟨23002047927527745344032243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30669397236703660458709657 23002047927527745344032243)
        ·
          refine ⟨34503071891291618016048365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23002047927527745344032243 34503071891291618016048365)
          ·
            refine ⟨12938651959234356756018137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34503071891291618016048365 12938651959234356756018137)
            ·
              refine ⟨9703988969425767567013603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12938651959234356756018137 9703988969425767567013603)
              ·
                refine ⟨14555983454138651350520405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9703988969425767567013603 14555983454138651350520405)
                ·
                  refine ⟨170577931103187320513911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14555983454138651350520405 170577931103187320513911)
                  ·
                    rfl

theorem cell22_1494897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_1494897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494897 prefixEnd_1494897 := by exact prefixLift 1494897
  have htrace : WordTrace (prefixWord ++ tailWord_1494897) baseStart_1494897 baseEnd_1494897 := by
    simpa [prefixWord, tailWord_1494897, baseEnd_1494897] using wordTrace_append hprefix tailTrace_1494897
  have hstable : (prefixWord ++ tailWord_1494897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494897).length < 2 ^ (prefixWord ++ tailWord_1494897).sum := by decide
  have hdescent : baseEnd_1494897 < baseStart_1494897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494929 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 4, 3]
def baseStart_1494929 : Nat := 118140960795 + 1494929 * 2 ^ 59
def prefixEnd_1494929 : Nat := 4983230072969 + 3 ^ 40 * 1494929 * 2
def baseEnd_1494929 : Nat := 511744747563524544741635

theorem tailTrace_1494929 : CollatzResearch.WordTrace tailWord_1494929 prefixEnd_1494929 511744747563524544741635 := by
  unfold tailWord_1494929
  simp only [CollatzResearch.WordTrace]
  refine ⟨54524540001135021391759841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36349693334090014261173227 54524540001135021391759841)
  ·
    refine ⟨40893405000851266043819881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54524540001135021391759841 40893405000851266043819881)
    ·
      refine ⟨30670053750638449532864911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40893405000851266043819881 30670053750638449532864911)
      ·
        refine ⟨46005080625957674299297367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30670053750638449532864911 46005080625957674299297367)
        ·
          refine ⟨69007620938936511448946051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46005080625957674299297367 69007620938936511448946051)
          ·
            refine ⟨103511431408404767173419077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69007620938936511448946051 103511431408404767173419077)
            ·
              refine ⟨19408393389075893845016077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103511431408404767173419077 19408393389075893845016077)
              ·
                refine ⟨7278147520903460191881029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19408393389075893845016077 7278147520903460191881029)
                ·
                  refine ⟨1364652660169398785977693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7278147520903460191881029 1364652660169398785977693)
                  ·
                    refine ⟨511744747563524544741635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364652660169398785977693 511744747563524544741635)
                    ·
                      rfl

theorem cell22_1494929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_1494929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494929 prefixEnd_1494929 := by exact prefixLift 1494929
  have htrace : WordTrace (prefixWord ++ tailWord_1494929) baseStart_1494929 baseEnd_1494929 := by
    simpa [prefixWord, tailWord_1494929, baseEnd_1494929] using wordTrace_append hprefix tailTrace_1494929
  have hstable : (prefixWord ++ tailWord_1494929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494929).length < 2 ^ (prefixWord ++ tailWord_1494929).sum := by decide
  have hdescent : baseEnd_1494929 < baseStart_1494929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494959 : List Nat := [1, 1, 2, 1, 2, 2, 7, 6]
def baseStart_1494959 : Nat := 118140960795 + 1494959 * 2 ^ 59
def prefixEnd_1494959 : Nat := 4983230072969 + 3 ^ 40 * 1494959 * 2
def baseEnd_1494959 : Nat := 56861668575179385165727

theorem tailTrace_1494959 : CollatzResearch.WordTrace tailWord_1494959 prefixEnd_1494959 56861668575179385165727 := by
  unfold tailWord_1494959
  simp only [CollatzResearch.WordTrace]
  refine ⟨54525634191026336515351931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36350422794017557676901287 54525634191026336515351931)
  ·
    refine ⟨81788451286539504773027897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54525634191026336515351931 81788451286539504773027897)
    ·
      refine ⟨61341338464904628579770923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81788451286539504773027897 61341338464904628579770923)
      ·
        refine ⟨92012007697356942869656385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61341338464904628579770923 92012007697356942869656385)
        ·
          refine ⟨69009005773017707152242289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92012007697356942869656385 69009005773017707152242289)
          ·
            refine ⟨51756754329763280364181717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69009005773017707152242289 51756754329763280364181717)
            ·
              refine ⟨1213048929603826883535509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51756754329763280364181717 1213048929603826883535509)
              ·
                refine ⟨56861668575179385165727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1213048929603826883535509 56861668575179385165727)
                ·
                  rfl

theorem cell22_1494959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 6].length) (baseStart_1494959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494959 prefixEnd_1494959 := by exact prefixLift 1494959
  have htrace : WordTrace (prefixWord ++ tailWord_1494959) baseStart_1494959 baseEnd_1494959 := by
    simpa [prefixWord, tailWord_1494959, baseEnd_1494959] using wordTrace_append hprefix tailTrace_1494959
  have hstable : (prefixWord ++ tailWord_1494959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494959).length < 2 ^ (prefixWord ++ tailWord_1494959).sum := by decide
  have hdescent : baseEnd_1494959 < baseStart_1494959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494961 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 2, 4]
def baseStart_1494961 : Nat := 118140960795 + 1494961 * 2 ^ 59
def prefixEnd_1494961 : Nat := 4983230072969 + 3 ^ 40 * 1494961 * 2
def baseEnd_1494961 : Nat := 511755701817487127941537

theorem tailTrace_1494961 : CollatzResearch.WordTrace tailWord_1494961 prefixEnd_1494961 511755701817487127941537 := by
  unfold tailWord_1494961
  simp only [CollatzResearch.WordTrace]
  refine ⟨54525707137019090856924737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36350471424679393904616491 54525707137019090856924737)
  ·
    refine ⟨40894280352764318142693553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54525707137019090856924737 40894280352764318142693553)
    ·
      refine ⟨30670710264573238607020165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40894280352764318142693553 30670710264573238607020165)
      ·
        refine ⟨5750758174607482238816281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30670710264573238607020165 5750758174607482238816281)
        ·
          refine ⟨4313068630955611679112211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5750758174607482238816281 4313068630955611679112211)
          ·
            refine ⟨6469602946433417518668317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313068630955611679112211 6469602946433417518668317)
            ·
              refine ⟨2426101104912531569500619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6469602946433417518668317 2426101104912531569500619)
              ·
                refine ⟨3639151657368797354250929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426101104912531569500619 3639151657368797354250929)
                ·
                  refine ⟨2729363743026598015688197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3639151657368797354250929 2729363743026598015688197)
                  ·
                    refine ⟨511755701817487127941537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729363743026598015688197 511755701817487127941537)
                    ·
                      rfl

theorem cell22_1494961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_1494961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494961 prefixEnd_1494961 := by exact prefixLift 1494961
  have htrace : WordTrace (prefixWord ++ tailWord_1494961) baseStart_1494961 baseEnd_1494961 := by
    simpa [prefixWord, tailWord_1494961, baseEnd_1494961] using wordTrace_append hprefix tailTrace_1494961
  have hstable : (prefixWord ++ tailWord_1494961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494961).length < 2 ^ (prefixWord ++ tailWord_1494961).sum := by decide
  have hdescent : baseEnd_1494961 < baseStart_1494961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494991 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 3, 3]
def baseStart_1494991 : Nat := 118140960795 + 1494991 * 2 ^ 59
def prefixEnd_1494991 : Nat := 4983230072969 + 3 ^ 40 * 1494991 * 2
def baseEnd_1494991 : Nat := 511765971430577049691445

theorem tailTrace_1494991 : CollatzResearch.WordTrace tailWord_1494991 prefixEnd_1494991 511765971430577049691445 := by
  unfold tailWord_1494991
  simp only [CollatzResearch.WordTrace]
  refine ⟨54526801326910405980516827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36351200884606937320344551 54526801326910405980516827)
  ·
    refine ⟨81790201990365608970775241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54526801326910405980516827 81790201990365608970775241)
    ·
      refine ⟨61342651492774206728081431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81790201990365608970775241 61342651492774206728081431)
      ·
        refine ⟨92013977239161310092122147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61342651492774206728081431 92013977239161310092122147)
        ·
          refine ⟨138020965858741965138183221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92013977239161310092122147 138020965858741965138183221)
          ·
            refine ⟨12939465549257059231704677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138020965858741965138183221 12939465549257059231704677)
            ·
              refine ⟨2426149790485698605944627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12939465549257059231704677 2426149790485698605944627)
              ·
                refine ⟨3639224685728547908916941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426149790485698605944627 3639224685728547908916941)
                ·
                  refine ⟨1364709257148205465843853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3639224685728547908916941 1364709257148205465843853)
                  ·
                    refine ⟨511765971430577049691445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364709257148205465843853 511765971430577049691445)
                    ·
                      rfl

theorem cell22_1494991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 3].length) (baseStart_1494991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1494991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1494991 prefixEnd_1494991 := by exact prefixLift 1494991
  have htrace : WordTrace (prefixWord ++ tailWord_1494991) baseStart_1494991 baseEnd_1494991 := by
    simpa [prefixWord, tailWord_1494991, baseEnd_1494991] using wordTrace_append hprefix tailTrace_1494991
  have hstable : (prefixWord ++ tailWord_1494991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494991).length < 2 ^ (prefixWord ++ tailWord_1494991).sum := by decide
  have hdescent : baseEnd_1494991 < baseStart_1494991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495010 : List Nat := [3, 3, 3, 1, 2, 2, 2, 6]
def baseStart_1495010 : Nat := 118140960795 + 1495010 * 2 ^ 59
def prefixEnd_1495010 : Nat := 4983230072969 + 3 ^ 40 * 1495010 * 2
def baseEnd_1495010 : Nat := 56863608390985259274043

theorem tailTrace_1495010 : CollatzResearch.WordTrace tailWord_1495010 prefixEnd_1495010 56863608390985259274043 := by
  unfold tailWord_1495010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13631873578460393056364621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36351662875894381483638989 13631873578460393056364621)
  ·
    refine ⟨5111952591922647396136733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13631873578460393056364621 5111952591922647396136733)
    ·
      refine ⟨1916982221970992773551275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5111952591922647396136733 1916982221970992773551275)
      ·
        refine ⟨2875473332956489160326913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916982221970992773551275 2875473332956489160326913)
        ·
          refine ⟨2156604999717366870245185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2875473332956489160326913 2156604999717366870245185)
          ·
            refine ⟨1617453749788025152683889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2156604999717366870245185 1617453749788025152683889)
            ·
              refine ⟨1213090312341018864512917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617453749788025152683889 1213090312341018864512917)
              ·
                refine ⟨56863608390985259274043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1213090312341018864512917 56863608390985259274043)
                ·
                  rfl

theorem cell22_1495010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_1495010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495010 prefixEnd_1495010 := by exact prefixLift 1495010
  have htrace : WordTrace (prefixWord ++ tailWord_1495010) baseStart_1495010 baseEnd_1495010 := by
    simpa [prefixWord, tailWord_1495010, baseEnd_1495010] using wordTrace_append hprefix tailTrace_1495010
  have hstable : (prefixWord ++ tailWord_1495010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495010).length < 2 ^ (prefixWord ++ tailWord_1495010).sum := by decide
  have hdescent : baseEnd_1495010 < baseStart_1495010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495034 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_1495034 : Nat := 118140960795 + 1495034 * 2 ^ 59
def prefixEnd_1495034 : Nat := 4983230072969 + 3 ^ 40 * 1495034 * 2
def baseEnd_1495034 : Nat := 511780691209339270866313

theorem tailTrace_1495034 : CollatzResearch.WordTrace tailWord_1495034 prefixEnd_1495034 511780691209339270866313 := by
  unfold tailWord_1495034
  simp only [CollatzResearch.WordTrace]
  refine ⟨13632092416438656081083039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36352246443836416216221437 13632092416438656081083039)
  ·
    refine ⟨20448138624657984121624559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13632092416438656081083039 20448138624657984121624559)
    ·
      refine ⟨30672207936986976182436839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20448138624657984121624559 30672207936986976182436839)
      ·
        refine ⟨46008311905480464273655259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30672207936986976182436839 46008311905480464273655259)
        ·
          refine ⟨69012467858220696410482889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46008311905480464273655259 69012467858220696410482889)
          ·
            refine ⟨51759350893665522307862167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69012467858220696410482889 51759350893665522307862167)
            ·
              refine ⟨77639026340498283461793251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51759350893665522307862167 77639026340498283461793251)
              ·
                refine ⟨116458539510747425192689877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77639026340498283461793251 116458539510747425192689877)
                ·
                  refine ⟨2729497019783142777953669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 116458539510747425192689877 2729497019783142777953669)
                  ·
                    refine ⟨511780691209339270866313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729497019783142777953669 511780691209339270866313)
                    ·
                      rfl

theorem cell22_1495034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_1495034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495034 prefixEnd_1495034 := by exact prefixLift 1495034
  have htrace : WordTrace (prefixWord ++ tailWord_1495034) baseStart_1495034 baseEnd_1495034 := by
    simpa [prefixWord, tailWord_1495034, baseEnd_1495034] using wordTrace_append hprefix tailTrace_1495034
  have hstable : (prefixWord ++ tailWord_1495034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495034).length < 2 ^ (prefixWord ++ tailWord_1495034).sum := by decide
  have hdescent : baseEnd_1495034 < baseStart_1495034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495068 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1495068 : Nat := 118140960795 + 1495068 * 2 ^ 59
def prefixEnd_1495068 : Nat := 4983230072969 + 3 ^ 40 * 1495068 * 2
def baseEnd_1495068 : Nat := 511792330104174515516209

theorem tailTrace_1495068 : CollatzResearch.WordTrace tailWord_1495068 prefixEnd_1495068 511792330104174515516209 := by
  unfold tailWord_1495068
  simp only [CollatzResearch.WordTrace]
  refine ⟨27264804873815724065534929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36353073165087632087379905 27264804873815724065534929)
  ·
    refine ⟨20448603655361793049151197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27264804873815724065534929 20448603655361793049151197)
    ·
      refine ⟨7668226370760672393431699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20448603655361793049151197 7668226370760672393431699)
      ·
        refine ⟨11502339556141008590147549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7668226370760672393431699 11502339556141008590147549)
        ·
          refine ⟨4313377333552878221305331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11502339556141008590147549 4313377333552878221305331)
          ·
            refine ⟨6470066000329317331957997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313377333552878221305331 6470066000329317331957997)
            ·
              refine ⟨2426274750123493999484249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6470066000329317331957997 2426274750123493999484249)
              ·
                refine ⟨1819706062592620499613187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426274750123493999484249 1819706062592620499613187)
                ·
                  refine ⟨2729559093888930749419781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819706062592620499613187 2729559093888930749419781)
                  ·
                    refine ⟨511792330104174515516209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729559093888930749419781 511792330104174515516209)
                    ·
                      rfl

theorem cell22_1495068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1495068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495068 prefixEnd_1495068 := by exact prefixLift 1495068
  have htrace : WordTrace (prefixWord ++ tailWord_1495068) baseStart_1495068 baseEnd_1495068 := by
    simpa [prefixWord, tailWord_1495068, baseEnd_1495068] using wordTrace_append hprefix tailTrace_1495068
  have hstable : (prefixWord ++ tailWord_1495068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495068).length < 2 ^ (prefixWord ++ tailWord_1495068).sum := by decide
  have hdescent : baseEnd_1495068 < baseStart_1495068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495109 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_1495109 : Nat := 118140960795 + 1495109 * 2 ^ 59
def prefixEnd_1495109 : Nat := 4983230072969 + 3 ^ 40 * 1495109 * 2
def baseEnd_1495109 : Nat := 511806365242064075241083

theorem tailTrace_1495109 : CollatzResearch.WordTrace tailWord_1495109 prefixEnd_1495109 511806365242064075241083 := by
  unfold tailWord_1495109
  simp only [CollatzResearch.WordTrace]
  refine ⟨54531105140482912133312381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36354070093655274755541587 54531105140482912133312381)
  ·
    refine ⟨20449164427681092049992143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54531105140482912133312381 20449164427681092049992143)
    ·
      refine ⟨30673746641521638074988215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20449164427681092049992143 30673746641521638074988215)
      ·
        refine ⟨46010619962282457112482323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30673746641521638074988215 46010619962282457112482323)
        ·
          refine ⟨69015929943423685668723485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46010619962282457112482323 69015929943423685668723485)
          ·
            refine ⟨25880973728783882125771307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69015929943423685668723485 25880973728783882125771307)
            ·
              refine ⟨38821460593175823188656961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25880973728783882125771307 38821460593175823188656961)
              ·
                refine ⟨29116095444881867391492721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38821460593175823188656961 29116095444881867391492721)
                ·
                  refine ⟨21837071583661400543619541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29116095444881867391492721 21837071583661400543619541)
                  ·
                    refine ⟨511806365242064075241083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21837071583661400543619541 511806365242064075241083)
                    ·
                      rfl

theorem cell22_1495109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_1495109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495109 prefixEnd_1495109 := by exact prefixLift 1495109
  have htrace : WordTrace (prefixWord ++ tailWord_1495109) baseStart_1495109 baseEnd_1495109 := by
    simpa [prefixWord, tailWord_1495109, baseEnd_1495109] using wordTrace_append hprefix tailTrace_1495109
  have hstable : (prefixWord ++ tailWord_1495109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495109).length < 2 ^ (prefixWord ++ tailWord_1495109).sum := by decide
  have hdescent : baseEnd_1495109 < baseStart_1495109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495134 : List Nat := [4, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1495134 : Nat := 118140960795 + 1495134 * 2 ^ 59
def prefixEnd_1495134 : Nat := 4983230072969 + 3 ^ 40 * 1495134 * 2
def baseEnd_1495134 : Nat := 170604974417657447788669

theorem tailTrace_1495134 : CollatzResearch.WordTrace tailWord_1495134 prefixEnd_1495134 170604974417657447788669 := by
  unfold tailWord_1495134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816502120674042675371557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36354677976928227601981637 6816502120674042675371557)
  ·
    refine ⟨1278094147626383001632167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6816502120674042675371557 1278094147626383001632167)
    ·
      refine ⟨1917141221439574502448251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1278094147626383001632167 1917141221439574502448251)
      ·
        refine ⟨2875711832159361753672377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1917141221439574502448251 2875711832159361753672377)
        ·
          refine ⟨2156783874119521315254283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2875711832159361753672377 2156783874119521315254283)
          ·
            refine ⟨3235175811179281972881425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156783874119521315254283 3235175811179281972881425)
            ·
              refine ⟨2426381858384461479661069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3235175811179281972881425 2426381858384461479661069)
              ·
                refine ⟨909893196894173054872901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2426381858384461479661069 909893196894173054872901)
                ·
                  refine ⟨170604974417657447788669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909893196894173054872901 170604974417657447788669)
                  ·
                    rfl

theorem cell22_1495134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1495134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495134 prefixEnd_1495134 := by exact prefixLift 1495134
  have htrace : WordTrace (prefixWord ++ tailWord_1495134) baseStart_1495134 baseEnd_1495134 := by
    simpa [prefixWord, tailWord_1495134, baseEnd_1495134] using wordTrace_append hprefix tailTrace_1495134
  have hstable : (prefixWord ++ tailWord_1495134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495134).length < 2 ^ (prefixWord ++ tailWord_1495134).sum := by decide
  have hdescent : baseEnd_1495134 < baseStart_1495134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495171 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 2, 5]
def baseStart_1495171 : Nat := 118140960795 + 1495171 * 2 ^ 59
def prefixEnd_1495171 : Nat := 4983230072969 + 3 ^ 40 * 1495171 * 2
def baseEnd_1495171 : Nat := 511827589109116580190893

theorem tailTrace_1495171 : CollatzResearch.WordTrace tailWord_1495171 prefixEnd_1495171 511827589109116580190893 := by
  unfold tailWord_1495171
  simp only [CollatzResearch.WordTrace]
  refine ⟨54533366466258296722069367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36355577644172197814712911 54533366466258296722069367)
  ·
    refine ⟨81800049699387445083104051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54533366466258296722069367 81800049699387445083104051)
    ·
      refine ⟨122700074549081167624656077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81800049699387445083104051 122700074549081167624656077)
      ·
        refine ⟨46012527955905437859246029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122700074549081167624656077 46012527955905437859246029)
        ·
          refine ⟨17254697983464539197217261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46012527955905437859246029 17254697983464539197217261)
          ·
            refine ⟨6470511743799202198956473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17254697983464539197217261 6470511743799202198956473)
            ·
              refine ⟨4852883807849401649217355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6470511743799202198956473 4852883807849401649217355)
              ·
                refine ⟨7279325711774102473826033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852883807849401649217355 7279325711774102473826033)
                ·
                  refine ⟨5459494283830576855369525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7279325711774102473826033 5459494283830576855369525)
                  ·
                    refine ⟨511827589109116580190893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5459494283830576855369525 511827589109116580190893)
                    ·
                      rfl

theorem cell22_1495171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 5].length) (baseStart_1495171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495171 prefixEnd_1495171 := by exact prefixLift 1495171
  have htrace : WordTrace (prefixWord ++ tailWord_1495171) baseStart_1495171 baseEnd_1495171 := by
    simpa [prefixWord, tailWord_1495171, baseEnd_1495171] using wordTrace_append hprefix tailTrace_1495171
  have hstable : (prefixWord ++ tailWord_1495171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495171).length < 2 ^ (prefixWord ++ tailWord_1495171).sum := by decide
  have hdescent : baseEnd_1495171 < baseStart_1495171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495194 : List Nat := [3, 1, 1, 5, 2, 2, 1, 3, 1, 3]
def baseStart_1495194 : Nat := 118140960795 + 1495194 * 2 ^ 59
def prefixEnd_1495194 : Nat := 4983230072969 + 3 ^ 40 * 1495194 * 2
def baseEnd_1495194 : Nat := 511835462479152186865823

theorem tailTrace_1495194 : CollatzResearch.WordTrace tailWord_1495194 prefixEnd_1495194 511835462479152186865823 := by
  unfold tailWord_1495194
  simp only [CollatzResearch.WordTrace]
  refine ⟨13633551336293742912539159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36356136896783314433437757 13633551336293742912539159)
  ·
    refine ⟨20450327004440614368808739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13633551336293742912539159 20450327004440614368808739)
    ·
      refine ⟨30675490506660921553213109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20450327004440614368808739 30675490506660921553213109)
      ·
        refine ⟨2875827234999461395613729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30675490506660921553213109 2875827234999461395613729)
        ·
          refine ⟨2156870426249596046710297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2875827234999461395613729 2156870426249596046710297)
          ·
            refine ⟨1617652819687197035032723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2156870426249596046710297 1617652819687197035032723)
            ·
              refine ⟨2426479229530795552549085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617652819687197035032723 2426479229530795552549085)
              ·
                refine ⟨909929711074048332205907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2426479229530795552549085 909929711074048332205907)
                ·
                  refine ⟨1364894566611072498308861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909929711074048332205907 1364894566611072498308861)
                  ·
                    refine ⟨511835462479152186865823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364894566611072498308861 511835462479152186865823)
                    ·
                      rfl

theorem cell22_1495194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_1495194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495194 prefixEnd_1495194 := by exact prefixLift 1495194
  have htrace : WordTrace (prefixWord ++ tailWord_1495194) baseStart_1495194 baseEnd_1495194 := by
    simpa [prefixWord, tailWord_1495194, baseEnd_1495194] using wordTrace_append hprefix tailTrace_1495194
  have hstable : (prefixWord ++ tailWord_1495194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495194).length < 2 ^ (prefixWord ++ tailWord_1495194).sum := by decide
  have hdescent : baseEnd_1495194 < baseStart_1495194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495231 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 6, 4]
def baseStart_1495231 : Nat := 118140960795 + 1495231 * 2 ^ 59
def prefixEnd_1495231 : Nat := 4983230072969 + 3 ^ 40 * 1495231 * 2
def baseEnd_1495231 : Nat := 511848128335296423690709

theorem tailTrace_1495231 : CollatzResearch.WordTrace tailWord_1495231 prefixEnd_1495231 511848128335296423690709 := by
  unfold tailWord_1495231
  simp only [CollatzResearch.WordTrace]
  refine ⟨54535554846040926969253547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36357036564027284646169031 54535554846040926969253547)
  ·
    refine ⟨81803332269061390453880321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54535554846040926969253547 81803332269061390453880321)
    ·
      refine ⟨61352499201796042840410241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81803332269061390453880321 61352499201796042840410241)
      ·
        refine ⟨46014374401347032130307681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61352499201796042840410241 46014374401347032130307681)
        ·
          refine ⟨34510780801010274097730761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46014374401347032130307681 34510780801010274097730761)
          ·
            refine ⟨25883085600757705573298071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34510780801010274097730761 25883085600757705573298071)
            ·
              refine ⟨38824628401136558359947107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25883085600757705573298071 38824628401136558359947107)
              ·
                refine ⟨58236942601704837539920661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38824628401136558359947107 58236942601704837539920661)
                ·
                  refine ⟨2729856684454914259683781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58236942601704837539920661 2729856684454914259683781)
                  ·
                    refine ⟨511848128335296423690709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729856684454914259683781 511848128335296423690709)
                    ·
                      rfl

theorem cell22_1495231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_1495231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495231 prefixEnd_1495231 := by exact prefixLift 1495231
  have htrace : WordTrace (prefixWord ++ tailWord_1495231) baseStart_1495231 baseEnd_1495231 := by
    simpa [prefixWord, tailWord_1495231, baseEnd_1495231] using wordTrace_append hprefix tailTrace_1495231
  have hstable : (prefixWord ++ tailWord_1495231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495231).length < 2 ^ (prefixWord ++ tailWord_1495231).sum := by decide
  have hdescent : baseEnd_1495231 < baseStart_1495231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495254 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1495254 : Nat := 118140960795 + 1495254 * 2 ^ 59
def prefixEnd_1495254 : Nat := 4983230072969 + 3 ^ 40 * 1495254 * 2
def baseEnd_1495254 : Nat := 511856001705332030365639

theorem tailTrace_1495254 : CollatzResearch.WordTrace tailWord_1495254 prefixEnd_1495254 511856001705332030365639 := by
  unfold tailWord_1495254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3408524607809850118583801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36357595816638401264893877 3408524607809850118583801)
  ·
    refine ⟨2556393455857387588937851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3408524607809850118583801 2556393455857387588937851)
    ·
      refine ⟨3834590183786081383406777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2556393455857387588937851 3834590183786081383406777)
      ·
        refine ⟨2875942637839561037555083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3834590183786081383406777 2875942637839561037555083)
        ·
          refine ⟨4313913956759341556332625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2875942637839561037555083 4313913956759341556332625)
          ·
            refine ⟨3235435467569506167249469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4313913956759341556332625 3235435467569506167249469)
            ·
              refine ⟨1213288300338564812718551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3235435467569506167249469 1213288300338564812718551)
              ·
                refine ⟨1819932450507847219077827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213288300338564812718551 1819932450507847219077827)
                ·
                  refine ⟨2729898675761770828616741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819932450507847219077827 2729898675761770828616741)
                  ·
                    refine ⟨511856001705332030365639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729898675761770828616741 511856001705332030365639)
                    ·
                      rfl

theorem cell22_1495254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1495254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495254 prefixEnd_1495254 := by exact prefixLift 1495254
  have htrace : WordTrace (prefixWord ++ tailWord_1495254) baseStart_1495254 baseEnd_1495254 := by
    simpa [prefixWord, tailWord_1495254, baseEnd_1495254] using wordTrace_append hprefix tailTrace_1495254
  have hstable : (prefixWord ++ tailWord_1495254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495254).length < 2 ^ (prefixWord ++ tailWord_1495254).sum := by decide
  have hdescent : baseEnd_1495254 < baseStart_1495254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495276 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_1495276 : Nat := 118140960795 + 1495276 * 2 ^ 59
def prefixEnd_1495276 : Nat := 4983230072969 + 3 ^ 40 * 1495276 * 2
def baseEnd_1495276 : Nat := 511863532754931306315571

theorem tailTrace_1495276 : CollatzResearch.WordTrace tailWord_1495276 prefixEnd_1495276 511863532754931306315571 := by
  unfold tailWord_1495276
  simp only [CollatzResearch.WordTrace]
  refine ⟨27268598065438949827320841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36358130753918599769761121 27268598065438949827320841)
  ·
    refine ⟨20451448549079212370490631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27268598065438949827320841 20451448549079212370490631)
    ·
      refine ⟨30677172823618818555735947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20451448549079212370490631 30677172823618818555735947)
      ·
        refine ⟨46015759235428227833603921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30677172823618818555735947 46015759235428227833603921)
        ·
          refine ⟨34511819426571170875202941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46015759235428227833603921 34511819426571170875202941)
          ·
            refine ⟨12941932284964189078201103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34511819426571170875202941 12941932284964189078201103)
            ·
              refine ⟨19412898427446283617301655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12941932284964189078201103 19412898427446283617301655)
              ·
                refine ⟨29119347641169425425952483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19412898427446283617301655 29119347641169425425952483)
                ·
                  refine ⟨43679021461754138138928725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29119347641169425425952483 43679021461754138138928725)
                  ·
                    refine ⟨511863532754931306315571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43679021461754138138928725 511863532754931306315571)
                    ·
                      rfl

theorem cell22_1495276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_1495276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495276 prefixEnd_1495276 := by exact prefixLift 1495276
  have htrace : WordTrace (prefixWord ++ tailWord_1495276) baseStart_1495276 baseEnd_1495276 := by
    simpa [prefixWord, tailWord_1495276, baseEnd_1495276] using wordTrace_append hprefix tailTrace_1495276
  have hstable : (prefixWord ++ tailWord_1495276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495276).length < 2 ^ (prefixWord ++ tailWord_1495276).sum := by decide
  have hdescent : baseEnd_1495276 < baseStart_1495276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495325 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 7]
def baseStart_1495325 : Nat := 118140960795 + 1495325 * 2 ^ 59
def prefixEnd_1495325 : Nat := 4983230072969 + 3 ^ 40 * 1495325 * 2
def baseEnd_1495325 : Nat := 170626768818770503946807

theorem tailTrace_1495325 : CollatzResearch.WordTrace tailWord_1495325 prefixEnd_1495325 170626768818770503946807 := by
  unfold tailWord_1495325
  simp only [CollatzResearch.WordTrace]
  refine ⟨54538983307700381023175429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36359322205133587348783619 54538983307700381023175429)
  ·
    refine ⟨10226059370193821441845393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54538983307700381023175429 10226059370193821441845393)
    ·
      refine ⟨7669544527645366081384045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10226059370193821441845393 7669544527645366081384045)
      ·
        refine ⟨2876079197867012280519017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7669544527645366081384045 2876079197867012280519017)
        ·
          refine ⟨2157059398400259210389263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2876079197867012280519017 2157059398400259210389263)
          ·
            refine ⟨3235589097600388815583895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157059398400259210389263 3235589097600388815583895)
            ·
              refine ⟨4853383646400583223375843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235589097600388815583895 4853383646400583223375843)
              ·
                refine ⟨7280075469600874835063765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853383646400583223375843 7280075469600874835063765)
                ·
                  refine ⟨170626768818770503946807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7280075469600874835063765 170626768818770503946807)
                  ·
                    rfl

theorem cell22_1495325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_1495325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495325 prefixEnd_1495325 := by exact prefixLift 1495325
  have htrace : WordTrace (prefixWord ++ tailWord_1495325) baseStart_1495325 baseEnd_1495325 := by
    simpa [prefixWord, tailWord_1495325, baseEnd_1495325] using wordTrace_append hprefix tailTrace_1495325
  have hstable : (prefixWord ++ tailWord_1495325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495325).length < 2 ^ (prefixWord ++ tailWord_1495325).sum := by decide
  have hdescent : baseEnd_1495325 < baseStart_1495325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495368 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_1495368 : Nat := 118140960795 + 1495368 * 2 ^ 59
def prefixEnd_1495368 : Nat := 4983230072969 + 3 ^ 40 * 1495368 * 2
def baseEnd_1495368 : Nat := 511895026235073733015289

theorem tailTrace_1495368 : CollatzResearch.WordTrace tailWord_1495368 prefixEnd_1495368 511895026235073733015289 := by
  unfold tailWord_1495368
  simp only [CollatzResearch.WordTrace]
  refine ⟨27270275823272299683495379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36360367764363066244660505 27270275823272299683495379)
  ·
    refine ⟨40905413734908449525243069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27270275823272299683495379 40905413734908449525243069)
    ·
      refine ⟨15339530150590668571966151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40905413734908449525243069 15339530150590668571966151)
      ·
        refine ⟨23009295225886002857949227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15339530150590668571966151 23009295225886002857949227)
        ·
          refine ⟨34513942838829004286923841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23009295225886002857949227 34513942838829004286923841)
          ·
            refine ⟨25885457129121753215192881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34513942838829004286923841 25885457129121753215192881)
            ·
              refine ⟨19414092846841314911394661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25885457129121753215192881 19414092846841314911394661)
              ·
                refine ⟨3640142408782746545886499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19414092846841314911394661 3640142408782746545886499)
                ·
                  refine ⟨5460213613174119818829749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640142408782746545886499 5460213613174119818829749)
                  ·
                    refine ⟨511895026235073733015289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5460213613174119818829749 511895026235073733015289)
                    ·
                      rfl

theorem cell22_1495368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_1495368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495368 prefixEnd_1495368 := by exact prefixLift 1495368
  have htrace : WordTrace (prefixWord ++ tailWord_1495368) baseStart_1495368 baseEnd_1495368 := by
    simpa [prefixWord, tailWord_1495368, baseEnd_1495368] using wordTrace_append hprefix tailTrace_1495368
  have hstable : (prefixWord ++ tailWord_1495368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495368).length < 2 ^ (prefixWord ++ tailWord_1495368).sum := by decide
  have hdescent : baseEnd_1495368 < baseStart_1495368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495385 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 2, 3]
def baseStart_1495385 : Nat := 118140960795 + 1495385 * 2 ^ 59
def prefixEnd_1495385 : Nat := 4983230072969 + 3 ^ 40 * 1495385 * 2
def baseEnd_1495385 : Nat := 511900845682491355340237

theorem tailTrace_1495385 : CollatzResearch.WordTrace tailWord_1495385 prefixEnd_1495385 511900845682491355340237 := by
  unfold tailWord_1495385
  simp only [CollatzResearch.WordTrace]
  refine ⟨54541171687483011270359609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36360781124988674180239739 54541171687483011270359609)
  ·
    refine ⟨40905878765612258452769707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54541171687483011270359609 40905878765612258452769707)
    ·
      refine ⟨61358818148418387679154561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40905878765612258452769707 61358818148418387679154561)
      ·
        refine ⟨46019113611313790759365921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61358818148418387679154561 46019113611313790759365921)
        ·
          refine ⟨34514335208485343069524441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46019113611313790759365921 34514335208485343069524441)
          ·
            refine ⟨25885751406364007302143331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34514335208485343069524441 25885751406364007302143331)
            ·
              refine ⟨38828627109546010953214997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25885751406364007302143331 38828627109546010953214997)
              ·
                refine ⟨1820091895759969263431953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38828627109546010953214997 1820091895759969263431953)
                ·
                  refine ⟨1365068921819976947573965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1820091895759969263431953 1365068921819976947573965)
                  ·
                    refine ⟨511900845682491355340237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1365068921819976947573965 511900845682491355340237)
                    ·
                      rfl

theorem cell22_1495385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 3].length) (baseStart_1495385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495385 prefixEnd_1495385 := by exact prefixLift 1495385
  have htrace : WordTrace (prefixWord ++ tailWord_1495385) baseStart_1495385 baseEnd_1495385 := by
    simpa [prefixWord, tailWord_1495385, baseEnd_1495385] using wordTrace_append hprefix tailTrace_1495385
  have hstable : (prefixWord ++ tailWord_1495385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495385).length < 2 ^ (prefixWord ++ tailWord_1495385).sum := by decide
  have hdescent : baseEnd_1495385 < baseStart_1495385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495460 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 5]
def baseStart_1495460 : Nat := 118140960795 + 1495460 * 2 ^ 59
def prefixEnd_1495460 : Nat := 4983230072969 + 3 ^ 40 * 1495460 * 2
def baseEnd_1495460 : Nat := 170642173238405386571669

theorem tailTrace_1495460 : CollatzResearch.WordTrace tailWord_1495460 prefixEnd_1495460 170642173238405386571669 := by
  unfold tailWord_1495460
  simp only [CollatzResearch.WordTrace]
  refine ⟨27271953581105649539669917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36362604774807532719559889 27271953581105649539669917)
  ·
    refine ⟨10226982592914618577376219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27271953581105649539669917 10226982592914618577376219)
    ·
      refine ⟨15340473889371927866064329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10226982592914618577376219 15340473889371927866064329)
      ·
        refine ⟨11505355417028945899548247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15340473889371927866064329 11505355417028945899548247)
        ·
          refine ⟨17258033125543418849322371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11505355417028945899548247 17258033125543418849322371)
          ·
            refine ⟨25887049688315128273983557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17258033125543418849322371 25887049688315128273983557)
            ·
              refine ⟨4853821816559086551371917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25887049688315128273983557 4853821816559086551371917)
              ·
                refine ⟨1820183181209657456764469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4853821816559086551371917 1820183181209657456764469)
                ·
                  refine ⟨170642173238405386571669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1820183181209657456764469 170642173238405386571669)
                  ·
                    rfl

theorem cell22_1495460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_1495460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495460 prefixEnd_1495460 := by exact prefixLift 1495460
  have htrace : WordTrace (prefixWord ++ tailWord_1495460) baseStart_1495460 baseEnd_1495460 := by
    simpa [prefixWord, tailWord_1495460, baseEnd_1495460] using wordTrace_append hprefix tailTrace_1495460
  have hstable : (prefixWord ++ tailWord_1495460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495460).length < 2 ^ (prefixWord ++ tailWord_1495460).sum := by decide
  have hdescent : baseEnd_1495460 < baseStart_1495460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495464 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1495464 : Nat := 118140960795 + 1495464 * 2 ^ 59
def prefixEnd_1495464 : Nat := 4983230072969 + 3 ^ 40 * 1495464 * 2
def baseEnd_1495464 : Nat := 511927888996961482614995

theorem tailTrace_1495464 : CollatzResearch.WordTrace tailWord_1495464 prefixEnd_1495464 511927888996961482614995 := by
  unfold tailWord_1495464
  simp only [CollatzResearch.WordTrace]
  refine ⟨27272026527098403881242723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36362702036131205174990297 27272026527098403881242723)
  ·
    refine ⟨40908039790647605821864085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27272026527098403881242723 40908039790647605821864085)
    ·
      refine ⟨1917564365186606522899879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40908039790647605821864085 1917564365186606522899879)
      ·
        refine ⟨2876346547779909784349819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1917564365186606522899879 2876346547779909784349819)
        ·
          refine ⟨4314519821669864676524729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2876346547779909784349819 4314519821669864676524729)
          ·
            refine ⟨3235889866252398507393547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4314519821669864676524729 3235889866252398507393547)
            ·
              refine ⟨4853834799378597761090321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235889866252398507393547 4853834799378597761090321)
              ·
                refine ⟨3640376099533948320817741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4853834799378597761090321 3640376099533948320817741)
                ·
                  refine ⟨1365141037325230620306653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3640376099533948320817741 1365141037325230620306653)
                  ·
                    refine ⟨511927888996961482614995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1365141037325230620306653 511927888996961482614995)
                    ·
                      rfl

theorem cell22_1495464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1495464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495464 prefixEnd_1495464 := by exact prefixLift 1495464
  have htrace : WordTrace (prefixWord ++ tailWord_1495464) baseStart_1495464 baseEnd_1495464 := by
    simpa [prefixWord, tailWord_1495464, baseEnd_1495464] using wordTrace_append hprefix tailTrace_1495464
  have hstable : (prefixWord ++ tailWord_1495464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495464).length < 2 ^ (prefixWord ++ tailWord_1495464).sum := by decide
  have hdescent : baseEnd_1495464 < baseStart_1495464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495466 : List Nat := [3, 1, 6, 1, 1, 1, 3, 6]
def baseStart_1495466 : Nat := 118140960795 + 1495466 * 2 ^ 59
def prefixEnd_1495466 : Nat := 4983230072969 + 3 ^ 40 * 1495466 * 2
def baseEnd_1495466 : Nat := 56880952626426016007221

theorem tailTrace_1495466 : CollatzResearch.WordTrace tailWord_1495466 prefixEnd_1495466 56880952626426016007221 := by
  unfold tailWord_1495466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636031500047390526014563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36362750666793041402705501 13636031500047390526014563)
  ·
    refine ⟨20454047250071085789021845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13636031500047390526014563 20454047250071085789021845)
    ·
      refine ⟨958783464847082146360399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20454047250071085789021845 958783464847082146360399)
      ·
        refine ⟨1438175197270623219540599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958783464847082146360399 1438175197270623219540599)
        ·
          refine ⟨2157262795905934829310899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438175197270623219540599 2157262795905934829310899)
          ·
            refine ⟨3235894193858902243966349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157262795905934829310899 3235894193858902243966349)
            ·
              refine ⟨1213460322697088341487381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3235894193858902243966349 1213460322697088341487381)
              ·
                refine ⟨56880952626426016007221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1213460322697088341487381 56880952626426016007221)
                ·
                  rfl

theorem cell22_1495466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_1495466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495466 prefixEnd_1495466 := by exact prefixLift 1495466
  have htrace : WordTrace (prefixWord ++ tailWord_1495466) baseStart_1495466 baseEnd_1495466 := by
    simpa [prefixWord, tailWord_1495466, baseEnd_1495466] using wordTrace_append hprefix tailTrace_1495466
  have hstable : (prefixWord ++ tailWord_1495466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495466).length < 2 ^ (prefixWord ++ tailWord_1495466).sum := by decide
  have hdescent : baseEnd_1495466 < baseStart_1495466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495488 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 10]
def baseStart_1495488 : Nat := 118140960795 + 1495488 * 2 ^ 59
def prefixEnd_1495488 : Nat := 4983230072969 + 3 ^ 40 * 1495488 * 2
def baseEnd_1495488 : Nat := 170645368229144473338307

theorem tailTrace_1495488 : CollatzResearch.WordTrace tailWord_1495488 prefixEnd_1495488 170645368229144473338307 := by
  unfold tailWord_1495488
  simp only [CollatzResearch.WordTrace]
  refine ⟨27272464203054929930679559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36363285604073239907572745 27272464203054929930679559)
  ·
    refine ⟨40908696304582394896019339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27272464203054929930679559 40908696304582394896019339)
    ·
      refine ⟨61363044456873592344029009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40908696304582394896019339 61363044456873592344029009)
      ·
        refine ⟨46022283342655194258021757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61363044456873592344029009 46022283342655194258021757)
        ·
          refine ⟨17258356253495697846758159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46022283342655194258021757 17258356253495697846758159)
          ·
            refine ⟨25887534380243546770137239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17258356253495697846758159 25887534380243546770137239)
            ·
              refine ⟨38831301570365320155205859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25887534380243546770137239 38831301570365320155205859)
              ·
                refine ⟨58246952355547980232808789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38831301570365320155205859 58246952355547980232808789)
                ·
                  refine ⟨170645368229144473338307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 58246952355547980232808789 170645368229144473338307)
                  ·
                    rfl

theorem cell22_1495488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_1495488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495488 prefixEnd_1495488 := by exact prefixLift 1495488
  have htrace : WordTrace (prefixWord ++ tailWord_1495488) baseStart_1495488 baseEnd_1495488 := by
    simpa [prefixWord, tailWord_1495488, baseEnd_1495488] using wordTrace_append hprefix tailTrace_1495488
  have hstable : (prefixWord ++ tailWord_1495488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495488).length < 2 ^ (prefixWord ++ tailWord_1495488).sum := by decide
  have hdescent : baseEnd_1495488 < baseStart_1495488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495535 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 2, 4]
def baseStart_1495535 : Nat := 118140960795 + 1495535 * 2 ^ 59
def prefixEnd_1495535 : Nat := 4983230072969 + 3 ^ 40 * 1495535 * 2
def baseEnd_1495535 : Nat := 511952193747940964089777

theorem tailTrace_1495535 : CollatzResearch.WordTrace tailWord_1495535 prefixEnd_1495535 511952193747940964089777 := by
  unfold tailWord_1495535
  simp only [CollatzResearch.WordTrace]
  refine ⟨54546642636939586888320059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36364428424626391258880039 54546642636939586888320059)
  ·
    refine ⟨81819963955409380332480089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54546642636939586888320059 81819963955409380332480089)
    ·
      refine ⟨61364972966557035249360067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81819963955409380332480089 61364972966557035249360067)
      ·
        refine ⟨92047459449835552874040101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61364972966557035249360067 92047459449835552874040101)
        ·
          refine ⟨17258898646844166163882519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92047459449835552874040101 17258898646844166163882519)
          ·
            refine ⟨25888347970266249245823779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17258898646844166163882519 25888347970266249245823779)
            ·
              refine ⟨38832521955399373868735669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25888347970266249245823779 38832521955399373868735669)
              ·
                refine ⟨3640548933318691300193969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38832521955399373868735669 3640548933318691300193969)
                ·
                  refine ⟨2730411699989018475145477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3640548933318691300193969 2730411699989018475145477)
                  ·
                    refine ⟨511952193747940964089777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2730411699989018475145477 511952193747940964089777)
                    ·
                      rfl

theorem cell22_1495535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_1495535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495535 prefixEnd_1495535 := by exact prefixLift 1495535
  have htrace : WordTrace (prefixWord ++ tailWord_1495535) baseStart_1495535 baseEnd_1495535 := by
    simpa [prefixWord, tailWord_1495535, baseEnd_1495535] using wordTrace_append hprefix tailTrace_1495535
  have hstable : (prefixWord ++ tailWord_1495535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495535).length < 2 ^ (prefixWord ++ tailWord_1495535).sum := by decide
  have hdescent : baseEnd_1495535 < baseStart_1495535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495556 : List Nat := [2, 3, 2, 3, 1, 2, 3, 2, 4]
def baseStart_1495556 : Nat := 118140960795 + 1495556 * 2 ^ 59
def prefixEnd_1495556 : Nat := 4983230072969 + 3 ^ 40 * 1495556 * 2
def baseEnd_1495556 : Nat := 170653127492367969771571

theorem tailTrace_1495556 : CollatzResearch.WordTrace tailWord_1495556 prefixEnd_1495556 170653127492367969771571 := by
  unfold tailWord_1495556
  simp only [CollatzResearch.WordTrace]
  refine ⟨27273704284931753737417261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36364939046575671649889681 27273704284931753737417261)
  ·
    refine ⟨10227639106849407651531473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27273704284931753737417261 10227639106849407651531473)
    ·
      refine ⟨7670729330137055738648605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10227639106849407651531473 7670729330137055738648605)
      ·
        refine ⟨2876523498801395901993227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7670729330137055738648605 2876523498801395901993227)
        ·
          refine ⟨4314785248202093852989841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2876523498801395901993227 4314785248202093852989841)
          ·
            refine ⟨3236088936151570389742381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4314785248202093852989841 3236088936151570389742381)
            ·
              refine ⟨1213533351056838896153393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3236088936151570389742381 1213533351056838896153393)
              ·
                refine ⟨910150013292629172115045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213533351056838896153393 910150013292629172115045)
                ·
                  refine ⟨170653127492367969771571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910150013292629172115045 170653127492367969771571)
                  ·
                    rfl

theorem cell22_1495556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_1495556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495556 prefixEnd_1495556 := by exact prefixLift 1495556
  have htrace : WordTrace (prefixWord ++ tailWord_1495556) baseStart_1495556 baseEnd_1495556 := by
    simpa [prefixWord, tailWord_1495556, baseEnd_1495556] using wordTrace_append hprefix tailTrace_1495556
  have hstable : (prefixWord ++ tailWord_1495556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495556).length < 2 ^ (prefixWord ++ tailWord_1495556).sum := by decide
  have hdescent : baseEnd_1495556 < baseStart_1495556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495612 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 5]
def baseStart_1495612 : Nat := 118140960795 + 1495612 * 2 ^ 59
def prefixEnd_1495612 : Nat := 4983230072969 + 3 ^ 40 * 1495612 * 2
def baseEnd_1495612 : Nat := 170659517473846143304847

theorem tailTrace_1495612 : CollatzResearch.WordTrace tailWord_1495612 prefixEnd_1495612 170659517473846143304847 := by
  unfold tailWord_1495612
  simp only [CollatzResearch.WordTrace]
  refine ⟨27274725528830314519436545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36366300705107086025915393 27274725528830314519436545)
  ·
    refine ⟨20456044146622735889577409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27274725528830314519436545 20456044146622735889577409)
    ·
      refine ⟨15342033109967051917183057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20456044146622735889577409 15342033109967051917183057)
      ·
        refine ⟨11506524832475288937887293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15342033109967051917183057 11506524832475288937887293)
        ·
          refine ⟨4314946812178233351707735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11506524832475288937887293 4314946812178233351707735)
          ·
            refine ⟨6472420218267350027561603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314946812178233351707735 6472420218267350027561603)
            ·
              refine ⟨9708630327401025041342405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6472420218267350027561603 9708630327401025041342405)
              ·
                refine ⟨1820368186387692195251701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9708630327401025041342405 1820368186387692195251701)
                ·
                  refine ⟨170659517473846143304847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1820368186387692195251701 170659517473846143304847)
                  ·
                    rfl

theorem cell22_1495612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_1495612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495612 prefixEnd_1495612 := by exact prefixLift 1495612
  have htrace : WordTrace (prefixWord ++ tailWord_1495612) baseStart_1495612 baseEnd_1495612 := by
    simpa [prefixWord, tailWord_1495612, baseEnd_1495612] using wordTrace_append hprefix tailTrace_1495612
  have hstable : (prefixWord ++ tailWord_1495612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495612).length < 2 ^ (prefixWord ++ tailWord_1495612).sum := by decide
  have hdescent : baseEnd_1495612 < baseStart_1495612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495616 : List Nat := [2, 1, 1, 2, 2, 2, 6, 2, 1, 3]
def baseStart_1495616 : Nat := 118140960795 + 1495616 * 2 ^ 59
def prefixEnd_1495616 : Nat := 4983230072969 + 3 ^ 40 * 1495616 * 2
def baseEnd_1495616 : Nat := 511979921703283752814529

theorem tailTrace_1495616 : CollatzResearch.WordTrace tailWord_1495616 prefixEnd_1495616 511979921703283752814529 := by
  unfold tailWord_1495616
  simp only [CollatzResearch.WordTrace]
  refine ⟨27274798474823068861009351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36366397966430758481345801 27274798474823068861009351)
  ·
    refine ⟨40912197712234603291514027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27274798474823068861009351 40912197712234603291514027)
    ·
      refine ⟨61368296568351904937271041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40912197712234603291514027 61368296568351904937271041)
      ·
        refine ⟨46026222426263928702953281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61368296568351904937271041 46026222426263928702953281)
        ·
          refine ⟨34519666819697946527214961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46026222426263928702953281 34519666819697946527214961)
          ·
            refine ⟨25889750114773459895411221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34519666819697946527214961 25889750114773459895411221)
            ·
              refine ⟨1213582036630005932597401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25889750114773459895411221 1213582036630005932597401)
              ·
                refine ⟨910186527472504449448051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213582036630005932597401 910186527472504449448051)
                ·
                  refine ⟨1365279791208756674172077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910186527472504449448051 1365279791208756674172077)
                  ·
                    refine ⟨511979921703283752814529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1365279791208756674172077 511979921703283752814529)
                    ·
                      rfl

theorem cell22_1495616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 1, 3].length) (baseStart_1495616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495616 prefixEnd_1495616 := by exact prefixLift 1495616
  have htrace : WordTrace (prefixWord ++ tailWord_1495616) baseStart_1495616 baseEnd_1495616 := by
    simpa [prefixWord, tailWord_1495616, baseEnd_1495616] using wordTrace_append hprefix tailTrace_1495616
  have hstable : (prefixWord ++ tailWord_1495616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495616).length < 2 ^ (prefixWord ++ tailWord_1495616).sum := by decide
  have hdescent : baseEnd_1495616 < baseStart_1495616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495629 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1495629 : Nat := 118140960795 + 1495629 * 2 ^ 59
def prefixEnd_1495629 : Nat := 4983230072969 + 3 ^ 40 * 1495629 * 2
def baseEnd_1495629 : Nat := 170661457289652017413163

theorem tailTrace_1495629 : CollatzResearch.WordTrace tailWord_1495629 prefixEnd_1495629 170661457289652017413163 := by
  unfold tailWord_1495629
  simp only [CollatzResearch.WordTrace]
  refine ⟨54550071098599040942241941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36366714065732693961494627 54550071098599040942241941)
  ·
    refine ⟨2557034582746830044167591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54550071098599040942241941 2557034582746830044167591)
    ·
      refine ⟨3835551874120245066251387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557034582746830044167591 3835551874120245066251387)
      ·
        refine ⟨5753327811180367599377081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3835551874120245066251387 5753327811180367599377081)
        ·
          refine ⟨4314995858385275699532811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5753327811180367599377081 4314995858385275699532811)
          ·
            refine ⟨6472493787577913549299217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314995858385275699532811 6472493787577913549299217)
            ·
              refine ⟨4854370340683435161974413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6472493787577913549299217 4854370340683435161974413)
              ·
                refine ⟨1820388877756288185740405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4854370340683435161974413 1820388877756288185740405)
                ·
                  refine ⟨170661457289652017413163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1820388877756288185740405 170661457289652017413163)
                  ·
                    rfl

theorem cell22_1495629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1495629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495629 prefixEnd_1495629 := by exact prefixLift 1495629
  have htrace : WordTrace (prefixWord ++ tailWord_1495629) baseStart_1495629 baseEnd_1495629 := by
    simpa [prefixWord, tailWord_1495629, baseEnd_1495629] using wordTrace_append hprefix tailTrace_1495629
  have hstable : (prefixWord ++ tailWord_1495629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495629).length < 2 ^ (prefixWord ++ tailWord_1495629).sum := by decide
  have hdescent : baseEnd_1495629 < baseStart_1495629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495640 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 8]
def baseStart_1495640 : Nat := 118140960795 + 1495640 * 2 ^ 59
def prefixEnd_1495640 : Nat := 4983230072969 + 3 ^ 40 * 1495640 * 2
def baseEnd_1495640 : Nat := 170662712464585230071485

theorem tailTrace_1495640 : CollatzResearch.WordTrace tailWord_1495640 prefixEnd_1495640 170662712464585230071485 := by
  unfold tailWord_1495640
  simp only [CollatzResearch.WordTrace]
  refine ⟨27275236150779594910446187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36366981534372793213928249 27275236150779594910446187)
  ·
    refine ⟨40912854226169392365669281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27275236150779594910446187 40912854226169392365669281)
    ·
      refine ⟨30684640669627044274251961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40912854226169392365669281 30684640669627044274251961)
      ·
        refine ⟨23013480502220283205688971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30684640669627044274251961 23013480502220283205688971)
        ·
          refine ⟨34520220753330424808533457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23013480502220283205688971 34520220753330424808533457)
          ·
            refine ⟨25890165564997818606400093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34520220753330424808533457 25890165564997818606400093)
            ·
              refine ⟨9708812086874181977400035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25890165564997818606400093 9708812086874181977400035)
              ·
                refine ⟨14563218130311272966100053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9708812086874181977400035 14563218130311272966100053)
                ·
                  refine ⟨170662712464585230071485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14563218130311272966100053 170662712464585230071485)
                  ·
                    rfl

theorem cell22_1495640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_1495640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495640 prefixEnd_1495640 := by exact prefixLift 1495640
  have htrace : WordTrace (prefixWord ++ tailWord_1495640) baseStart_1495640 baseEnd_1495640 := by
    simpa [prefixWord, tailWord_1495640, baseEnd_1495640] using wordTrace_append hprefix tailTrace_1495640
  have hstable : (prefixWord ++ tailWord_1495640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495640).length < 2 ^ (prefixWord ++ tailWord_1495640).sum := by decide
  have hdescent : baseEnd_1495640 < baseStart_1495640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495650 : List Nat := [3, 3, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1495650 : Nat := 118140960795 + 1495650 * 2 ^ 59
def prefixEnd_1495650 : Nat := 4983230072969 + 3 ^ 40 * 1495650 * 2
def baseEnd_1495650 : Nat := 511991560598118997464425

theorem tailTrace_1495650 : CollatzResearch.WordTrace tailWord_1495650 prefixEnd_1495650 511991560598118997464425 := by
  unfold tailWord_1495650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13637709257880740382189101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36367224687681974352504269 13637709257880740382189101)
  ·
    refine ⟨5114140971705277643320913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13637709257880740382189101 5114140971705277643320913)
    ·
      refine ⟨3835605728778958232490685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5114140971705277643320913 3835605728778958232490685)
      ·
        refine ⟨1438352148292109337184007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3835605728778958232490685 1438352148292109337184007)
        ·
          refine ⟨2157528222438164005776011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438352148292109337184007 2157528222438164005776011)
          ·
            refine ⟨3236292333657246008664017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157528222438164005776011 3236292333657246008664017)
            ·
              refine ⟨2427219250242934506498013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236292333657246008664017 2427219250242934506498013)
              ·
                refine ⟨910207218841100439936755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2427219250242934506498013 910207218841100439936755)
                ·
                  refine ⟨1365310828261650659905133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910207218841100439936755 1365310828261650659905133)
                  ·
                    refine ⟨511991560598118997464425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1365310828261650659905133 511991560598118997464425)
                    ·
                      rfl

theorem cell22_1495650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1495650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495650 prefixEnd_1495650 := by exact prefixLift 1495650
  have htrace : WordTrace (prefixWord ++ tailWord_1495650) baseStart_1495650 baseEnd_1495650 := by
    simpa [prefixWord, tailWord_1495650, baseEnd_1495650] using wordTrace_append hprefix tailTrace_1495650
  have hstable : (prefixWord ++ tailWord_1495650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495650).length < 2 ^ (prefixWord ++ tailWord_1495650).sum := by decide
  have hdescent : baseEnd_1495650 < baseStart_1495650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495672 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 4, 3]
def baseStart_1495672 : Nat := 118140960795 + 1495672 * 2 ^ 59
def prefixEnd_1495672 : Nat := 4983230072969 + 3 ^ 40 * 1495672 * 2
def baseEnd_1495672 : Nat := 511999091647718273414357

theorem tailTrace_1495672 : CollatzResearch.WordTrace tailWord_1495672 prefixEnd_1495672 511999091647718273414357 := by
  unfold tailWord_1495672
  simp only [CollatzResearch.WordTrace]
  refine ⟨27275819718721629643028635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36367759624962172857371513 27275819718721629643028635)
  ·
    refine ⟨40913729578082444464542953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27275819718721629643028635 40913729578082444464542953)
    ·
      refine ⟨30685297183561833348407215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40913729578082444464542953 30685297183561833348407215)
      ·
        refine ⟨46027945775342750022610823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30685297183561833348407215 46027945775342750022610823)
        ·
          refine ⟨69041918663014125033916235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46027945775342750022610823 69041918663014125033916235)
          ·
            refine ⟨103562877994521187550874353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69041918663014125033916235 103562877994521187550874353)
            ·
              refine ⟨77672158495890890663155765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103562877994521187550874353 77672158495890890663155765)
              ·
                refine ⟨7281764858989770999670853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77672158495890890663155765 7281764858989770999670853)
                ·
                  refine ⟨1365330911060582062438285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7281764858989770999670853 1365330911060582062438285)
                  ·
                    refine ⟨511999091647718273414357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1365330911060582062438285 511999091647718273414357)
                    ·
                      rfl

theorem cell22_1495672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_1495672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495672 prefixEnd_1495672 := by exact prefixLift 1495672
  have htrace : WordTrace (prefixWord ++ tailWord_1495672) baseStart_1495672 baseEnd_1495672 := by
    simpa [prefixWord, tailWord_1495672, baseEnd_1495672] using wordTrace_append hprefix tailTrace_1495672
  have hstable : (prefixWord ++ tailWord_1495672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495672).length < 2 ^ (prefixWord ++ tailWord_1495672).sum := by decide
  have hdescent : baseEnd_1495672 < baseStart_1495672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495792 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 6]
def baseStart_1495792 : Nat := 118140960795 + 1495792 * 2 ^ 59
def prefixEnd_1495792 : Nat := 4983230072969 + 3 ^ 40 * 1495792 * 2
def baseEnd_1495792 : Nat := 170680056700025986804663

theorem tailTrace_1495792 : CollatzResearch.WordTrace tailWord_1495792 prefixEnd_1495792 170680056700025986804663 := by
  unfold tailWord_1495792
  simp only [CollatzResearch.WordTrace]
  refine ⟨27278008098504259890212815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36370677464672346520283753 27278008098504259890212815)
  ·
    refine ⟨40917012147756389835319223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27278008098504259890212815 40917012147756389835319223)
    ·
      refine ⟨61375518221634584752978835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40917012147756389835319223 61375518221634584752978835)
      ·
        refine ⟨92063277332451877129468253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61375518221634584752978835 92063277332451877129468253)
        ·
          refine ⟨34523728999669453923550595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92063277332451877129468253 34523728999669453923550595)
          ·
            refine ⟨51785593499504180885325893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34523728999669453923550595 51785593499504180885325893)
            ·
              refine ⟨9709798781157033915998605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51785593499504180885325893 9709798781157033915998605)
              ·
                refine ⟨3641174542933887718499477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9709798781157033915998605 3641174542933887718499477)
                ·
                  refine ⟨170680056700025986804663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3641174542933887718499477 170680056700025986804663)
                  ·
                    rfl

theorem cell22_1495792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_1495792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495792 prefixEnd_1495792 := by exact prefixLift 1495792
  have htrace : WordTrace (prefixWord ++ tailWord_1495792) baseStart_1495792 baseEnd_1495792 := by
    simpa [prefixWord, tailWord_1495792, baseEnd_1495792] using wordTrace_append hprefix tailTrace_1495792
  have hstable : (prefixWord ++ tailWord_1495792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495792).length < 2 ^ (prefixWord ++ tailWord_1495792).sum := by decide
  have hdescent : baseEnd_1495792 < baseStart_1495792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495794 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1495794 : Nat := 118140960795 + 1495794 * 2 ^ 59
def prefixEnd_1495794 : Nat := 4983230072969 + 3 ^ 40 * 1495794 * 2
def baseEnd_1495794 : Nat := 512040854740950621863983

theorem tailTrace_1495794 : CollatzResearch.WordTrace tailWord_1495794 prefixEnd_1495794 512040854740950621863983 := by
  unfold tailWord_1495794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13639022285750318530499609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36370726095334182747998957 13639022285750318530499609)
  ·
    refine ⟨10229266714312738897874707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13639022285750318530499609 10229266714312738897874707)
    ·
      refine ⟨15343900071469108346812061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10229266714312738897874707 15343900071469108346812061)
      ·
        refine ⟨5753962526800915630054523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15343900071469108346812061 5753962526800915630054523)
        ·
          refine ⟨8630943790201373445081785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5753962526800915630054523 8630943790201373445081785)
          ·
            refine ⟨6473207842651030083811339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8630943790201373445081785 6473207842651030083811339)
            ·
              refine ⟨9709811763976545125717009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6473207842651030083811339 9709811763976545125717009)
              ·
                refine ⟨7282358822982408844287757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9709811763976545125717009 7282358822982408844287757)
                ·
                  refine ⟨2730884558618403316607909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7282358822982408844287757 2730884558618403316607909)
                  ·
                    refine ⟨512040854740950621863983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2730884558618403316607909 512040854740950621863983)
                    ·
                      rfl

theorem cell22_1495794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1495794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495794 prefixEnd_1495794 := by exact prefixLift 1495794
  have htrace : WordTrace (prefixWord ++ tailWord_1495794) baseStart_1495794 baseEnd_1495794 := by
    simpa [prefixWord, tailWord_1495794, baseEnd_1495794] using wordTrace_append hprefix tailTrace_1495794
  have hstable : (prefixWord ++ tailWord_1495794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495794).length < 2 ^ (prefixWord ++ tailWord_1495794).sum := by decide
  have hdescent : baseEnd_1495794 < baseStart_1495794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495858 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_1495858 : Nat := 118140960795 + 1495858 * 2 ^ 59
def prefixEnd_1495858 : Nat := 4983230072969 + 3 ^ 40 * 1495858 * 2
def baseEnd_1495858 : Nat := 512062763248875788263787

theorem tailTrace_1495858 : CollatzResearch.WordTrace tailWord_1495858 prefixEnd_1495858 512062763248875788263787 := by
  unfold tailWord_1495858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13639605853692353263082057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36372282276512942034885485 13639605853692353263082057)
  ·
    refine ⟨10229704390269264947311543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13639605853692353263082057 10229704390269264947311543)
    ·
      refine ⟨15344556585403897420967315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10229704390269264947311543 15344556585403897420967315)
      ·
        refine ⟨23016834878105846131450973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15344556585403897420967315 23016834878105846131450973)
        ·
          refine ⟨8631313079289692299294115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23016834878105846131450973 8631313079289692299294115)
          ·
            refine ⟨12946969618934538448941173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8631313079289692299294115 12946969618934538448941173)
            ·
              refine ⟨1213778401775112979588235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12946969618934538448941173 1213778401775112979588235)
              ·
                refine ⟨1820667602662669469382353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213778401775112979588235 1820667602662669469382353)
                ·
                  refine ⟨1365500701997002102036765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1820667602662669469382353 1365500701997002102036765)
                  ·
                    refine ⟨512062763248875788263787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1365500701997002102036765 512062763248875788263787)
                    ·
                      rfl

theorem cell22_1495858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_1495858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495858 prefixEnd_1495858 := by exact prefixLift 1495858
  have htrace : WordTrace (prefixWord ++ tailWord_1495858) baseStart_1495858 baseEnd_1495858 := by
    simpa [prefixWord, tailWord_1495858, baseEnd_1495858] using wordTrace_append hprefix tailTrace_1495858
  have hstable : (prefixWord ++ tailWord_1495858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495858).length < 2 ^ (prefixWord ++ tailWord_1495858).sum := by decide
  have hdescent : baseEnd_1495858 < baseStart_1495858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495871 : List Nat := [1, 1, 2, 2, 5, 3, 2, 6]
def baseStart_1495871 : Nat := 118140960795 + 1495871 * 2 ^ 59
def prefixEnd_1495871 : Nat := 4983230072969 + 3 ^ 40 * 1495871 * 2
def baseEnd_1495871 : Nat := 56896357046060898632083

theorem tailTrace_1495871 : CollatzResearch.WordTrace tailWord_1495871 prefixEnd_1495871 56896357046060898632083 := by
  unfold tailWord_1495871
  simp only [CollatzResearch.WordTrace]
  refine ⟨54558897563722316272551467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36372598375814877515034311 54558897563722316272551467)
  ·
    refine ⟨81838346345583474408827201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54558897563722316272551467 81838346345583474408827201)
    ·
      refine ⟨61378759759187605806620401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81838346345583474408827201 61378759759187605806620401)
      ·
        refine ⟨46034069819390704354965301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61378759759187605806620401 46034069819390704354965301)
        ·
          refine ⟨4315694045567878533277997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46034069819390704354965301 4315694045567878533277997)
          ·
            refine ⟨1618385267087954449979249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4315694045567878533277997 1618385267087954449979249)
            ·
              refine ⟨1213788950315965837484437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618385267087954449979249 1213788950315965837484437)
              ·
                refine ⟨56896357046060898632083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1213788950315965837484437 56896357046060898632083)
                ·
                  rfl

theorem cell22_1495871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 6].length) (baseStart_1495871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495871 prefixEnd_1495871 := by exact prefixLift 1495871
  have htrace : WordTrace (prefixWord ++ tailWord_1495871) baseStart_1495871 baseEnd_1495871 := by
    simpa [prefixWord, tailWord_1495871, baseEnd_1495871] using wordTrace_append hprefix tailTrace_1495871
  have hstable : (prefixWord ++ tailWord_1495871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495871).length < 2 ^ (prefixWord ++ tailWord_1495871).sum := by decide
  have hdescent : baseEnd_1495871 < baseStart_1495871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495954 : List Nat := [3, 2, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_1495954 : Nat := 118140960795 + 1495954 * 2 ^ 59
def prefixEnd_1495954 : Nat := 4983230072969 + 3 ^ 40 * 1495954 * 2
def baseEnd_1495954 : Nat := 512095626010763537863493

theorem tailTrace_1495954 : CollatzResearch.WordTrace tailWord_1495954 prefixEnd_1495954 512095626010763537863493 := by
  unfold tailWord_1495954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13640481205605405361955729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36374616548281080965215277 13640481205605405361955729)
  ·
    refine ⟨10230360904204054021466797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13640481205605405361955729 10230360904204054021466797)
    ·
      refine ⟨3836385339076520258050049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10230360904204054021466797 3836385339076520258050049)
      ·
        refine ⟨2877289004307390193537537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3836385339076520258050049 2877289004307390193537537)
        ·
          refine ⟨2157966753230542645153153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2877289004307390193537537 2157966753230542645153153)
          ·
            refine ⟨1618475064922906983864865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2157966753230542645153153 1618475064922906983864865)
            ·
              refine ⟨1213856298692180237898649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618475064922906983864865 1213856298692180237898649)
              ·
                refine ⟨910392224019135178423987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213856298692180237898649 910392224019135178423987)
                ·
                  refine ⟨1365588336028702767635981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910392224019135178423987 1365588336028702767635981)
                  ·
                    refine ⟨512095626010763537863493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1365588336028702767635981 512095626010763537863493)
                    ·
                      rfl

theorem cell22_1495954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_1495954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495954 prefixEnd_1495954 := by exact prefixLift 1495954
  have htrace : WordTrace (prefixWord ++ tailWord_1495954) baseStart_1495954 baseEnd_1495954 := by
    simpa [prefixWord, tailWord_1495954, baseEnd_1495954] using wordTrace_append hprefix tailTrace_1495954
  have hstable : (prefixWord ++ tailWord_1495954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495954).length < 2 ^ (prefixWord ++ tailWord_1495954).sum := by decide
  have hdescent : baseEnd_1495954 < baseStart_1495954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495959 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 3, 5]
def baseStart_1495959 : Nat := 118140960795 + 1495959 * 2 ^ 59
def prefixEnd_1495959 : Nat := 4983230072969 + 3 ^ 40 * 1495959 * 2
def baseEnd_1495959 : Nat := 512097337612945191488477

theorem tailTrace_1495959 : CollatzResearch.WordTrace tailWord_1495959 prefixEnd_1495959 512097337612945191488477 := by
  unfold tailWord_1495959
  simp only [CollatzResearch.WordTrace]
  refine ⟨54562107187403507301754931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36374738124935671534503287 54562107187403507301754931)
  ·
    refine ⟨81843160781105260952632397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54562107187403507301754931 81843160781105260952632397)
    ·
      refine ⟨30691185292914472857237149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81843160781105260952632397 30691185292914472857237149)
      ·
        refine ⟨11509194484842927321463931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30691185292914472857237149 11509194484842927321463931)
        ·
          refine ⟨17263791727264390982195897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11509194484842927321463931 17263791727264390982195897)
          ·
            refine ⟨12947843795448293236646923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17263791727264390982195897 12947843795448293236646923)
            ·
              refine ⟨19421765693172439854970385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12947843795448293236646923 19421765693172439854970385)
              ·
                refine ⟨14566324269879329891227789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19421765693172439854970385 14566324269879329891227789)
                ·
                  refine ⟨5462371601204748709210421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14566324269879329891227789 5462371601204748709210421)
                  ·
                    refine ⟨512097337612945191488477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5462371601204748709210421 512097337612945191488477)
                    ·
                      rfl

theorem cell22_1495959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_1495959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495959 prefixEnd_1495959 := by exact prefixLift 1495959
  have htrace : WordTrace (prefixWord ++ tailWord_1495959) baseStart_1495959 baseEnd_1495959 := by
    simpa [prefixWord, tailWord_1495959, baseEnd_1495959] using wordTrace_append hprefix tailTrace_1495959
  have hstable : (prefixWord ++ tailWord_1495959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495959).length < 2 ^ (prefixWord ++ tailWord_1495959).sum := by decide
  have hdescent : baseEnd_1495959 < baseStart_1495959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495991 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 2, 4]
def baseStart_1495991 : Nat := 118140960795 + 1495991 * 2 ^ 59
def prefixEnd_1495991 : Nat := 4983230072969 + 3 ^ 40 * 1495991 * 2
def baseEnd_1495991 : Nat := 512108291866907774688379

theorem tailTrace_1495991 : CollatzResearch.WordTrace tailWord_1495991 prefixEnd_1495991 512108291866907774688379 := by
  unfold tailWord_1495991
  simp only [CollatzResearch.WordTrace]
  refine ⟨54563274323287576766919827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36375516215525051177946551 54563274323287576766919827)
  ·
    refine ⟨81844911484931365150379741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54563274323287576766919827 81844911484931365150379741)
    ·
      refine ⟨30691841806849261931392403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81844911484931365150379741 30691841806849261931392403)
      ·
        refine ⟨46037762710273892897088605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30691841806849261931392403 46037762710273892897088605)
        ·
          refine ⟨17264161016352709836408227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46037762710273892897088605 17264161016352709836408227)
          ·
            refine ⟨25896241524529064754612341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17264161016352709836408227 25896241524529064754612341)
            ·
              refine ⟨2427772642924599820744907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25896241524529064754612341 2427772642924599820744907)
              ·
                refine ⟨3641658964386899731117361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427772642924599820744907 3641658964386899731117361)
                ·
                  refine ⟨2731244223290174798338021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3641658964386899731117361 2731244223290174798338021)
                  ·
                    refine ⟨512108291866907774688379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2731244223290174798338021 512108291866907774688379)
                    ·
                      rfl

theorem cell22_1495991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_1495991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495991 prefixEnd_1495991 := by exact prefixLift 1495991
  have htrace : WordTrace (prefixWord ++ tailWord_1495991) baseStart_1495991 baseEnd_1495991 := by
    simpa [prefixWord, tailWord_1495991, baseEnd_1495991] using wordTrace_append hprefix tailTrace_1495991
  have hstable : (prefixWord ++ tailWord_1495991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495991).length < 2 ^ (prefixWord ++ tailWord_1495991).sum := by decide
  have hdescent : baseEnd_1495991 < baseStart_1495991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495997 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_1495997 : Nat := 118140960795 + 1495997 * 2 ^ 59
def prefixEnd_1495997 : Nat := 4983230072969 + 3 ^ 40 * 1495997 * 2
def baseEnd_1495997 : Nat := 512110345789525759038361

theorem tailTrace_1495997 : CollatzResearch.WordTrace tailWord_1495997 prefixEnd_1495997 512110345789525759038361 := by
  unfold tailWord_1495997
  simp only [CollatzResearch.WordTrace]
  refine ⟨54563493161265839791638245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36375662107510559861092163 54563493161265839791638245)
  ·
    refine ⟨10230654967737344960932171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54563493161265839791638245 10230654967737344960932171)
    ·
      refine ⟨15345982451606017441398257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10230654967737344960932171 15345982451606017441398257)
      ·
        refine ⟨11509486838704513081048693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15345982451606017441398257 11509486838704513081048693)
        ·
          refine ⟨1079014391128548101348315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11509486838704513081048693 1079014391128548101348315)
          ·
            refine ⟨1618521586692822152022473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079014391128548101348315 1618521586692822152022473)
            ·
              refine ⟨1213891190019616614016855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618521586692822152022473 1213891190019616614016855)
              ·
                refine ⟨1820836785029424921025283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213891190019616614016855 1820836785029424921025283)
                ·
                  refine ⟨2731255177544137381537925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820836785029424921025283 2731255177544137381537925)
                  ·
                    refine ⟨512110345789525759038361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2731255177544137381537925 512110345789525759038361)
                    ·
                      rfl

theorem cell22_1495997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_1495997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1495997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1495997 prefixEnd_1495997 := by exact prefixLift 1495997
  have htrace : WordTrace (prefixWord ++ tailWord_1495997) baseStart_1495997 baseEnd_1495997 := by
    simpa [prefixWord, tailWord_1495997, baseEnd_1495997] using wordTrace_append hprefix tailTrace_1495997
  have hstable : (prefixWord ++ tailWord_1495997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495997).length < 2 ^ (prefixWord ++ tailWord_1495997).sum := by decide
  have hdescent : baseEnd_1495997 < baseStart_1495997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496064 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_1496064 : Nat := 118140960795 + 1496064 * 2 ^ 59
def prefixEnd_1496064 : Nat := 4983230072969 + 3 ^ 40 * 1496064 * 2
def baseEnd_1496064 : Nat := 512133281258759917613155

theorem tailTrace_1496064 : CollatzResearch.WordTrace tailWord_1496064 prefixEnd_1496064 512133281258759917613155 := by
  unfold tailWord_1496064
  simp only [CollatzResearch.WordTrace]
  refine ⟨27282968426011555117163623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36377291234682073489551497 27282968426011555117163623)
  ·
    refine ⟨40924452639017332675745435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27282968426011555117163623 40924452639017332675745435)
    ·
      refine ⟨61386678958525999013618153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40924452639017332675745435 61386678958525999013618153)
      ·
        refine ⟨46040009218894499260213615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61386678958525999013618153 46040009218894499260213615)
        ·
          refine ⟨69060013828341748890320423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46040009218894499260213615 69060013828341748890320423)
          ·
            refine ⟨103590020742512623335480635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69060013828341748890320423 103590020742512623335480635)
            ·
              refine ⟨155385031113768935003220953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103590020742512623335480635 155385031113768935003220953)
              ·
                refine ⟨116538773335326701252415715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155385031113768935003220953 116538773335326701252415715)
                ·
                  refine ⟨174808160002990051878623573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116538773335326701252415715 174808160002990051878623573)
                  ·
                    refine ⟨512133281258759917613155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 174808160002990051878623573 512133281258759917613155)
                    ·
                      rfl

theorem cell22_1496064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_1496064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496064 prefixEnd_1496064 := by exact prefixLift 1496064
  have htrace : WordTrace (prefixWord ++ tailWord_1496064) baseStart_1496064 baseEnd_1496064 := by
    simpa [prefixWord, tailWord_1496064, baseEnd_1496064] using wordTrace_append hprefix tailTrace_1496064
  have hstable : (prefixWord ++ tailWord_1496064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496064).length < 2 ^ (prefixWord ++ tailWord_1496064).sum := by decide
  have hdescent : baseEnd_1496064 < baseStart_1496064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496072 : List Nat := [2, 1, 3, 2, 1, 4, 3, 2, 1, 3]
def baseStart_1496072 : Nat := 118140960795 + 1496072 * 2 ^ 59
def prefixEnd_1496072 : Nat := 4983230072969 + 3 ^ 40 * 1496072 * 2
def baseEnd_1496072 : Nat := 512136019822250563413131

theorem tailTrace_1496072 : CollatzResearch.WordTrace tailWord_1496072 prefixEnd_1496072 512136019822250563413131 := by
  unfold tailWord_1496072
  simp only [CollatzResearch.WordTrace]
  refine ⟨27283114317997063800309235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36377485757329418400412313 27283114317997063800309235)
  ·
    refine ⟨40924671476995595700463853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27283114317997063800309235 40924671476995595700463853)
    ·
      refine ⟨15346751803873348387673945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40924671476995595700463853 15346751803873348387673945)
      ·
        refine ⟨11510063852905011290755459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15346751803873348387673945 11510063852905011290755459)
        ·
          refine ⟨17265095779357516936133189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11510063852905011290755459 17265095779357516936133189)
          ·
            refine ⟨3237205458629534425524973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17265095779357516936133189 3237205458629534425524973)
            ·
              refine ⟨1213952046986075409571865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3237205458629534425524973 1213952046986075409571865)
              ·
                refine ⟨910464035239556557178899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213952046986075409571865 910464035239556557178899)
                ·
                  refine ⟨1365696052859334835768349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910464035239556557178899 1365696052859334835768349)
                  ·
                    refine ⟨512136019822250563413131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1365696052859334835768349 512136019822250563413131)
                    ·
                      rfl

theorem cell22_1496072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_1496072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496072 prefixEnd_1496072 := by exact prefixLift 1496072
  have htrace : WordTrace (prefixWord ++ tailWord_1496072) baseStart_1496072 baseEnd_1496072 := by
    simpa [prefixWord, tailWord_1496072, baseEnd_1496072] using wordTrace_append hprefix tailTrace_1496072
  have hstable : (prefixWord ++ tailWord_1496072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496072).length < 2 ^ (prefixWord ++ tailWord_1496072).sum := by decide
  have hdescent : baseEnd_1496072 < baseStart_1496072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496079 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 12]
def baseStart_1496079 : Nat := 118140960795 + 1496079 * 2 ^ 59
def prefixEnd_1496079 : Nat := 4983230072969 + 3 ^ 40 * 1496079 * 2
def baseEnd_1496079 : Nat := 170712805355101626162703

theorem tailTrace_1496079 : CollatzResearch.WordTrace tailWord_1496079 prefixEnd_1496079 170712805355101626162703 := by
  unfold tailWord_1496079
  simp only [CollatzResearch.WordTrace]
  refine ⟨54566483946968767796123291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36377655964645845197415527 54566483946968767796123291)
  ·
    refine ⟨81849725920453151694184937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54566483946968767796123291 81849725920453151694184937)
    ·
      refine ⟨61387294440339863770638703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81849725920453151694184937 61387294440339863770638703)
      ·
        refine ⟨92080941660509795655958055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61387294440339863770638703 92080941660509795655958055)
        ·
          refine ⟨138121412490764693483937083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92080941660509795655958055 138121412490764693483937083)
          ·
            refine ⟨207182118736147040225905625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138121412490764693483937083 207182118736147040225905625)
            ·
              refine ⟨155386589052110280169429219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207182118736147040225905625 155386589052110280169429219)
              ·
                refine ⟨233079883578165420254143829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155386589052110280169429219 233079883578165420254143829)
                ·
                  refine ⟨170712805355101626162703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 233079883578165420254143829 170712805355101626162703)
                  ·
                    rfl

theorem cell22_1496079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 12].length) (baseStart_1496079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496079 prefixEnd_1496079 := by exact prefixLift 1496079
  have htrace : WordTrace (prefixWord ++ tailWord_1496079) baseStart_1496079 baseEnd_1496079 := by
    simpa [prefixWord, tailWord_1496079, baseEnd_1496079] using wordTrace_append hprefix tailTrace_1496079
  have hstable : (prefixWord ++ tailWord_1496079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496079).length < 2 ^ (prefixWord ++ tailWord_1496079).sum := by decide
  have hdescent : baseEnd_1496079 < baseStart_1496079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496085 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 5]
def baseStart_1496085 : Nat := 118140960795 + 1496085 * 2 ^ 59
def prefixEnd_1496085 : Nat := 4983230072969 + 3 ^ 40 * 1496085 * 2
def baseEnd_1496085 : Nat := 170713489995974287612697

theorem tailTrace_1496085 : CollatzResearch.WordTrace tailWord_1496085 prefixEnd_1496085 170713489995974287612697 := by
  unfold tailWord_1496085
  simp only [CollatzResearch.WordTrace]
  refine ⟨54566702784947030820841709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36377801856631353880561139 54566702784947030820841709)
  ·
    refine ⟨20462513544355136557815641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54566702784947030820841709 20462513544355136557815641)
    ·
      refine ⟨15346885158266352418361731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20462513544355136557815641 15346885158266352418361731)
      ·
        refine ⟨23020327737399528627542597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15346885158266352418361731 23020327737399528627542597)
        ·
          refine ⟨4316311450762411617664237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23020327737399528627542597 4316311450762411617664237)
          ·
            refine ⟨1618616794035904356624089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4316311450762411617664237 1618616794035904356624089)
            ·
              refine ⟨1213962595526928267468067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618616794035904356624089 1213962595526928267468067)
              ·
                refine ⟨1820943893290392401202101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213962595526928267468067 1820943893290392401202101)
                ·
                  refine ⟨170713489995974287612697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1820943893290392401202101 170713489995974287612697)
                  ·
                    rfl

theorem cell22_1496085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_1496085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496085 prefixEnd_1496085 := by exact prefixLift 1496085
  have htrace : WordTrace (prefixWord ++ tailWord_1496085) baseStart_1496085 baseEnd_1496085 := by
    simpa [prefixWord, tailWord_1496085, baseEnd_1496085] using wordTrace_append hprefix tailTrace_1496085
  have hstable : (prefixWord ++ tailWord_1496085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496085).length < 2 ^ (prefixWord ++ tailWord_1496085).sum := by decide
  have hdescent : baseEnd_1496085 < baseStart_1496085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496098 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1496098 : Nat := 118140960795 + 1496098 * 2 ^ 59
def prefixEnd_1496098 : Nat := 4983230072969 + 3 ^ 40 * 1496098 * 2
def baseEnd_1496098 : Nat := 512144920153595162263051

theorem tailTrace_1496098 : CollatzResearch.WordTrace tailWord_1496098 prefixEnd_1496098 512144920153595162263051 := by
  unfold tailWord_1496098
  simp only [CollatzResearch.WordTrace]
  refine ⟨13641794233474983510266237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36378117955933289360709965 13641794233474983510266237)
  ·
    refine ⟨5115672837553118816349839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13641794233474983510266237 5115672837553118816349839)
    ·
      refine ⟨7673509256329678224524759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5115672837553118816349839 7673509256329678224524759)
      ·
        refine ⟨11510263884494517336787139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7673509256329678224524759 11510263884494517336787139)
        ·
          refine ⟨17265395826741776005180709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11510263884494517336787139 17265395826741776005180709)
          ·
            refine ⟨3237261717514083000971383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17265395826741776005180709 3237261717514083000971383)
            ·
              refine ⟨4855892576271124501457075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3237261717514083000971383 4855892576271124501457075)
              ·
                refine ⟨7283838864406686752185613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4855892576271124501457075 7283838864406686752185613)
                ·
                  refine ⟨2731439574152507532069605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7283838864406686752185613 2731439574152507532069605)
                  ·
                    refine ⟨512144920153595162263051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2731439574152507532069605 512144920153595162263051)
                    ·
                      rfl

theorem cell22_1496098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1496098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496098 prefixEnd_1496098 := by exact prefixLift 1496098
  have htrace : WordTrace (prefixWord ++ tailWord_1496098) baseStart_1496098 baseEnd_1496098 := by
    simpa [prefixWord, tailWord_1496098, baseEnd_1496098] using wordTrace_append hprefix tailTrace_1496098
  have hstable : (prefixWord ++ tailWord_1496098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496098).length < 2 ^ (prefixWord ++ tailWord_1496098).sum := by decide
  have hdescent : baseEnd_1496098 < baseStart_1496098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496113 : List Nat := [1, 2, 2, 3, 1, 2, 2, 5, 4]
def baseStart_1496113 : Nat := 118140960795 + 1496113 * 2 ^ 59
def prefixEnd_1496113 : Nat := 4983230072969 + 3 ^ 40 * 1496113 * 2
def baseEnd_1496113 : Nat := 170716684986713374379335

theorem tailTrace_1496113 : CollatzResearch.WordTrace tailWord_1496113 prefixEnd_1496113 170716684986713374379335 := by
  unfold tailWord_1496113
  simp only [CollatzResearch.WordTrace]
  refine ⟨54567724028845591602860993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36378482685897061068573995 54567724028845591602860993)
  ·
    refine ⟨40925793021634193702145745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54567724028845591602860993 40925793021634193702145745)
    ·
      refine ⟨30694344766225645276609309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40925793021634193702145745 30694344766225645276609309)
      ·
        refine ⟨11510379287334616978728491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30694344766225645276609309 11510379287334616978728491)
        ·
          refine ⟨17265568931001925468092737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11510379287334616978728491 17265568931001925468092737)
          ·
            refine ⟨12949176698251444101069553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17265568931001925468092737 12949176698251444101069553)
            ·
              refine ⟨9711882523688583075802165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12949176698251444101069553 9711882523688583075802165)
              ·
                refine ⟨910488986595804663356453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9711882523688583075802165 910488986595804663356453)
                ·
                  refine ⟨170716684986713374379335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910488986595804663356453 170716684986713374379335)
                  ·
                    rfl

theorem cell22_1496113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 4].length) (baseStart_1496113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496113 prefixEnd_1496113 := by exact prefixLift 1496113
  have htrace : WordTrace (prefixWord ++ tailWord_1496113) baseStart_1496113 baseEnd_1496113 := by
    simpa [prefixWord, tailWord_1496113, baseEnd_1496113] using wordTrace_append hprefix tailTrace_1496113
  have hstable : (prefixWord ++ tailWord_1496113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496113).length < 2 ^ (prefixWord ++ tailWord_1496113).sum := by decide
  have hdescent : baseEnd_1496113 < baseStart_1496113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496280 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 1, 5]
def baseStart_1496280 : Nat := 118140960795 + 1496280 * 2 ^ 59
def prefixEnd_1496280 : Nat := 4983230072969 + 3 ^ 40 * 1496280 * 2
def baseEnd_1496280 : Nat := 512207222473007354212493

theorem tailTrace_1496280 : CollatzResearch.WordTrace tailWord_1496280 prefixEnd_1496280 512207222473007354212493 := by
  unfold tailWord_1496280
  simp only [CollatzResearch.WordTrace]
  refine ⟨27286907509620289562095147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36382543346160386082793529 27286907509620289562095147)
  ·
    refine ⟨40930361264430434343142721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27286907509620289562095147 40930361264430434343142721)
    ·
      refine ⟨30697770948322825757357041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40930361264430434343142721 30697770948322825757357041)
      ·
        refine ⟨23023328211242119318017781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30697770948322825757357041 23023328211242119318017781)
        ·
          refine ⟨2158437019803948686064167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23023328211242119318017781 2158437019803948686064167)
          ·
            refine ⟨3237655529705923029096251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158437019803948686064167 3237655529705923029096251)
            ·
              refine ⟨4856483294558884543644377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3237655529705923029096251 4856483294558884543644377)
              ·
                refine ⟨3642362470919163407733283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4856483294558884543644377 3642362470919163407733283)
                ·
                  refine ⟨5463543706378745111599925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3642362470919163407733283 5463543706378745111599925)
                  ·
                    refine ⟨512207222473007354212493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5463543706378745111599925 512207222473007354212493)
                    ·
                      rfl

theorem cell22_1496280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_1496280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496280 prefixEnd_1496280 := by exact prefixLift 1496280
  have htrace : WordTrace (prefixWord ++ tailWord_1496280) baseStart_1496280 baseEnd_1496280 := by
    simpa [prefixWord, tailWord_1496280, baseEnd_1496280] using wordTrace_append hprefix tailTrace_1496280
  have hstable : (prefixWord ++ tailWord_1496280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496280).length < 2 ^ (prefixWord ++ tailWord_1496280).sum := by decide
  have hdescent : baseEnd_1496280 < baseStart_1496280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496293 : List Nat := [1, 3, 1, 4, 3, 10]
def baseStart_1496293 : Nat := 118140960795 + 1496293 * 2 ^ 59
def prefixEnd_1496293 : Nat := 4983230072969 + 3 ^ 40 * 1496293 * 2
def baseEnd_1496293 : Nat := 6323600896773822884413

theorem tailTrace_1496293 : CollatzResearch.WordTrace tailWord_1496293 prefixEnd_1496293 6323600896773822884413 := by
  unfold tailWord_1496293
  simp only [CollatzResearch.WordTrace]
  refine ⟨54574289168193482344413533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36382859445462321562942355 54574289168193482344413533)
  ·
    refine ⟨20465358438072555879155075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54574289168193482344413533 20465358438072555879155075)
    ·
      refine ⟨30698037657108833818732613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20465358438072555879155075 30698037657108833818732613)
      ·
        refine ⟨5755882060707906341012365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30698037657108833818732613 5755882060707906341012365)
        ·
          refine ⟨2158455772765464877879637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5755882060707906341012365 2158455772765464877879637)
          ·
            refine ⟨6323600896773822884413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2158455772765464877879637 6323600896773822884413)
            ·
              rfl

theorem cell22_1496293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 10].length) (baseStart_1496293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496293 prefixEnd_1496293 := by exact prefixLift 1496293
  have htrace : WordTrace (prefixWord ++ tailWord_1496293) baseStart_1496293 baseEnd_1496293 := by
    simpa [prefixWord, tailWord_1496293, baseEnd_1496293] using wordTrace_append hprefix tailTrace_1496293
  have hstable : (prefixWord ++ tailWord_1496293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496293).length < 2 ^ (prefixWord ++ tailWord_1496293).sum := by decide
  have hdescent : baseEnd_1496293 < baseStart_1496293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496325 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 3, 3]
def baseStart_1496325 : Nat := 118140960795 + 1496325 * 2 ^ 59
def prefixEnd_1496325 : Nat := 4983230072969 + 3 ^ 40 * 1496325 * 2
def baseEnd_1496325 : Nat := 512222626892642236837355

theorem tailTrace_1496325 : CollatzResearch.WordTrace tailWord_1496325 prefixEnd_1496325 512222626892642236837355 := by
  unfold tailWord_1496325
  simp only [CollatzResearch.WordTrace]
  refine ⟨54575456304077551809578429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36383637536051701206385619 54575456304077551809578429)
  ·
    refine ⟨20465796114029081928591911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54575456304077551809578429 20465796114029081928591911)
    ·
      refine ⟨30698694171043622892887867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20465796114029081928591911 30698694171043622892887867)
      ·
        refine ⟨46048041256565434339331801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30698694171043622892887867 46048041256565434339331801)
        ·
          refine ⟨34536030942424075754498851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46048041256565434339331801 34536030942424075754498851)
          ·
            refine ⟨51804046413636113631748277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34536030942424075754498851 51804046413636113631748277)
            ·
              refine ⟨4856629351278385652976401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51804046413636113631748277 4856629351278385652976401)
              ·
                refine ⟨3642472013458789239732301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4856629351278385652976401 3642472013458789239732301)
                ·
                  refine ⟨1365927005047045964899613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3642472013458789239732301 1365927005047045964899613)
                  ·
                    refine ⟨512222626892642236837355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1365927005047045964899613 512222626892642236837355)
                    ·
                      rfl

theorem cell22_1496325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_1496325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496325 prefixEnd_1496325 := by exact prefixLift 1496325
  have htrace : WordTrace (prefixWord ++ tailWord_1496325) baseStart_1496325 baseEnd_1496325 := by
    simpa [prefixWord, tailWord_1496325, baseEnd_1496325] using wordTrace_append hprefix tailTrace_1496325
  have hstable : (prefixWord ++ tailWord_1496325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496325).length < 2 ^ (prefixWord ++ tailWord_1496325).sum := by decide
  have hdescent : baseEnd_1496325 < baseStart_1496325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496355 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 5]
def baseStart_1496355 : Nat := 118140960795 + 1496355 * 2 ^ 59
def prefixEnd_1496355 : Nat := 4983230072969 + 3 ^ 40 * 1496355 * 2
def baseEnd_1496355 : Nat := 170744298835244052862421

theorem tailTrace_1496355 : CollatzResearch.WordTrace tailWord_1496355 prefixEnd_1496355 170744298835244052862421 := by
  unfold tailWord_1496355
  simp only [CollatzResearch.WordTrace]
  refine ⟨54576550493968866933170519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36384366995979244622113679 54576550493968866933170519)
  ·
    refine ⟨81864825740953300399755779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54576550493968866933170519 81864825740953300399755779)
    ·
      refine ⟨122797238611429950599633669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81864825740953300399755779 122797238611429950599633669)
      ·
        refine ⟨23024482239643115737431313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122797238611429950599633669 23024482239643115737431313)
        ·
          refine ⟨17268361679732336803073485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23024482239643115737431313 17268361679732336803073485)
          ·
            refine ⟨6475635629899626301152557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17268361679732336803073485 6475635629899626301152557)
            ·
              refine ⟨2428363361212359862932209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6475635629899626301152557 2428363361212359862932209)
              ·
                refine ⟨1821272520909269897199157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428363361212359862932209 1821272520909269897199157)
                ·
                  refine ⟨170744298835244052862421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1821272520909269897199157 170744298835244052862421)
                  ·
                    rfl

theorem cell22_1496355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 5].length) (baseStart_1496355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496355 prefixEnd_1496355 := by exact prefixLift 1496355
  have htrace : WordTrace (prefixWord ++ tailWord_1496355) baseStart_1496355 baseEnd_1496355 := by
    simpa [prefixWord, tailWord_1496355, baseEnd_1496355] using wordTrace_append hprefix tailTrace_1496355
  have hstable : (prefixWord ++ tailWord_1496355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496355).length < 2 ^ (prefixWord ++ tailWord_1496355).sum := by decide
  have hdescent : baseEnd_1496355 < baseStart_1496355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496370 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1496370 : Nat := 118140960795 + 1496370 * 2 ^ 59
def prefixEnd_1496370 : Nat := 4983230072969 + 3 ^ 40 * 1496370 * 2
def baseEnd_1496370 : Nat := 512238031312277119462217

theorem tailTrace_1496370 : CollatzResearch.WordTrace tailWord_1496370 prefixEnd_1496370 512238031312277119462217 := by
  unfold tailWord_1496370
  simp only [CollatzResearch.WordTrace]
  refine ⟨13644274397228631123741641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36384731725943016329977709 13644274397228631123741641)
  ·
    refine ⟨10233205797921473342806231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13644274397228631123741641 10233205797921473342806231)
    ·
      refine ⟨15349808696882210014209347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10233205797921473342806231 15349808696882210014209347)
      ·
        refine ⟨23024713045323315021314021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15349808696882210014209347 23024713045323315021314021)
        ·
          refine ⟨4317133695998121566496379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23024713045323315021314021 4317133695998121566496379)
          ·
            refine ⟨6475700543997182349744569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317133695998121566496379 6475700543997182349744569)
            ·
              refine ⟨4856775407997886762308427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6475700543997182349744569 4856775407997886762308427)
              ·
                refine ⟨7285163111996830143462641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4856775407997886762308427 7285163111996830143462641)
                ·
                  refine ⟨5463872333997622607596981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7285163111996830143462641 5463872333997622607596981)
                  ·
                    refine ⟨512238031312277119462217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5463872333997622607596981 512238031312277119462217)
                    ·
                      rfl

theorem cell22_1496370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1496370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496370 prefixEnd_1496370 := by exact prefixLift 1496370
  have htrace : WordTrace (prefixWord ++ tailWord_1496370) baseStart_1496370 baseEnd_1496370 := by
    simpa [prefixWord, tailWord_1496370, baseEnd_1496370] using wordTrace_append hprefix tailTrace_1496370
  have hstable : (prefixWord ++ tailWord_1496370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496370).length < 2 ^ (prefixWord ++ tailWord_1496370).sum := by decide
  have hdescent : baseEnd_1496370 < baseStart_1496370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496432 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 2, 3]
def baseStart_1496432 : Nat := 118140960795 + 1496432 * 2 ^ 59
def prefixEnd_1496432 : Nat := 4983230072969 + 3 ^ 40 * 1496432 * 2
def baseEnd_1496432 : Nat := 512259255179329624412027

theorem tailTrace_1496432 : CollatzResearch.WordTrace tailWord_1496432 prefixEnd_1496432 512259255179329624412027 := by
  unfold tailWord_1496432
  simp only [CollatzResearch.WordTrace]
  refine ⟨27289679457344954541861775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36386239276459939389149033 27289679457344954541861775)
  ·
    refine ⟨40934519186017431812792663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27289679457344954541861775 40934519186017431812792663)
    ·
      refine ⟨61401778779026147719188995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40934519186017431812792663 61401778779026147719188995)
      ·
        refine ⟨92102668168539221578783493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61401778779026147719188995 92102668168539221578783493)
        ·
          refine ⟨17269250281601104046021905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92102668168539221578783493 17269250281601104046021905)
          ·
            refine ⟨12951937711200828034516429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17269250281601104046021905 12951937711200828034516429)
            ·
              refine ⟨4856976641700310512943661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12951937711200828034516429 4856976641700310512943661)
              ·
                refine ⟨1821366240637616442353873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4856976641700310512943661 1821366240637616442353873)
                ·
                  refine ⟨1366024680478212331765405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1821366240637616442353873 1366024680478212331765405)
                  ·
                    refine ⟨512259255179329624412027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1366024680478212331765405 512259255179329624412027)
                    ·
                      rfl

theorem cell22_1496432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2, 3].length) (baseStart_1496432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496432 prefixEnd_1496432 := by exact prefixLift 1496432
  have htrace : WordTrace (prefixWord ++ tailWord_1496432) baseStart_1496432 baseEnd_1496432 := by
    simpa [prefixWord, tailWord_1496432, baseEnd_1496432] using wordTrace_append hprefix tailTrace_1496432
  have hstable : (prefixWord ++ tailWord_1496432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496432).length < 2 ^ (prefixWord ++ tailWord_1496432).sum := by decide
  have hdescent : baseEnd_1496432 < baseStart_1496432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496462 : List Nat := [4, 1, 1, 4, 3, 9]
def baseStart_1496462 : Nat := 118140960795 + 1496462 * 2 ^ 59
def prefixEnd_1496462 : Nat := 4983230072969 + 3 ^ 40 * 1496462 * 2
def baseEnd_1496462 : Nat := 6324315120894068471135

theorem tailTrace_1496462 : CollatzResearch.WordTrace tailWord_1496462 prefixEnd_1496462 6324315120894068471135 := by
  unfold tailWord_1496462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6822556638072653025914455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36386968736387482804877093 6822556638072653025914455)
  ·
    refine ⟨10233834957108979538871683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6822556638072653025914455 10233834957108979538871683)
    ·
      refine ⟨15350752435663469308307525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10233834957108979538871683 15350752435663469308307525)
      ·
        refine ⟨2878266081686900495307661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15350752435663469308307525 2878266081686900495307661)
        ·
          refine ⟨1079349780632587685740373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2878266081686900495307661 1079349780632587685740373)
          ·
            refine ⟨6324315120894068471135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1079349780632587685740373 6324315120894068471135)
            ·
              rfl

theorem cell22_1496462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 9].length) (baseStart_1496462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496462 prefixEnd_1496462 := by exact prefixLift 1496462
  have htrace : WordTrace (prefixWord ++ tailWord_1496462) baseStart_1496462 baseEnd_1496462 := by
    simpa [prefixWord, tailWord_1496462, baseEnd_1496462] using wordTrace_append hprefix tailTrace_1496462
  have hstable : (prefixWord ++ tailWord_1496462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496462).length < 2 ^ (prefixWord ++ tailWord_1496462).sum := by decide
  have hdescent : baseEnd_1496462 < baseStart_1496462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496524 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 5]
def baseStart_1496524 : Nat := 118140960795 + 1496524 * 2 ^ 59
def prefixEnd_1496524 : Nat := 4983230072969 + 3 ^ 40 * 1496524 * 2
def baseEnd_1496524 : Nat := 170763582886490683703915

theorem tailTrace_1496524 : CollatzResearch.WordTrace tailWord_1496524 prefixEnd_1496524 170763582886490683703915 := by
  unfold tailWord_1496524
  simp only [CollatzResearch.WordTrace]
  refine ⟨27291357215178304398036313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36388476286904405864048417 27291357215178304398036313)
  ·
    refine ⟨20468517911383728298527235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27291357215178304398036313 20468517911383728298527235)
    ·
      refine ⟨30702776867075592447790853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20468517911383728298527235 30702776867075592447790853)
      ·
        refine ⟨5756770662576673583960785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30702776867075592447790853 5756770662576673583960785)
        ·
          refine ⟨4317577996932505187970589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5756770662576673583960785 4317577996932505187970589)
          ·
            refine ⟨1619091748849689445488971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4317577996932505187970589 1619091748849689445488971)
            ·
              refine ⟨2428637623274534168233457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619091748849689445488971 2428637623274534168233457)
              ·
                refine ⟨1821478217455900626175093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428637623274534168233457 1821478217455900626175093)
                ·
                  refine ⟨170763582886490683703915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1821478217455900626175093 170763582886490683703915)
                  ·
                    rfl

theorem cell22_1496524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_1496524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496524 prefixEnd_1496524 := by exact prefixLift 1496524
  have htrace : WordTrace (prefixWord ++ tailWord_1496524) baseStart_1496524 baseEnd_1496524 := by
    simpa [prefixWord, tailWord_1496524, baseEnd_1496524] using wordTrace_append hprefix tailTrace_1496524
  have hstable : (prefixWord ++ tailWord_1496524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496524).length < 2 ^ (prefixWord ++ tailWord_1496524).sum := by decide
  have hdescent : baseEnd_1496524 < baseStart_1496524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496586 : List Nat := [3, 1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_1496586 : Nat := 118140960795 + 1496586 * 2 ^ 59
def prefixEnd_1496586 : Nat := 4983230072969 + 3 ^ 40 * 1496586 * 2
def baseEnd_1496586 : Nat := 170770657508841518687185

theorem tailTrace_1496586 : CollatzResearch.WordTrace tailWord_1496586 prefixEnd_1496586 170770657508841518687185 := by
  unfold tailWord_1496586
  simp only [CollatzResearch.WordTrace]
  refine ⟨13646243939032998346207403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36389983837421328923219741 13646243939032998346207403)
  ·
    refine ⟨20469365908549497519311105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13646243939032998346207403 20469365908549497519311105)
    ·
      refine ⟨15352024431412123139483329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20469365908549497519311105 15352024431412123139483329)
      ·
        refine ⟨11514018323559092354612497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15352024431412123139483329 11514018323559092354612497)
        ·
          refine ⟨8635513742669319265959373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11514018323559092354612497 8635513742669319265959373)
          ·
            refine ⟨3238317653500994724734765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8635513742669319265959373 3238317653500994724734765)
            ·
              refine ⟨1214369120062873021775537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3238317653500994724734765 1214369120062873021775537)
              ·
                refine ⟨910776840047154766331653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1214369120062873021775537 910776840047154766331653)
                ·
                  refine ⟨170770657508841518687185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910776840047154766331653 170770657508841518687185)
                  ·
                    rfl

theorem cell22_1496586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_1496586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496586 prefixEnd_1496586 := by exact prefixLift 1496586
  have htrace : WordTrace (prefixWord ++ tailWord_1496586) baseStart_1496586 baseEnd_1496586 := by
    simpa [prefixWord, tailWord_1496586, baseEnd_1496586] using wordTrace_append hprefix tailTrace_1496586
  have hstable : (prefixWord ++ tailWord_1496586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496586).length < 2 ^ (prefixWord ++ tailWord_1496586).sum := by decide
  have hdescent : baseEnd_1496586 < baseStart_1496586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496597 : List Nat := [1, 3, 2, 1, 3, 3, 2, 7]
def baseStart_1496597 : Nat := 118140960795 + 1496597 * 2 ^ 59
def prefixEnd_1496597 : Nat := 4983230072969 + 3 ^ 40 * 1496597 * 2
def baseEnd_1496597 : Nat := 56923970894591577115169

theorem tailTrace_1496597 : CollatzResearch.WordTrace tailWord_1496597 prefixEnd_1496597 56923970894591577115169 := by
  unfold tailWord_1496597
  simp only [CollatzResearch.WordTrace]
  refine ⟨54585376959092142263480045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36390251306061428175653363 54585376959092142263480045)
  ·
    refine ⟨20469516359659553348805017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54585376959092142263480045 20469516359659553348805017)
    ·
      refine ⟨15352137269744665011603763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20469516359659553348805017 15352137269744665011603763)
      ·
        refine ⟨23028205904616997517405645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15352137269744665011603763 23028205904616997517405645)
        ·
          refine ⟨8635577214231374069027117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23028205904616997517405645 8635577214231374069027117)
          ·
            refine ⟨3238341455336765275885169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8635577214231374069027117 3238341455336765275885169)
            ·
              refine ⟨2428756091502573956913877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3238341455336765275885169 2428756091502573956913877)
              ·
                refine ⟨56923970894591577115169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2428756091502573956913877 56923970894591577115169)
                ·
                  rfl

theorem cell22_1496597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 7].length) (baseStart_1496597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496597 prefixEnd_1496597 := by exact prefixLift 1496597
  have htrace : WordTrace (prefixWord ++ tailWord_1496597) baseStart_1496597 baseEnd_1496597 := by
    simpa [prefixWord, tailWord_1496597, baseEnd_1496597] using wordTrace_append hprefix tailTrace_1496597
  have hstable : (prefixWord ++ tailWord_1496597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496597).length < 2 ^ (prefixWord ++ tailWord_1496597).sum := by decide
  have hdescent : baseEnd_1496597 < baseStart_1496597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496616 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1496616 : Nat := 118140960795 + 1496616 * 2 ^ 59
def prefixEnd_1496616 : Nat := 4983230072969 + 3 ^ 40 * 1496616 * 2
def baseEnd_1496616 : Nat := 512322242139614477811463

theorem tailTrace_1496616 : CollatzResearch.WordTrace tailWord_1496616 prefixEnd_1496616 512322242139614477811463 := by
  unfold tailWord_1496616
  simp only [CollatzResearch.WordTrace]
  refine ⟨27293034973011654254210851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36390713297348872338947801 27293034973011654254210851)
  ·
    refine ⟨40939552459517481381316277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27293034973011654254210851 40939552459517481381316277)
    ·
      refine ⟨3838083043079763879498401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40939552459517481381316277 3838083043079763879498401)
      ·
        refine ⟨2878562282309822909623801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3838083043079763879498401 2878562282309822909623801)
        ·
          refine ⟨2158921711732367182217851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2878562282309822909623801 2158921711732367182217851)
          ·
            refine ⟨3238382567598550773326777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158921711732367182217851 3238382567598550773326777)
            ·
              refine ⟨2428786925698913079995083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3238382567598550773326777 2428786925698913079995083)
              ·
                refine ⟨3643180388548369619992625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2428786925698913079995083 3643180388548369619992625)
                ·
                  refine ⟨2732385291411277214994469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3643180388548369619992625 2732385291411277214994469)
                  ·
                    refine ⟨512322242139614477811463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2732385291411277214994469 512322242139614477811463)
                    ·
                      rfl

theorem cell22_1496616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1496616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496616 prefixEnd_1496616 := by exact prefixLift 1496616
  have htrace : WordTrace (prefixWord ++ tailWord_1496616) baseStart_1496616 baseEnd_1496616 := by
    simpa [prefixWord, tailWord_1496616, baseEnd_1496616] using wordTrace_append hprefix tailTrace_1496616
  have hstable : (prefixWord ++ tailWord_1496616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496616).length < 2 ^ (prefixWord ++ tailWord_1496616).sum := by decide
  have hdescent : baseEnd_1496616 < baseStart_1496616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496657 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_1496657 : Nat := 118140960795 + 1496657 * 2 ^ 59
def prefixEnd_1496657 : Nat := 4983230072969 + 3 ^ 40 * 1496657 * 2
def baseEnd_1496657 : Nat := 512336277277504037536337

theorem tailTrace_1496657 : CollatzResearch.WordTrace tailWord_1496657 prefixEnd_1496657 512336277277504037536337 := by
  unfold tailWord_1496657
  simp only [CollatzResearch.WordTrace]
  refine ⟨54587565338874772510664225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36391710225916515007109483 54587565338874772510664225)
  ·
    refine ⟨40940674004156079382998169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54587565338874772510664225 40940674004156079382998169)
    ·
      refine ⟨30705505503117059537248627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40940674004156079382998169 30705505503117059537248627)
      ·
        refine ⟨46058258254675589305872941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30705505503117059537248627 46058258254675589305872941)
        ·
          refine ⟨17271846845503345989702353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46058258254675589305872941 17271846845503345989702353)
          ·
            refine ⟨12953885134127509492276765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17271846845503345989702353 12953885134127509492276765)
            ·
              refine ⟨4857706925297816059603787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12953885134127509492276765 4857706925297816059603787)
              ·
                refine ⟨7286560387946724089405681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857706925297816059603787 7286560387946724089405681)
                ·
                  refine ⟨5464920290960043067054261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7286560387946724089405681 5464920290960043067054261)
                  ·
                    refine ⟨512336277277504037536337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5464920290960043067054261 512336277277504037536337)
                    ·
                      rfl

theorem cell22_1496657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_1496657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496657 prefixEnd_1496657 := by exact prefixLift 1496657
  have htrace : WordTrace (prefixWord ++ tailWord_1496657) baseStart_1496657 baseEnd_1496657 := by
    simpa [prefixWord, tailWord_1496657, baseEnd_1496657] using wordTrace_append hprefix tailTrace_1496657
  have hstable : (prefixWord ++ tailWord_1496657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496657).length < 2 ^ (prefixWord ++ tailWord_1496657).sum := by decide
  have hdescent : baseEnd_1496657 < baseStart_1496657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496704 : List Nat := [2, 1, 1, 2, 1, 4, 1, 6, 4]
def baseStart_1496704 : Nat := 118140960795 + 1496704 * 2 ^ 59
def prefixEnd_1496704 : Nat := 4983230072969 + 3 ^ 40 * 1496704 * 2
def baseEnd_1496704 : Nat := 170784122112670527203731

theorem tailTrace_1496704 : CollatzResearch.WordTrace tailWord_1496704 prefixEnd_1496704 170784122112670527203731 := by
  unfold tailWord_1496704
  simp only [CollatzResearch.WordTrace]
  refine ⟨27294639784852249768812583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36392853046469666358416777 27294639784852249768812583)
  ·
    refine ⟨40941959677278374653218875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27294639784852249768812583 40941959677278374653218875)
    ·
      refine ⟨61412939515917561979828313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40941959677278374653218875 61412939515917561979828313)
      ·
        refine ⟨46059704636938171484871235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61412939515917561979828313 46059704636938171484871235)
        ·
          refine ⟨69089556955407257227306853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46059704636938171484871235 69089556955407257227306853)
          ·
            refine ⟨12954291929138860730120035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69089556955407257227306853 12954291929138860730120035)
            ·
              refine ⟨19431437893708291095180053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12954291929138860730120035 19431437893708291095180053)
              ·
                refine ⟨910848651267576145086565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19431437893708291095180053 910848651267576145086565)
                ·
                  refine ⟨170784122112670527203731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910848651267576145086565 170784122112670527203731)
                  ·
                    rfl

theorem cell22_1496704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 4].length) (baseStart_1496704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496704 prefixEnd_1496704 := by exact prefixLift 1496704
  have htrace : WordTrace (prefixWord ++ tailWord_1496704) baseStart_1496704 baseEnd_1496704 := by
    simpa [prefixWord, tailWord_1496704, baseEnd_1496704] using wordTrace_append hprefix tailTrace_1496704
  have hstable : (prefixWord ++ tailWord_1496704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496704).length < 2 ^ (prefixWord ++ tailWord_1496704).sum := by decide
  have hdescent : baseEnd_1496704 < baseStart_1496704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496856 : List Nat := [2, 1, 2, 3, 1, 1, 3, 5, 4]
def baseStart_1496856 : Nat := 118140960795 + 1496856 * 2 ^ 59
def prefixEnd_1496856 : Nat := 4983230072969 + 3 ^ 40 * 1496856 * 2
def baseEnd_1496856 : Nat := 170801466348111283936909

theorem tailTrace_1496856 : CollatzResearch.WordTrace tailWord_1496856 prefixEnd_1496856 170801466348111283936909 := by
  unfold tailWord_1496856
  simp only [CollatzResearch.WordTrace]
  refine ⟨27297411732576914748579211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36396548976769219664772281 27297411732576914748579211)
  ·
    refine ⟨40946117598865372122868817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27297411732576914748579211 40946117598865372122868817)
    ·
      refine ⟨30709588199149029092151613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40946117598865372122868817 30709588199149029092151613)
      ·
        refine ⟨11516095574680885909556855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30709588199149029092151613 11516095574680885909556855)
        ·
          refine ⟨17274143362021328864335283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11516095574680885909556855 17274143362021328864335283)
          ·
            refine ⟨25911215043031993296502925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17274143362021328864335283 25911215043031993296502925)
            ·
              refine ⟨9716705641136997486188597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25911215043031993296502925 9716705641136997486188597)
              ·
                refine ⟨910941153856593514330181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9716705641136997486188597 910941153856593514330181)
                ·
                  refine ⟨170801466348111283936909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910941153856593514330181 170801466348111283936909)
                  ·
                    rfl

theorem cell22_1496856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 4].length) (baseStart_1496856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496856 prefixEnd_1496856 := by exact prefixLift 1496856
  have htrace : WordTrace (prefixWord ++ tailWord_1496856) baseStart_1496856 baseEnd_1496856 := by
    simpa [prefixWord, tailWord_1496856, baseEnd_1496856] using wordTrace_append hprefix tailTrace_1496856
  have hstable : (prefixWord ++ tailWord_1496856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496856).length < 2 ^ (prefixWord ++ tailWord_1496856).sum := by decide
  have hdescent : baseEnd_1496856 < baseStart_1496856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496858 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 1, 4]
def baseStart_1496858 : Nat := 118140960795 + 1496858 * 2 ^ 59
def prefixEnd_1496858 : Nat := 4983230072969 + 3 ^ 40 * 1496858 * 2
def baseEnd_1496858 : Nat := 512405083685206513260721

theorem tailTrace_1496858 : CollatzResearch.WordTrace tailWord_1496858 prefixEnd_1496858 512405083685206513260721 := by
  unfold tailWord_1496858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13648724102786645959682807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36396597607431055892487485 13648724102786645959682807)
  ·
    refine ⟨20473086154179968939524211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13648724102786645959682807 20473086154179968939524211)
    ·
      refine ⟨30709629231269953409286317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20473086154179968939524211 30709629231269953409286317)
      ·
        refine ⟨11516110961726232528482369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30709629231269953409286317 11516110961726232528482369)
        ·
          refine ⟨8637083221294674396361777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11516110961726232528482369 8637083221294674396361777)
          ·
            refine ⟨6477812415971005797271333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8637083221294674396361777 6477812415971005797271333)
            ·
              refine ⟨1214589827994563586988375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6477812415971005797271333 1214589827994563586988375)
              ·
                refine ⟨1821884741991845380482563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214589827994563586988375 1821884741991845380482563)
                ·
                  refine ⟨2732827112987768070723845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821884741991845380482563 2732827112987768070723845)
                  ·
                    refine ⟨512405083685206513260721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2732827112987768070723845 512405083685206513260721)
                    ·
                      rfl

theorem cell22_1496858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_1496858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496858 prefixEnd_1496858 := by exact prefixLift 1496858
  have htrace : WordTrace (prefixWord ++ tailWord_1496858) baseStart_1496858 baseEnd_1496858 := by
    simpa [prefixWord, tailWord_1496858, baseEnd_1496858] using wordTrace_append hprefix tailTrace_1496858
  have hstable : (prefixWord ++ tailWord_1496858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496858).length < 2 ^ (prefixWord ++ tailWord_1496858).sum := by decide
  have hdescent : baseEnd_1496858 < baseStart_1496858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496862 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1496862 : Nat := 118140960795 + 1496862 * 2 ^ 59
def prefixEnd_1496862 : Nat := 4983230072969 + 3 ^ 40 * 1496862 * 2
def baseEnd_1496862 : Nat := 170802150988983945386903

theorem tailTrace_1496862 : CollatzResearch.WordTrace tailWord_1496862 prefixEnd_1496862 170802150988983945386903 := by
  unfold tailWord_1496862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6824380287891511565234605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36396694868754728347917893 6824380287891511565234605)
  ·
    refine ⟨2559142607959316836962977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6824380287891511565234605 2559142607959316836962977)
    ·
      refine ⟨1919356955969487627722233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2559142607959316836962977 1919356955969487627722233)
      ·
        refine ⟨1439517716977115720791675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1919356955969487627722233 1439517716977115720791675)
        ·
          refine ⟨2159276575465673581187513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439517716977115720791675 2159276575465673581187513)
          ·
            refine ⟨1619457431599255185890635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2159276575465673581187513 1619457431599255185890635)
            ·
              refine ⟨2429186147398882778835953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619457431599255185890635 2429186147398882778835953)
              ·
                refine ⟨1821889610549162084126965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2429186147398882778835953 1821889610549162084126965)
                ·
                  refine ⟨170802150988983945386903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1821889610549162084126965 170802150988983945386903)
                  ·
                    rfl

theorem cell22_1496862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1496862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496862 prefixEnd_1496862 := by exact prefixLift 1496862
  have htrace : WordTrace (prefixWord ++ tailWord_1496862) baseStart_1496862 baseEnd_1496862 := by
    simpa [prefixWord, tailWord_1496862, baseEnd_1496862] using wordTrace_append hprefix tailTrace_1496862
  have hstable : (prefixWord ++ tailWord_1496862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496862).length < 2 ^ (prefixWord ++ tailWord_1496862).sum := by decide
  have hdescent : baseEnd_1496862 < baseStart_1496862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496929 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 7]
def baseStart_1496929 : Nat := 118140960795 + 1496929 * 2 ^ 59
def prefixEnd_1496929 : Nat := 4983230072969 + 3 ^ 40 * 1496929 * 2
def baseEnd_1496929 : Nat := 170809796145395331578501

theorem tailTrace_1496929 : CollatzResearch.WordTrace tailWord_1496929 prefixEnd_1496929 170809796145395331578501 := by
  unfold tailWord_1496929
  simp only [CollatzResearch.WordTrace]
  refine ⟨54597485993889362964565841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36398323995926241976377227 54597485993889362964565841)
  ·
    refine ⟨40948114495417022223424381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54597485993889362964565841 40948114495417022223424381)
    ·
      refine ⟨15355542935781383333784143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40948114495417022223424381 15355542935781383333784143)
      ·
        refine ⟨23033314403672075000676215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15355542935781383333784143 23033314403672075000676215)
        ·
          refine ⟨34549971605508112501014323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23033314403672075000676215 34549971605508112501014323)
          ·
            refine ⟨51824957408262168751521485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34549971605508112501014323 51824957408262168751521485)
            ·
              refine ⟨19434359028098313281820557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51824957408262168751521485 19434359028098313281820557)
              ·
                refine ⟨7287884635536867480682709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19434359028098313281820557 7287884635536867480682709)
                ·
                  refine ⟨170809796145395331578501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7287884635536867480682709 170809796145395331578501)
                  ·
                    rfl

theorem cell22_1496929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_1496929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496929 prefixEnd_1496929 := by exact prefixLift 1496929
  have htrace : WordTrace (prefixWord ++ tailWord_1496929) baseStart_1496929 baseEnd_1496929 := by
    simpa [prefixWord, tailWord_1496929, baseEnd_1496929] using wordTrace_append hprefix tailTrace_1496929
  have hstable : (prefixWord ++ tailWord_1496929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496929).length < 2 ^ (prefixWord ++ tailWord_1496929).sum := by decide
  have hdescent : baseEnd_1496929 < baseStart_1496929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496944 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_1496944 : Nat := 118140960795 + 1496944 * 2 ^ 59
def prefixEnd_1496944 : Nat := 4983230072969 + 3 ^ 40 * 1496944 * 2
def baseEnd_1496944 : Nat := 512434523242730955610457

theorem tailTrace_1496944 : CollatzResearch.WordTrace tailWord_1496944 prefixEnd_1496944 512434523242730955610457 := by
  unfold tailWord_1496944
  simp only [CollatzResearch.WordTrace]
  refine ⟨27299016544417510263180943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36398688725890013684241257 27299016544417510263180943)
  ·
    refine ⟨40948524816626265394771415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27299016544417510263180943 40948524816626265394771415)
    ·
      refine ⟨61422787224939398092157123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40948524816626265394771415 61422787224939398092157123)
      ·
        refine ⟨92134180837409097138235685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61422787224939398092157123 92134180837409097138235685)
        ·
          refine ⟨17275158907014205713419191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92134180837409097138235685 17275158907014205713419191)
          ·
            refine ⟨25912738360521308570128787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17275158907014205713419191 25912738360521308570128787)
            ·
              refine ⟨38869107540781962855193181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25912738360521308570128787 38869107540781962855193181)
              ·
                refine ⟨14575915327793236070697443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38869107540781962855193181 14575915327793236070697443)
                ·
                  refine ⟨21863872991689854106046165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14575915327793236070697443 21863872991689854106046165)
                  ·
                    refine ⟨512434523242730955610457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21863872991689854106046165 512434523242730955610457)
                    ·
                      rfl

theorem cell22_1496944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_1496944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1496944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1496944 prefixEnd_1496944 := by exact prefixLift 1496944
  have htrace : WordTrace (prefixWord ++ tailWord_1496944) baseStart_1496944 baseEnd_1496944 := by
    simpa [prefixWord, tailWord_1496944, baseEnd_1496944] using wordTrace_append hprefix tailTrace_1496944
  have hstable : (prefixWord ++ tailWord_1496944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496944).length < 2 ^ (prefixWord ++ tailWord_1496944).sum := by decide
  have hdescent : baseEnd_1496944 < baseStart_1496944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497036 : List Nat := [2, 2, 1, 4, 1, 3, 9]
def baseStart_1497036 : Nat := 118140960795 + 1497036 * 2 ^ 59
def prefixEnd_1497036 : Nat := 4983230072969 + 3 ^ 40 * 1497036 * 2
def baseEnd_1497036 : Nat := 18980222841587903048525

theorem tailTrace_1497036 : CollatzResearch.WordTrace tailWord_1497036 prefixEnd_1497036 18980222841587903048525 := by
  unfold tailWord_1497036
  simp only [CollatzResearch.WordTrace]
  refine ⟨27300694302250860119355481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36400925736334480159140641 27300694302250860119355481)
  ·
    refine ⟨20475520726688145089516611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27300694302250860119355481 20475520726688145089516611)
    ·
      refine ⟨30713281090032217634274917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20475520726688145089516611 30713281090032217634274917)
      ·
        refine ⟨5758740204381040806426547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30713281090032217634274917 5758740204381040806426547)
        ·
          refine ⟨8638110306571561209639821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5758740204381040806426547 8638110306571561209639821)
          ·
            refine ⟨3239291364964335453614933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8638110306571561209639821 3239291364964335453614933)
            ·
              refine ⟨18980222841587903048525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3239291364964335453614933 18980222841587903048525)
              ·
                rfl

theorem cell22_1497036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 9].length) (baseStart_1497036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497036 prefixEnd_1497036 := by exact prefixLift 1497036
  have htrace : WordTrace (prefixWord ++ tailWord_1497036) baseStart_1497036 baseEnd_1497036 := by
    simpa [prefixWord, tailWord_1497036, baseEnd_1497036] using wordTrace_append hprefix tailTrace_1497036
  have hstable : (prefixWord ++ tailWord_1497036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497036).length < 2 ^ (prefixWord ++ tailWord_1497036).sum := by decide
  have hdescent : baseEnd_1497036 < baseStart_1497036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497070 : List Nat := [4, 1, 2, 1, 3, 3, 2, 6]
def baseStart_1497070 : Nat := 118140960795 + 1497070 * 2 ^ 59
def prefixEnd_1497070 : Nat := 4983230072969 + 3 ^ 40 * 1497070 * 2
def baseEnd_1497070 : Nat := 56941961735300958551119

theorem tailTrace_1497070 : CollatzResearch.WordTrace tailWord_1497070 prefixEnd_1497070 56941961735300958551119 := by
  unfold tailWord_1497070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6825328585797318005681083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36401752457585696030299109 6825328585797318005681083)
  ·
    refine ⟨10237992878695977008521625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6825328585797318005681083 10237992878695977008521625)
    ·
      refine ⟨7678494659021982756391219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10237992878695977008521625 7678494659021982756391219)
      ·
        refine ⟨11517741988532974134586829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678494659021982756391219 11517741988532974134586829)
        ·
          refine ⟨4319153245699865300470061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11517741988532974134586829 4319153245699865300470061)
          ·
            refine ⟨1619682467137449487676273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4319153245699865300470061 1619682467137449487676273)
            ·
              refine ⟨1214761850353087115757205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619682467137449487676273 1214761850353087115757205)
              ·
                refine ⟨56941961735300958551119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1214761850353087115757205 56941961735300958551119)
                ·
                  rfl

theorem cell22_1497070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_1497070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497070 prefixEnd_1497070 := by exact prefixLift 1497070
  have htrace : WordTrace (prefixWord ++ tailWord_1497070) baseStart_1497070 baseEnd_1497070 := by
    simpa [prefixWord, tailWord_1497070, baseEnd_1497070] using wordTrace_append hprefix tailTrace_1497070
  have hstable : (prefixWord ++ tailWord_1497070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497070).length < 2 ^ (prefixWord ++ tailWord_1497070).sum := by decide
  have hdescent : baseEnd_1497070 < baseStart_1497070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497081 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 7]
def baseStart_1497081 : Nat := 118140960795 + 1497081 * 2 ^ 59
def prefixEnd_1497081 : Nat := 4983230072969 + 3 ^ 40 * 1497081 * 2
def baseEnd_1497081 : Nat := 170827140380836088311679

theorem tailTrace_1497081 : CollatzResearch.WordTrace tailWord_1497081 prefixEnd_1497081 170827140380836088311679 := by
  unfold tailWord_1497081
  simp only [CollatzResearch.WordTrace]
  refine ⟨54603029889338692924099097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36402019926225795282732731 54603029889338692924099097)
  ·
    refine ⟨40952272417004019693074323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54603029889338692924099097 40952272417004019693074323)
    ·
      refine ⟨61428408625506029539611485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40952272417004019693074323 61428408625506029539611485)
      ·
        refine ⟨23035653234564761077354307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61428408625506029539611485 23035653234564761077354307)
        ·
          refine ⟨34553479851847141616031461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23035653234564761077354307 34553479851847141616031461)
          ·
            refine ⟨6478777472221339053005899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34553479851847141616031461 6478777472221339053005899)
            ·
              refine ⟨9718166208332008579508849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478777472221339053005899 9718166208332008579508849)
              ·
                refine ⟨7288624656249006434631637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9718166208332008579508849 7288624656249006434631637)
                ·
                  refine ⟨170827140380836088311679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7288624656249006434631637 170827140380836088311679)
                  ·
                    rfl

theorem cell22_1497081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_1497081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497081 prefixEnd_1497081 := by exact prefixLift 1497081
  have htrace : WordTrace (prefixWord ++ tailWord_1497081) baseStart_1497081 baseEnd_1497081 := by
    simpa [prefixWord, tailWord_1497081, baseEnd_1497081] using wordTrace_append hprefix tailTrace_1497081
  have hstable : (prefixWord ++ tailWord_1497081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497081).length < 2 ^ (prefixWord ++ tailWord_1497081).sum := by decide
  have hdescent : baseEnd_1497081 < baseStart_1497081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497108 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1497108 : Nat := 118140960795 + 1497108 * 2 ^ 59
def prefixEnd_1497108 : Nat := 4983230072969 + 3 ^ 40 * 1497108 * 2
def baseEnd_1497108 : Nat := 512490663794289194509955

theorem tailTrace_1497108 : CollatzResearch.WordTrace tailWord_1497108 prefixEnd_1497108 512490663794289194509955 := by
  unfold tailWord_1497108
  simp only [CollatzResearch.WordTrace]
  refine ⟨27302007330120438267665989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36402676440160584356887985 27302007330120438267665989)
  ·
    refine ⟨5119126374397582175187373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27302007330120438267665989 5119126374397582175187373)
    ·
      refine ⟨1919672390399093315695265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5119126374397582175187373 1919672390399093315695265)
      ·
        refine ⟨1439754292799319986771449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1919672390399093315695265 1439754292799319986771449)
        ·
          refine ⟨1079815719599489990078587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1439754292799319986771449 1079815719599489990078587)
          ·
            refine ⟨1619723579399234985117881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079815719599489990078587 1619723579399234985117881)
            ·
              refine ⟨1214792684549426238838411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619723579399234985117881 1214792684549426238838411)
              ·
                refine ⟨1822189026824139358257617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214792684549426238838411 1822189026824139358257617)
                ·
                  refine ⟨1366641770118104518693213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1822189026824139358257617 1366641770118104518693213)
                  ·
                    refine ⟨512490663794289194509955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1366641770118104518693213 512490663794289194509955)
                    ·
                      rfl

theorem cell22_1497108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1497108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497108 prefixEnd_1497108 := by exact prefixLift 1497108
  have htrace : WordTrace (prefixWord ++ tailWord_1497108) baseStart_1497108 baseEnd_1497108 := by
    simpa [prefixWord, tailWord_1497108, baseEnd_1497108] using wordTrace_append hprefix tailTrace_1497108
  have hstable : (prefixWord ++ tailWord_1497108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497108).length < 2 ^ (prefixWord ++ tailWord_1497108).sum := by decide
  have hdescent : baseEnd_1497108 < baseStart_1497108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497175 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 2, 3]
def baseStart_1497175 : Nat := 118140960795 + 1497175 * 2 ^ 59
def prefixEnd_1497175 : Nat := 4983230072969 + 3 ^ 40 * 1497175 * 2
def baseEnd_1497175 : Nat := 512513599263523353084749

theorem tailTrace_1497175 : CollatzResearch.WordTrace tailWord_1497175 prefixEnd_1497175 512513599263523353084749 := by
  unfold tailWord_1497175
  simp only [CollatzResearch.WordTrace]
  refine ⟨54606458350998146978020979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36404305567332097985347319 54606458350998146978020979)
  ·
    refine ⟨81909687526497220467031469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54606458350998146978020979 81909687526497220467031469)
    ·
      refine ⟨30716132822436457675136801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81909687526497220467031469 30716132822436457675136801)
      ·
        refine ⟨23037099616827343256352601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30716132822436457675136801 23037099616827343256352601)
        ·
          refine ⟨17277824712620507442264451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23037099616827343256352601 17277824712620507442264451)
          ·
            refine ⟨25916737068930761163396677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17277824712620507442264451 25916737068930761163396677)
            ·
              refine ⟨4859388200424517718136877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25916737068930761163396677 4859388200424517718136877)
              ·
                refine ⟨1822270575159194144301329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4859388200424517718136877 1822270575159194144301329)
                ·
                  refine ⟨1366702931369395608225997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1822270575159194144301329 1366702931369395608225997)
                  ·
                    refine ⟨512513599263523353084749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1366702931369395608225997 512513599263523353084749)
                    ·
                      rfl

theorem cell22_1497175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_1497175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497175 prefixEnd_1497175 := by exact prefixLift 1497175
  have htrace : WordTrace (prefixWord ++ tailWord_1497175) baseStart_1497175 baseEnd_1497175 := by
    simpa [prefixWord, tailWord_1497175, baseEnd_1497175] using wordTrace_append hprefix tailTrace_1497175
  have hstable : (prefixWord ++ tailWord_1497175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497175).length < 2 ^ (prefixWord ++ tailWord_1497175).sum := by decide
  have hdescent : baseEnd_1497175 < baseStart_1497175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497250 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1497250 : Nat := 118140960795 + 1497250 * 2 ^ 59
def prefixEnd_1497250 : Nat := 4983230072969 + 3 ^ 40 * 1497250 * 2
def baseEnd_1497250 : Nat := 170846424432082719153173

theorem tailTrace_1497250 : CollatzResearch.WordTrace tailWord_1497250 prefixEnd_1497250 170846424432082719153173 := by
  unfold tailWord_1497250
  simp only [CollatzResearch.WordTrace]
  refine ⟨13652298456431608696750301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36406129217150956524667469 13652298456431608696750301)
  ·
    refine ⟨5119611921161853261281363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13652298456431608696750301 5119611921161853261281363)
    ·
      refine ⟨7679417881742779891922045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5119611921161853261281363 7679417881742779891922045)
      ·
        refine ⟨2879781705653542459470767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7679417881742779891922045 2879781705653542459470767)
        ·
          refine ⟨4319672558480313689206151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879781705653542459470767 4319672558480313689206151)
          ·
            refine ⟨6479508837720470533809227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319672558480313689206151 6479508837720470533809227)
            ·
              refine ⟨9719263256580705800713841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479508837720470533809227 9719263256580705800713841)
              ·
                refine ⟨7289447442435529350535381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9719263256580705800713841 7289447442435529350535381)
                ·
                  refine ⟨170846424432082719153173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7289447442435529350535381 170846424432082719153173)
                  ·
                    rfl

theorem cell22_1497250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1497250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497250 prefixEnd_1497250 := by exact prefixLift 1497250
  have htrace : WordTrace (prefixWord ++ tailWord_1497250) baseStart_1497250 baseEnd_1497250 := by
    simpa [prefixWord, tailWord_1497250, baseEnd_1497250] using wordTrace_append hprefix tailTrace_1497250
  have hstable : (prefixWord ++ tailWord_1497250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497250).length < 2 ^ (prefixWord ++ tailWord_1497250).sum := by decide
  have hdescent : baseEnd_1497250 < baseStart_1497250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497263 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 5, 4]
def baseStart_1497263 : Nat := 118140960795 + 1497263 * 2 ^ 59
def prefixEnd_1497263 : Nat := 4983230072969 + 3 ^ 40 * 1497263 * 2
def baseEnd_1497263 : Nat := 512543723461920456884479

theorem tailTrace_1497263 : CollatzResearch.WordTrace tailWord_1497263 prefixEnd_1497263 512543723461920456884479 := by
  unfold tailWord_1497263
  simp only [CollatzResearch.WordTrace]
  refine ⟨54609667974679338007224443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36406445316452892004816295 54609667974679338007224443)
  ·
    refine ⟨81914501962019007010836665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54609667974679338007224443 81914501962019007010836665)
    ·
      refine ⟨61435876471514255258127499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81914501962019007010836665 61435876471514255258127499)
      ·
        refine ⟨92153814707271382887191249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61435876471514255258127499 92153814707271382887191249)
        ·
          refine ⟨69115361030453537165393437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92153814707271382887191249 69115361030453537165393437)
          ·
            refine ⟨25918260386420076437022539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69115361030453537165393437 25918260386420076437022539)
            ·
              refine ⟨38877390579630114655533809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25918260386420076437022539 38877390579630114655533809)
              ·
                refine ⟨29158042934722585991650357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38877390579630114655533809 29158042934722585991650357)
                ·
                  refine ⟨2733566525130242436717221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29158042934722585991650357 2733566525130242436717221)
                  ·
                    refine ⟨512543723461920456884479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2733566525130242436717221 512543723461920456884479)
                    ·
                      rfl

theorem cell22_1497263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_1497263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497263 prefixEnd_1497263 := by exact prefixLift 1497263
  have htrace : WordTrace (prefixWord ++ tailWord_1497263) baseStart_1497263 baseEnd_1497263 := by
    simpa [prefixWord, tailWord_1497263, baseEnd_1497263] using wordTrace_append hprefix tailTrace_1497263
  have hstable : (prefixWord ++ tailWord_1497263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497263).length < 2 ^ (prefixWord ++ tailWord_1497263).sum := by decide
  have hdescent : baseEnd_1497263 < baseStart_1497263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497284 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 5]
def baseStart_1497284 : Nat := 118140960795 + 1497284 * 2 ^ 59
def prefixEnd_1497284 : Nat := 4983230072969 + 3 ^ 40 * 1497284 * 2
def baseEnd_1497284 : Nat := 170850304063694467369805

theorem tailTrace_1497284 : CollatzResearch.WordTrace tailWord_1497284 prefixEnd_1497284 170850304063694467369805 := by
  unfold tailWord_1497284
  simp only [CollatzResearch.WordTrace]
  refine ⟨27305216953801629296869453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36406955938402172395825937 27305216953801629296869453)
  ·
    refine ⟨10239456357675610986326045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27305216953801629296869453 10239456357675610986326045)
    ·
      refine ⟨3839796134128354119872267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10239456357675610986326045 3839796134128354119872267)
      ·
        refine ⟨5759694201192531179808401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3839796134128354119872267 5759694201192531179808401)
        ·
          refine ⟨4319770650894398384856301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5759694201192531179808401 4319770650894398384856301)
          ·
            refine ⟨1619913994085399394321113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4319770650894398384856301 1619913994085399394321113)
            ·
              refine ⟨1214935495564049545740835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619913994085399394321113 1214935495564049545740835)
              ·
                refine ⟨1822403243346074318611253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214935495564049545740835 1822403243346074318611253)
                ·
                  refine ⟨170850304063694467369805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1822403243346074318611253 170850304063694467369805)
                  ·
                    rfl

theorem cell22_1497284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_1497284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497284 prefixEnd_1497284 := by exact prefixLift 1497284
  have htrace : WordTrace (prefixWord ++ tailWord_1497284) baseStart_1497284 baseEnd_1497284 := by
    simpa [prefixWord, tailWord_1497284, baseEnd_1497284] using wordTrace_append hprefix tailTrace_1497284
  have hstable : (prefixWord ++ tailWord_1497284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497284).length < 2 ^ (prefixWord ++ tailWord_1497284).sum := by decide
  have hdescent : baseEnd_1497284 < baseStart_1497284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497327 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 2, 3]
def baseStart_1497327 : Nat := 118140960795 + 1497327 * 2 ^ 59
def prefixEnd_1497327 : Nat := 4983230072969 + 3 ^ 40 * 1497327 * 2
def baseEnd_1497327 : Nat := 512565631969845623284283

theorem tailTrace_1497327 : CollatzResearch.WordTrace tailWord_1497327 prefixEnd_1497327 512565631969845623284283 := by
  unfold tailWord_1497327
  simp only [CollatzResearch.WordTrace]
  refine ⟨54612002246447476937554235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36408001497631651291702823 54612002246447476937554235)
  ·
    refine ⟨81918003369671215406331353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54612002246447476937554235 81918003369671215406331353)
    ·
      refine ⟨61438502527253411554748515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81918003369671215406331353 61438502527253411554748515)
      ·
        refine ⟨92157753790880117332122773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61438502527253411554748515 92157753790880117332122773)
        ·
          refine ⟨4319894708947505499943255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92157753790880117332122773 4319894708947505499943255)
          ·
            refine ⟨6479842063421258249914883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319894708947505499943255 6479842063421258249914883)
            ·
              refine ⟨9719763095131887374872325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479842063421258249914883 9719763095131887374872325)
              ·
                refine ⟨1822455580337228882788561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9719763095131887374872325 1822455580337228882788561)
                ·
                  refine ⟨1366841685252921662091421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1822455580337228882788561 1366841685252921662091421)
                  ·
                    refine ⟨512565631969845623284283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1366841685252921662091421 512565631969845623284283)
                    ·
                      rfl

theorem cell22_1497327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 3].length) (baseStart_1497327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497327 prefixEnd_1497327 := by exact prefixLift 1497327
  have htrace : WordTrace (prefixWord ++ tailWord_1497327) baseStart_1497327 baseEnd_1497327 := by
    simpa [prefixWord, tailWord_1497327, baseEnd_1497327] using wordTrace_append hprefix tailTrace_1497327
  have hstable : (prefixWord ++ tailWord_1497327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497327).length < 2 ^ (prefixWord ++ tailWord_1497327).sum := by decide
  have hdescent : baseEnd_1497327 < baseStart_1497327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497340 : List Nat := [2, 2, 2, 1, 4, 1, 3, 7]
def baseStart_1497340 : Nat := 118140960795 + 1497340 * 2 ^ 59
def prefixEnd_1497340 : Nat := 4983230072969 + 3 ^ 40 * 1497340 * 2
def baseEnd_1497340 : Nat := 56952231348390880301027

theorem tailTrace_1497340 : CollatzResearch.WordTrace tailWord_1497340 prefixEnd_1497340 56952231348390880301027 := by
  unfold tailWord_1497340
  simp only [CollatzResearch.WordTrace]
  refine ⟨27306238197700190078888737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36408317596933586771851649 27306238197700190078888737)
  ·
    refine ⟨20479678648275142559166553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27306238197700190078888737 20479678648275142559166553)
    ·
      refine ⟨15359758986206356919374915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20479678648275142559166553 15359758986206356919374915)
      ·
        refine ⟨23039638479309535379062373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15359758986206356919374915 23039638479309535379062373)
        ·
          refine ⟨4319932214870537883574195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23039638479309535379062373 4319932214870537883574195)
          ·
            refine ⟨6479898322305806825361293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319932214870537883574195 6479898322305806825361293)
            ·
              refine ⟨2429961870864677559510485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6479898322305806825361293 2429961870864677559510485)
              ·
                refine ⟨56952231348390880301027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2429961870864677559510485 56952231348390880301027)
                ·
                  rfl

theorem cell22_1497340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 7].length) (baseStart_1497340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497340 prefixEnd_1497340 := by exact prefixLift 1497340
  have htrace : WordTrace (prefixWord ++ tailWord_1497340) baseStart_1497340 baseEnd_1497340 := by
    simpa [prefixWord, tailWord_1497340, baseEnd_1497340] using wordTrace_append hprefix tailTrace_1497340
  have hstable : (prefixWord ++ tailWord_1497340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497340).length < 2 ^ (prefixWord ++ tailWord_1497340).sum := by decide
  have hdescent : baseEnd_1497340 < baseStart_1497340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497400 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_1497400 : Nat := 118140960795 + 1497400 * 2 ^ 59
def prefixEnd_1497400 : Nat := 4983230072969 + 3 ^ 40 * 1497400 * 2
def baseEnd_1497400 : Nat := 512590621361697766209059

theorem tailTrace_1497400 : CollatzResearch.WordTrace tailWord_1497400 prefixEnd_1497400 512590621361697766209059 := by
  unfold tailWord_1497400
  simp only [CollatzResearch.WordTrace]
  refine ⟨27307332387591505202480827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36409776516788673603307769 27307332387591505202480827)
  ·
    refine ⟨40960998581387257803721241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27307332387591505202480827 40960998581387257803721241)
    ·
      refine ⟨30720748936040443352790931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40960998581387257803721241 30720748936040443352790931)
      ·
        refine ⟨46081123404060665029186397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30720748936040443352790931 46081123404060665029186397)
        ·
          refine ⟨17280421276522749385944899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46081123404060665029186397 17280421276522749385944899)
          ·
            refine ⟨25920631914784124078917349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17280421276522749385944899 25920631914784124078917349)
            ·
              refine ⟨4860118484022023264797003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25920631914784124078917349 4860118484022023264797003)
              ·
                refine ⟨7290177726033034897195505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4860118484022023264797003 7290177726033034897195505)
                ·
                  refine ⟨5467633294524776172896629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7290177726033034897195505 5467633294524776172896629)
                  ·
                    refine ⟨512590621361697766209059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5467633294524776172896629 512590621361697766209059)
                    ·
                      rfl

theorem cell22_1497400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_1497400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497400 prefixEnd_1497400 := by exact prefixLift 1497400
  have htrace : WordTrace (prefixWord ++ tailWord_1497400) baseStart_1497400 baseEnd_1497400 := by
    simpa [prefixWord, tailWord_1497400, baseEnd_1497400] using wordTrace_append hprefix tailTrace_1497400
  have hstable : (prefixWord ++ tailWord_1497400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497400).length < 2 ^ (prefixWord ++ tailWord_1497400).sum := by decide
  have hdescent : baseEnd_1497400 < baseStart_1497400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497447 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 6]
def baseStart_1497447 : Nat := 118140960795 + 1497447 * 2 ^ 59
def prefixEnd_1497447 : Nat := 4983230072969 + 3 ^ 40 * 1497447 * 2
def baseEnd_1497447 : Nat := 170868903474068436761305

theorem tailTrace_1497447 : CollatzResearch.WordTrace tailWord_1497447 prefixEnd_1497447 170868903474068436761305 := by
  unfold tailWord_1497447
  simp only [CollatzResearch.WordTrace]
  refine ⟨54616379006012737431922595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36410919337341824954615063 54616379006012737431922595)
  ·
    refine ⟨81924568509019106147883893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54616379006012737431922595 81924568509019106147883893)
    ·
      refine ⟨7680428297720541201364115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81924568509019106147883893 7680428297720541201364115)
      ·
        refine ⟨11520642446580811802046173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680428297720541201364115 11520642446580811802046173)
        ·
          refine ⟨4320240917467804425767315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11520642446580811802046173 4320240917467804425767315)
          ·
            refine ⟨6480361376201706638650973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4320240917467804425767315 6480361376201706638650973)
            ·
              refine ⟨2430135516075639989494115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6480361376201706638650973 2430135516075639989494115)
              ·
                refine ⟨3645203274113459984241173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430135516075639989494115 3645203274113459984241173)
                ·
                  refine ⟨170868903474068436761305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3645203274113459984241173 170868903474068436761305)
                  ·
                    rfl

theorem cell22_1497447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 6].length) (baseStart_1497447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497447 prefixEnd_1497447 := by exact prefixLift 1497447
  have htrace : WordTrace (prefixWord ++ tailWord_1497447) baseStart_1497447 baseEnd_1497447 := by
    simpa [prefixWord, tailWord_1497447, baseEnd_1497447] using wordTrace_append hprefix tailTrace_1497447
  have hstable : (prefixWord ++ tailWord_1497447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497447).length < 2 ^ (prefixWord ++ tailWord_1497447).sum := by decide
  have hdescent : baseEnd_1497447 < baseStart_1497447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497492 : List Nat := [2, 4, 2, 1, 3, 10]
def baseStart_1497492 : Nat := 118140960795 + 1497492 * 2 ^ 59
def prefixEnd_1497492 : Nat := 4983230072969 + 3 ^ 40 * 1497492 * 2
def baseEnd_1497492 : Nat := 6328668084467162875417

theorem tailTrace_1497492 : CollatzResearch.WordTrace tailWord_1497492 prefixEnd_1497492 6328668084467162875417 := by
  unfold tailWord_1497492
  simp only [CollatzResearch.WordTrace]
  refine ⟨27309010145424855058655365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36412013527233140078207153 27309010145424855058655365)
  ·
    refine ⟨5120439402267160323497881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27309010145424855058655365 5120439402267160323497881)
    ·
      refine ⟨3840329551700370242623411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5120439402267160323497881 3840329551700370242623411)
      ·
        refine ⟨5760494327550555363935117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3840329551700370242623411 5760494327550555363935117)
        ·
          refine ⟨2160185372831458261475669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5760494327550555363935117 2160185372831458261475669)
          ·
            refine ⟨6328668084467162875417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2160185372831458261475669 6328668084467162875417)
            ·
              rfl

theorem cell22_1497492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 10].length) (baseStart_1497492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497492 prefixEnd_1497492 := by exact prefixLift 1497492
  have htrace : WordTrace (prefixWord ++ tailWord_1497492) baseStart_1497492 baseEnd_1497492 := by
    simpa [prefixWord, tailWord_1497492, baseEnd_1497492] using wordTrace_append hprefix tailTrace_1497492
  have hstable : (prefixWord ++ tailWord_1497492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497492).length < 2 ^ (prefixWord ++ tailWord_1497492).sum := by decide
  have hdescent : baseEnd_1497492 < baseStart_1497492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497496 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 2, 3]
def baseStart_1497496 : Nat := 118140960795 + 1497496 * 2 ^ 59
def prefixEnd_1497496 : Nat := 4983230072969 + 3 ^ 40 * 1497496 * 2
def baseEnd_1497496 : Nat := 512623484123585515808765

theorem tailTrace_1497496 : CollatzResearch.WordTrace tailWord_1497496 prefixEnd_1497496 512623484123585515808765 := by
  unfold tailWord_1497496
  simp only [CollatzResearch.WordTrace]
  refine ⟨27309083091417609400228171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36412110788556812533637561 27309083091417609400228171)
  ·
    refine ⟨40963624637126414100342257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27309083091417609400228171 40963624637126414100342257)
    ·
      refine ⟨30722718477844810575256693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40963624637126414100342257 30722718477844810575256693)
      ·
        refine ⟨2880254857297950991430315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30722718477844810575256693 2880254857297950991430315)
        ·
          refine ⟨4320382285946926487145473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2880254857297950991430315 4320382285946926487145473)
          ·
            refine ⟨3240286714460194865359105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4320382285946926487145473 3240286714460194865359105)
            ·
              refine ⟨2430215035845146149019329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3240286714460194865359105 2430215035845146149019329)
              ·
                refine ⟨1822661276883859611764497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430215035845146149019329 1822661276883859611764497)
                ·
                  refine ⟨1366995957662894708823373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1822661276883859611764497 1366995957662894708823373)
                  ·
                    refine ⟨512623484123585515808765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1366995957662894708823373 512623484123585515808765)
                    ·
                      rfl

theorem cell22_1497496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_1497496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497496 prefixEnd_1497496 := by exact prefixLift 1497496
  have htrace : WordTrace (prefixWord ++ tailWord_1497496) baseStart_1497496 baseEnd_1497496 := by
    simpa [prefixWord, tailWord_1497496, baseEnd_1497496] using wordTrace_append hprefix tailTrace_1497496
  have hstable : (prefixWord ++ tailWord_1497496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497496).length < 2 ^ (prefixWord ++ tailWord_1497496).sum := by decide
  have hdescent : baseEnd_1497496 < baseStart_1497496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497558 : List Nat := [5, 2, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1497558 : Nat := 118140960795 + 1497558 * 2 ^ 59
def prefixEnd_1497558 : Nat := 4983230072969 + 3 ^ 40 * 1497558 * 2
def baseEnd_1497558 : Nat := 512644707990638020758575

theorem tailTrace_1497558 : CollatzResearch.WordTrace tailWord_1497558 prefixEnd_1497558 512644707990638020758575 := by
  unfold tailWord_1497558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3413776719288162711825833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36413618339073735592808885 3413776719288162711825833)
  ·
    refine ⟨2560332539466122033869375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3413776719288162711825833 2560332539466122033869375)
    ·
      refine ⟨3840498809199183050804063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2560332539466122033869375 3840498809199183050804063)
      ·
        refine ⟨5760748213798774576206095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3840498809199183050804063 5760748213798774576206095)
        ·
          refine ⟨8641122320698161864309143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5760748213798774576206095 8641122320698161864309143)
          ·
            refine ⟨12961683481047242796463715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8641122320698161864309143 12961683481047242796463715)
            ·
              refine ⟨19442525221570864194695573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12961683481047242796463715 19442525221570864194695573)
              ·
                refine ⟨911368369761134259126355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19442525221570864194695573 911368369761134259126355)
                ·
                  refine ⟨1367052554641701388689533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911368369761134259126355 1367052554641701388689533)
                  ·
                    refine ⟨512644707990638020758575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1367052554641701388689533 512644707990638020758575)
                    ·
                      rfl

theorem cell22_1497558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1497558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497558 prefixEnd_1497558 := by exact prefixLift 1497558
  have htrace : WordTrace (prefixWord ++ tailWord_1497558) baseStart_1497558 baseEnd_1497558 := by
    simpa [prefixWord, tailWord_1497558, baseEnd_1497558] using wordTrace_append hprefix tailTrace_1497558
  have hstable : (prefixWord ++ tailWord_1497558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497558).length < 2 ^ (prefixWord ++ tailWord_1497558).sum := by decide
  have hdescent : baseEnd_1497558 < baseStart_1497558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497571 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 5]
def baseStart_1497571 : Nat := 118140960795 + 1497571 * 2 ^ 59
def prefixEnd_1497571 : Nat := 4983230072969 + 3 ^ 40 * 1497571 * 2
def baseEnd_1497571 : Nat := 170883052718770106727845

theorem tailTrace_1497571 : CollatzResearch.WordTrace tailWord_1497571 prefixEnd_1497571 170883052718770106727845 := by
  unfold tailWord_1497571
  simp only [CollatzResearch.WordTrace]
  refine ⟨54620901657563506609436567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36413934438375671072957711 54620901657563506609436567)
  ·
    refine ⟨81931352486345259914154851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54620901657563506609436567 81931352486345259914154851)
    ·
      refine ⟨122897028729517889871232277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81931352486345259914154851 122897028729517889871232277)
      ·
        refine ⟨5760798221696151087714013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122897028729517889871232277 5760798221696151087714013)
        ·
          refine ⟨2160299333136056657892755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5760798221696151087714013 2160299333136056657892755)
          ·
            refine ⟨3240448999704084986839133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160299333136056657892755 3240448999704084986839133)
            ·
              refine ⟨1215168374889031870064675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3240448999704084986839133 1215168374889031870064675)
              ·
                refine ⟨1822752562333547805097013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215168374889031870064675 1822752562333547805097013)
                ·
                  refine ⟨170883052718770106727845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1822752562333547805097013 170883052718770106727845)
                  ·
                    rfl

theorem cell22_1497571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 5].length) (baseStart_1497571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497571 prefixEnd_1497571 := by exact prefixLift 1497571
  have htrace : WordTrace (prefixWord ++ tailWord_1497571) baseStart_1497571 baseEnd_1497571 := by
    simpa [prefixWord, tailWord_1497571, baseEnd_1497571] using wordTrace_append hprefix tailTrace_1497571
  have hstable : (prefixWord ++ tailWord_1497571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497571).length < 2 ^ (prefixWord ++ tailWord_1497571).sum := by decide
  have hdescent : baseEnd_1497571 < baseStart_1497571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497584 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 1, 4]
def baseStart_1497584 : Nat := 118140960795 + 1497584 * 2 ^ 59
def prefixEnd_1497584 : Nat := 4983230072969 + 3 ^ 40 * 1497584 * 2
def baseEnd_1497584 : Nat := 512653608321982619608495

theorem tailTrace_1497584 : CollatzResearch.WordTrace tailWord_1497584 prefixEnd_1497584 512653608321982619608495 := by
  unfold tailWord_1497584
  simp only [CollatzResearch.WordTrace]
  refine ⟨27310687903258204914829903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36414250537677606553106537 27310687903258204914829903)
  ·
    refine ⟨40966031854887307372244855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27310687903258204914829903 40966031854887307372244855)
    ·
      refine ⟨61449047782330961058367283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40966031854887307372244855 61449047782330961058367283)
      ·
        refine ⟨92173571673496441587550925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61449047782330961058367283 92173571673496441587550925)
        ·
          refine ⟨34565089377561165595331597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92173571673496441587550925 34565089377561165595331597)
          ·
            refine ⟨12961908516585437098249349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34565089377561165595331597 12961908516585437098249349)
            ·
              refine ⟨2430357846859769455921753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12961908516585437098249349 2430357846859769455921753)
              ·
                refine ⟨1822768385144827091941315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430357846859769455921753 1822768385144827091941315)
                ·
                  refine ⟨2734152577717240637911973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822768385144827091941315 2734152577717240637911973)
                  ·
                    refine ⟨512653608321982619608495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2734152577717240637911973 512653608321982619608495)
                    ·
                      rfl

theorem cell22_1497584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_1497584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497584 prefixEnd_1497584 := by exact prefixLift 1497584
  have htrace : WordTrace (prefixWord ++ tailWord_1497584) baseStart_1497584 baseEnd_1497584 := by
    simpa [prefixWord, tailWord_1497584, baseEnd_1497584] using wordTrace_append hprefix tailTrace_1497584
  have hstable : (prefixWord ++ tailWord_1497584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497584).length < 2 ^ (prefixWord ++ tailWord_1497584).sum := by decide
  have hdescent : baseEnd_1497584 < baseStart_1497584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497597 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1497597 : Nat := 118140960795 + 1497597 * 2 ^ 59
def prefixEnd_1497597 : Nat := 4983230072969 + 3 ^ 40 * 1497597 * 2
def baseEnd_1497597 : Nat := 512658058487654919033455

theorem tailTrace_1497597 : CollatzResearch.WordTrace tailWord_1497597 prefixEnd_1497597 512658058487654919033455 := by
  unfold tailWord_1497597
  simp only [CollatzResearch.WordTrace]
  refine ⟨54621849955469313049883045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36414566636979542033255363 54621849955469313049883045)
  ·
    refine ⟨10241596866650496196853071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54621849955469313049883045 10241596866650496196853071)
    ·
      refine ⟨15362395299975744295279607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10241596866650496196853071 15362395299975744295279607)
      ·
        refine ⟨23043592949963616442919411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15362395299975744295279607 23043592949963616442919411)
        ·
          refine ⟨34565389424945424664379117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23043592949963616442919411 34565389424945424664379117)
          ·
            refine ⟨12962021034354534249142169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34565389424945424664379117 12962021034354534249142169)
            ·
              refine ⟨9721515775765900686856627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12962021034354534249142169 9721515775765900686856627)
              ·
                refine ⟨14582273663648851030284941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9721515775765900686856627 14582273663648851030284941)
                ·
                  refine ⟨5468352623868319136356853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14582273663648851030284941 5468352623868319136356853)
                  ·
                    refine ⟨512658058487654919033455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5468352623868319136356853 512658058487654919033455)
                    ·
                      rfl

theorem cell22_1497597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1497597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497597 prefixEnd_1497597 := by exact prefixLift 1497597
  have htrace : WordTrace (prefixWord ++ tailWord_1497597) baseStart_1497597 baseEnd_1497597 := by
    simpa [prefixWord, tailWord_1497597, baseEnd_1497597] using wordTrace_append hprefix tailTrace_1497597
  have hstable : (prefixWord ++ tailWord_1497597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497597).length < 2 ^ (prefixWord ++ tailWord_1497597).sum := by decide
  have hdescent : baseEnd_1497597 < baseStart_1497597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497672 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 7]
def baseStart_1497672 : Nat := 118140960795 + 1497672 * 2 ^ 59
def prefixEnd_1497672 : Nat := 4983230072969 + 3 ^ 40 * 1497672 * 2
def baseEnd_1497672 : Nat := 170894577506793241136075

theorem tailTrace_1497672 : CollatzResearch.WordTrace tailWord_1497672 prefixEnd_1497672 170894577506793241136075 := by
  unfold tailWord_1497672
  simp only [CollatzResearch.WordTrace]
  refine ⟨27312292715098800429431635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36416390286798400572575513 27312292715098800429431635)
  ·
    refine ⟨40968439072648200644147453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27312292715098800429431635 40968439072648200644147453)
    ·
      refine ⟨15363164652243075241555295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40968439072648200644147453 15363164652243075241555295)
      ·
        refine ⟨23044746978364612862332943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15363164652243075241555295 23044746978364612862332943)
        ·
          refine ⟨34567120467546919293499415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23044746978364612862332943 34567120467546919293499415)
          ·
            refine ⟨51850680701320378940249123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34567120467546919293499415 51850680701320378940249123)
            ·
              refine ⟨77776021051980568410373685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51850680701320378940249123 77776021051980568410373685)
              ·
                refine ⟨7291501973623178288472533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77776021051980568410373685 7291501973623178288472533)
                ·
                  refine ⟨170894577506793241136075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7291501973623178288472533 170894577506793241136075)
                  ·
                    rfl

theorem cell22_1497672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_1497672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497672 prefixEnd_1497672 := by exact prefixLift 1497672
  have htrace : WordTrace (prefixWord ++ tailWord_1497672) baseStart_1497672 baseEnd_1497672 := by
    simpa [prefixWord, tailWord_1497672, baseEnd_1497672] using wordTrace_append hprefix tailTrace_1497672
  have hstable : (prefixWord ++ tailWord_1497672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497672).length < 2 ^ (prefixWord ++ tailWord_1497672).sum := by decide
  have hdescent : baseEnd_1497672 < baseStart_1497672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497710 : List Nat := [4, 1, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_1497710 : Nat := 118140960795 + 1497710 * 2 ^ 59
def prefixEnd_1497710 : Nat := 4983230072969 + 3 ^ 40 * 1497710 * 2
def baseEnd_1497710 : Nat := 512696740696960290958109

theorem tailTrace_1497710 : CollatzResearch.WordTrace tailWord_1497710 prefixEnd_1497710 512696740696960290958109 := by
  unfold tailWord_1497710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828246425507491668593323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36417314269373288899164389 6828246425507491668593323)
  ·
    refine ⟨10242369638261237502889985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6828246425507491668593323 10242369638261237502889985)
    ·
      refine ⟨7681777228695928127167489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10242369638261237502889985 7681777228695928127167489)
      ·
        refine ⟨5761332921521946095375617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7681777228695928127167489 5761332921521946095375617)
        ·
          refine ⟨4320999691141459571531713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5761332921521946095375617 4320999691141459571531713)
          ·
            refine ⟨3240749768356094678648785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4320999691141459571531713 3240749768356094678648785)
            ·
              refine ⟨2430562326267071008986589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3240749768356094678648785 2430562326267071008986589)
              ·
                refine ⟨911460872350151628369971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2430562326267071008986589 911460872350151628369971)
                ·
                  refine ⟨1367191308525227442554957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911460872350151628369971 1367191308525227442554957)
                  ·
                    refine ⟨512696740696960290958109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1367191308525227442554957 512696740696960290958109)
                    ·
                      rfl

theorem cell22_1497710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_1497710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497710 prefixEnd_1497710 := by exact prefixLift 1497710
  have htrace : WordTrace (prefixWord ++ tailWord_1497710) baseStart_1497710 baseEnd_1497710 := by
    simpa [prefixWord, tailWord_1497710, baseEnd_1497710] using wordTrace_append hprefix tailTrace_1497710
  have hstable : (prefixWord ++ tailWord_1497710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497710).length < 2 ^ (prefixWord ++ tailWord_1497710).sum := by decide
  have hdescent : baseEnd_1497710 < baseStart_1497710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497764 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1497764 : Nat := 118140960795 + 1497764 * 2 ^ 59
def prefixEnd_1497764 : Nat := 4983230072969 + 3 ^ 40 * 1497764 * 2
def baseEnd_1497764 : Nat := 512715226000522150107943

theorem tailTrace_1497764 : CollatzResearch.WordTrace tailWord_1497764 prefixEnd_1497764 512715226000522150107943 := by
  unfold tailWord_1497764
  simp only [CollatzResearch.WordTrace]
  refine ⟨27313970472932150285606173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36418627297242867047474897 27313970472932150285606173)
  ·
    refine ⟨10242738927349556357102315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27313970472932150285606173 10242738927349556357102315)
    ·
      refine ⟨15364108391024334535653473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10242738927349556357102315 15364108391024334535653473)
      ·
        refine ⟨11523081293268250901740105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15364108391024334535653473 11523081293268250901740105)
        ·
          refine ⟨8642310969951188176305079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11523081293268250901740105 8642310969951188176305079)
          ·
            refine ⟨12963466454926782264457619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8642310969951188176305079 12963466454926782264457619)
            ·
              refine ⟨19445199682390173396686429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12963466454926782264457619 19445199682390173396686429)
              ·
                refine ⟨7291949880896315023757411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19445199682390173396686429 7291949880896315023757411)
                ·
                  refine ⟨10937924821344472535636117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7291949880896315023757411 10937924821344472535636117)
                  ·
                    refine ⟨512715226000522150107943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10937924821344472535636117 512715226000522150107943)
                    ·
                      rfl

theorem cell22_1497764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1497764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497764 prefixEnd_1497764 := by exact prefixLift 1497764
  have htrace : WordTrace (prefixWord ++ tailWord_1497764) baseStart_1497764 baseEnd_1497764 := by
    simpa [prefixWord, tailWord_1497764, baseEnd_1497764] using wordTrace_append hprefix tailTrace_1497764
  have hstable : (prefixWord ++ tailWord_1497764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497764).length < 2 ^ (prefixWord ++ tailWord_1497764).sum := by decide
  have hdescent : baseEnd_1497764 < baseStart_1497764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497779 : List Nat := [1, 1, 1, 2, 3, 6, 8]
def baseStart_1497779 : Nat := 118140960795 + 1497779 * 2 ^ 59
def prefixEnd_1497779 : Nat := 4983230072969 + 3 ^ 40 * 1497779 * 2
def baseEnd_1497779 : Nat := 18989642992854337443811

theorem tailTrace_1497779 : CollatzResearch.WordTrace tailWord_1497779 prefixEnd_1497779 18989642992854337443811 := by
  unfold tailWord_1497779
  simp only [CollatzResearch.WordTrace]
  refine ⟨54628488040809958133008391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36418992027206638755338927 54628488040809958133008391)
  ·
    refine ⟨81942732061214937199512587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54628488040809958133008391 81942732061214937199512587)
    ·
      refine ⟨122914098091822405799268881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81942732061214937199512587 122914098091822405799268881)
      ·
        refine ⟨92185573568866804349451661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122914098091822405799268881 92185573568866804349451661)
        ·
          refine ⟨34569590088325051631044373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92185573568866804349451661 34569590088325051631044373)
          ·
            refine ⟨1620449535390236795205205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34569590088325051631044373 1620449535390236795205205)
            ·
              refine ⟨18989642992854337443811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1620449535390236795205205 18989642992854337443811)
              ·
                rfl

theorem cell22_1497779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 8].length) (baseStart_1497779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497779 prefixEnd_1497779 := by exact prefixLift 1497779
  have htrace : WordTrace (prefixWord ++ tailWord_1497779) baseStart_1497779 baseEnd_1497779 := by
    simpa [prefixWord, tailWord_1497779, baseEnd_1497779] using wordTrace_append hprefix tailTrace_1497779
  have hstable : (prefixWord ++ tailWord_1497779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497779).length < 2 ^ (prefixWord ++ tailWord_1497779).sum := by decide
  have hdescent : baseEnd_1497779 < baseStart_1497779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497781 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1497781 : Nat := 118140960795 + 1497781 * 2 ^ 59
def prefixEnd_1497781 : Nat := 4983230072969 + 3 ^ 40 * 1497781 * 2
def baseEnd_1497781 : Nat := 512721045447939772432891

theorem tailTrace_1497781 : CollatzResearch.WordTrace tailWord_1497781 prefixEnd_1497781 512721045447939772432891 := by
  unfold tailWord_1497781
  simp only [CollatzResearch.WordTrace]
  refine ⟨54628560986802712474581197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36419040657868474983054131 54628560986802712474581197)
  ·
    refine ⟨20485710370051017177967949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54628560986802712474581197 20485710370051017177967949)
    ·
      refine ⟨7682141388769131441737981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20485710370051017177967949 7682141388769131441737981)
      ·
        refine ⟨2880803020788424290651743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7682141388769131441737981 2880803020788424290651743)
        ·
          refine ⟨4321204531182636435977615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2880803020788424290651743 4321204531182636435977615)
          ·
            refine ⟨6481806796773954653966423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4321204531182636435977615 6481806796773954653966423)
            ·
              refine ⟨9722710195160931980949635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6481806796773954653966423 9722710195160931980949635)
              ·
                refine ⟨14584065292741397971424453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9722710195160931980949635 14584065292741397971424453)
                ·
                  refine ⟨2734512242389012119642085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14584065292741397971424453 2734512242389012119642085)
                  ·
                    refine ⟨512721045447939772432891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2734512242389012119642085 512721045447939772432891)
                    ·
                      rfl

theorem cell22_1497781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1497781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497781 prefixEnd_1497781 := by exact prefixLift 1497781
  have htrace : WordTrace (prefixWord ++ tailWord_1497781) baseStart_1497781 baseEnd_1497781 := by
    simpa [prefixWord, tailWord_1497781, baseEnd_1497781] using wordTrace_append hprefix tailTrace_1497781
  have hstable : (prefixWord ++ tailWord_1497781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497781).length < 2 ^ (prefixWord ++ tailWord_1497781).sum := by decide
  have hdescent : baseEnd_1497781 < baseStart_1497781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497796 : List Nat := [2, 3, 3, 1, 1, 3, 2, 7]
def baseStart_1497796 : Nat := 118140960795 + 1497796 * 2 ^ 59
def prefixEnd_1497796 : Nat := 4983230072969 + 3 ^ 40 * 1497796 * 2
def baseEnd_1497796 : Nat := 56969575583831637034205

theorem tailTrace_1497796 : CollatzResearch.WordTrace tailWord_1497796 prefixEnd_1497796 56969575583831637034205 := by
  unfold tailWord_1497796
  simp only [CollatzResearch.WordTrace]
  refine ⟨27314554040874185018188621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36419405387832246690918161 27314554040874185018188621)
  ·
    refine ⟨10242957765327819381820733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27314554040874185018188621 10242957765327819381820733)
    ·
      refine ⟨3841109161997932268182775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10242957765327819381820733 3841109161997932268182775)
      ·
        refine ⟨5761663742996898402274163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3841109161997932268182775 5761663742996898402274163)
        ·
          refine ⟨8642495614495347603411245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5761663742996898402274163 8642495614495347603411245)
          ·
            refine ⟨3240935855435755351279217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8642495614495347603411245 3240935855435755351279217)
            ·
              refine ⟨2430701891576816513459413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3240935855435755351279217 2430701891576816513459413)
              ·
                refine ⟨56969575583831637034205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2430701891576816513459413 56969575583831637034205)
                ·
                  rfl

theorem cell22_1497796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 7].length) (baseStart_1497796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497796 prefixEnd_1497796 := by exact prefixLift 1497796
  have htrace : WordTrace (prefixWord ++ tailWord_1497796) baseStart_1497796 baseEnd_1497796 := by
    simpa [prefixWord, tailWord_1497796, baseEnd_1497796] using wordTrace_append hprefix tailTrace_1497796
  have hstable : (prefixWord ++ tailWord_1497796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497796).length < 2 ^ (prefixWord ++ tailWord_1497796).sum := by decide
  have hdescent : baseEnd_1497796 < baseStart_1497796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497800 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 2, 3]
def baseStart_1497800 : Nat := 118140960795 + 1497800 * 2 ^ 59
def prefixEnd_1497800 : Nat := 4983230072969 + 3 ^ 40 * 1497800 * 2
def baseEnd_1497800 : Nat := 512727549536230056207833

theorem tailTrace_1497800 : CollatzResearch.WordTrace tailWord_1497800 prefixEnd_1497800 512727549536230056207833 := by
  unfold tailWord_1497800
  simp only [CollatzResearch.WordTrace]
  refine ⟨27314626986866939359761427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36419502649155919146348569 27314626986866939359761427)
  ·
    refine ⟨40971940480300409039642141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27314626986866939359761427 40971940480300409039642141)
    ·
      refine ⟨15364477680112653389865803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40971940480300409039642141 15364477680112653389865803)
      ·
        refine ⟨23046716520168980084798705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15364477680112653389865803 23046716520168980084798705)
        ·
          refine ⟨17285037390126735063599029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23046716520168980084798705 17285037390126735063599029)
          ·
            refine ⟨1620472255324381412212409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17285037390126735063599029 1620472255324381412212409)
            ·
              refine ⟨1215354191493286059159307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620472255324381412212409 1215354191493286059159307)
              ·
                refine ⟨1823031287239929088738961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215354191493286059159307 1823031287239929088738961)
                ·
                  refine ⟨1367273465429946816554221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1823031287239929088738961 1367273465429946816554221)
                  ·
                    refine ⟨512727549536230056207833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1367273465429946816554221 512727549536230056207833)
                    ·
                      rfl

theorem cell22_1497800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_1497800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497800 prefixEnd_1497800 := by exact prefixLift 1497800
  have htrace : WordTrace (prefixWord ++ tailWord_1497800) baseStart_1497800 baseEnd_1497800 := by
    simpa [prefixWord, tailWord_1497800, baseEnd_1497800] using wordTrace_append hprefix tailTrace_1497800
  have hstable : (prefixWord ++ tailWord_1497800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497800).length < 2 ^ (prefixWord ++ tailWord_1497800).sum := by decide
  have hdescent : baseEnd_1497800 < baseStart_1497800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497841 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 5]
def baseStart_1497841 : Nat := 118140960795 + 1497841 * 2 ^ 59
def prefixEnd_1497841 : Nat := 4983230072969 + 3 ^ 40 * 1497841 * 2
def baseEnd_1497841 : Nat := 170913861558039871977569

theorem tailTrace_1497841 : CollatzResearch.WordTrace tailWord_1497841 prefixEnd_1497841 170913861558039871977569 := by
  unfold tailWord_1497841
  simp only [CollatzResearch.WordTrace]
  refine ⟨54630749366585342721765377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36420499577723561814510251 54630749366585342721765377)
  ·
    refine ⟨40973062024939007041324033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54630749366585342721765377 40973062024939007041324033)
    ·
      refine ⟨30729796518704255280993025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40973062024939007041324033 30729796518704255280993025)
      ·
        refine ⟨23047347389028191460744769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30729796518704255280993025 23047347389028191460744769)
        ·
          refine ⟨17285510541771143595558577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23047347389028191460744769 17285510541771143595558577)
          ·
            refine ⟨12964132906328357696668933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17285510541771143595558577 12964132906328357696668933)
            ·
              refine ⟨2430774919936567068125425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12964132906328357696668933 2430774919936567068125425)
              ·
                refine ⟨1823081189952425301094069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430774919936567068125425 1823081189952425301094069)
                ·
                  refine ⟨170913861558039871977569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1823081189952425301094069 170913861558039871977569)
                  ·
                    rfl

theorem cell22_1497841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_1497841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497841 prefixEnd_1497841 := by exact prefixLift 1497841
  have htrace : WordTrace (prefixWord ++ tailWord_1497841) baseStart_1497841 baseEnd_1497841 := by
    simpa [prefixWord, tailWord_1497841, baseEnd_1497841] using wordTrace_append hprefix tailTrace_1497841
  have hstable : (prefixWord ++ tailWord_1497841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497841).length < 2 ^ (prefixWord ++ tailWord_1497841).sum := by decide
  have hdescent : baseEnd_1497841 < baseStart_1497841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497858 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1497858 : Nat := 118140960795 + 1497858 * 2 ^ 59
def prefixEnd_1497858 : Nat := 4983230072969 + 3 ^ 40 * 1497858 * 2
def baseEnd_1497858 : Nat := 170915801373845746085885

theorem tailTrace_1497858 : CollatzResearch.WordTrace tailWord_1497858 prefixEnd_1497858 170915801373845746085885 := by
  unfold tailWord_1497858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13657842351880938656283557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36420912938349169750089485 13657842351880938656283557)
  ·
    refine ⟨2560845440977675998053167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13657842351880938656283557 2560845440977675998053167)
    ·
      refine ⟨3841268161466513997079751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2560845440977675998053167 3841268161466513997079751)
      ·
        refine ⟨5761902242199770995619627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3841268161466513997079751 5761902242199770995619627)
        ·
          refine ⟨8642853363299656493429441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5761902242199770995619627 8642853363299656493429441)
          ·
            refine ⟨6482140022474742370072081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8642853363299656493429441 6482140022474742370072081)
            ·
              refine ⟨4861605016856056777554061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6482140022474742370072081 4861605016856056777554061)
              ·
                refine ⟨1823101881321021291582773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4861605016856056777554061 1823101881321021291582773)
                ·
                  refine ⟨170915801373845746085885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1823101881321021291582773 170915801373845746085885)
                  ·
                    rfl

theorem cell22_1497858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1497858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497858 prefixEnd_1497858 := by exact prefixLift 1497858
  have htrace : WordTrace (prefixWord ++ tailWord_1497858) baseStart_1497858 baseEnd_1497858 := by
    simpa [prefixWord, tailWord_1497858, baseEnd_1497858] using wordTrace_append hprefix tailTrace_1497858
  have hstable : (prefixWord ++ tailWord_1497858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497858).length < 2 ^ (prefixWord ++ tailWord_1497858).sum := by decide
  have hdescent : baseEnd_1497858 < baseStart_1497858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497871 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 1, 4]
def baseStart_1497871 : Nat := 118140960795 + 1497871 * 2 ^ 59
def prefixEnd_1497871 : Nat := 4983230072969 + 3 ^ 40 * 1497871 * 2
def baseEnd_1497871 : Nat := 512751854287209537682615

theorem tailTrace_1497871 : CollatzResearch.WordTrace tailWord_1497871 prefixEnd_1497871 512751854287209537682615 := by
  unfold tailWord_1497871
  simp only [CollatzResearch.WordTrace]
  refine ⟨54631843556476657845357467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36421229037651105230238311 54631843556476657845357467)
  ·
    refine ⟨81947765334714986768036201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54631843556476657845357467 81947765334714986768036201)
    ·
      refine ⟨61460824001036240076027151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81947765334714986768036201 61460824001036240076027151)
      ·
        refine ⟨92191236001554360114040727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61460824001036240076027151 92191236001554360114040727)
        ·
          refine ⟨138286854002331540171061091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92191236001554360114040727 138286854002331540171061091)
          ·
            refine ⟨207430281003497310256591637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138286854002331540171061091 207430281003497310256591637)
            ·
              refine ⟨9723294422038936418277733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207430281003497310256591637 9723294422038936418277733)
              ·
                refine ⟨1823117704132300578427075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9723294422038936418277733 1823117704132300578427075)
                ·
                  refine ⟨2734676556198450867640613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823117704132300578427075 2734676556198450867640613)
                  ·
                    refine ⟨512751854287209537682615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2734676556198450867640613 512751854287209537682615)
                    ·
                      rfl

theorem cell22_1497871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_1497871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497871 prefixEnd_1497871 := by exact prefixLift 1497871
  have htrace : WordTrace (prefixWord ++ tailWord_1497871) baseStart_1497871 baseEnd_1497871 := by
    simpa [prefixWord, tailWord_1497871, baseEnd_1497871] using wordTrace_append hprefix tailTrace_1497871
  have hstable : (prefixWord ++ tailWord_1497871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497871).length < 2 ^ (prefixWord ++ tailWord_1497871).sum := by decide
  have hdescent : baseEnd_1497871 < baseStart_1497871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497888 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 1, 4]
def baseStart_1497888 : Nat := 118140960795 + 1497888 * 2 ^ 59
def prefixEnd_1497888 : Nat := 4983230072969 + 3 ^ 40 * 1497888 * 2
def baseEnd_1497888 : Nat := 512757673734627160007563

theorem tailTrace_1497888 : CollatzResearch.WordTrace tailWord_1497888 prefixEnd_1497888 512757673734627160007563 := by
  unfold tailWord_1497888
  simp only [CollatzResearch.WordTrace]
  refine ⟨27316231798707534874363159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36421642398276713165817545 27316231798707534874363159)
  ·
    refine ⟨40974347698061302311544739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27316231798707534874363159 40974347698061302311544739)
    ·
      refine ⟨61461521547091953467317109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40974347698061302311544739 61461521547091953467317109)
      ·
        refine ⟨5762017645039870637560979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61461521547091953467317109 5762017645039870637560979)
        ·
          refine ⟨8643026467559805956341469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5762017645039870637560979 8643026467559805956341469)
          ·
            refine ⟨3241134925334927233628051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8643026467559805956341469 3241134925334927233628051)
            ·
              refine ⟨4861702388002390850442077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241134925334927233628051 4861702388002390850442077)
              ·
                refine ⟨1823138395500896568915779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4861702388002390850442077 1823138395500896568915779)
                ·
                  refine ⟨2734707593251344853373669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823138395500896568915779 2734707593251344853373669)
                  ·
                    refine ⟨512757673734627160007563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2734707593251344853373669 512757673734627160007563)
                    ·
                      rfl

theorem cell22_1497888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_1497888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497888 prefixEnd_1497888 := by exact prefixLift 1497888
  have htrace : WordTrace (prefixWord ++ tailWord_1497888) baseStart_1497888 baseEnd_1497888 := by
    simpa [prefixWord, tailWord_1497888, baseEnd_1497888] using wordTrace_append hprefix tailTrace_1497888
  have hstable : (prefixWord ++ tailWord_1497888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497888).length < 2 ^ (prefixWord ++ tailWord_1497888).sum := by decide
  have hdescent : baseEnd_1497888 < baseStart_1497888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497899 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 3, 6]
def baseStart_1497899 : Nat := 118140960795 + 1497899 * 2 ^ 59
def prefixEnd_1497899 : Nat := 4983230072969 + 3 ^ 40 * 1497899 * 2
def baseEnd_1497899 : Nat := 512761439259426797982529

theorem tailTrace_1497899 : CollatzResearch.WordTrace tailWord_1497899 prefixEnd_1497899 512761439259426797982529 := by
  unfold tailWord_1497899
  simp only [CollatzResearch.WordTrace]
  refine ⟨54632864800375218627376751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36421909866916812418251167 54632864800375218627376751)
  ·
    refine ⟨81949297200562827941065127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54632864800375218627376751 81949297200562827941065127)
    ·
      refine ⟨122923945800844241911597691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81949297200562827941065127 122923945800844241911597691)
      ·
        refine ⟨184385918701266362867396537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122923945800844241911597691 184385918701266362867396537)
        ·
          refine ⟨138289439025949772150547403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184385918701266362867396537 138289439025949772150547403)
          ·
            refine ⟨207434158538924658225821105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138289439025949772150547403 207434158538924658225821105)
            ·
              refine ⟨155575618904193493669365829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207434158538924658225821105 155575618904193493669365829)
              ·
                refine ⟨29170428544536280063006093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155575618904193493669365829 29170428544536280063006093)
                ·
                  refine ⟨10938910704201105023627285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29170428544536280063006093 10938910704201105023627285)
                  ·
                    refine ⟨512761439259426797982529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10938910704201105023627285 512761439259426797982529)
                    ·
                      rfl

theorem cell22_1497899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_1497899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497899 prefixEnd_1497899 := by exact prefixLift 1497899
  have htrace : WordTrace (prefixWord ++ tailWord_1497899) baseStart_1497899 baseEnd_1497899 := by
    simpa [prefixWord, tailWord_1497899, baseEnd_1497899] using wordTrace_append hprefix tailTrace_1497899
  have hstable : (prefixWord ++ tailWord_1497899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497899).length < 2 ^ (prefixWord ++ tailWord_1497899).sum := by decide
  have hdescent : baseEnd_1497899 < baseStart_1497899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497937 : List Nat := [1, 2, 2, 1, 7, 1, 1, 3, 4]
def baseStart_1497937 : Nat := 118140960795 + 1497937 * 2 ^ 59
def prefixEnd_1497937 : Nat := 4983230072969 + 3 ^ 40 * 1497937 * 2
def baseEnd_1497937 : Nat := 170924815812002455177471

theorem tailTrace_1497937 : CollatzResearch.WordTrace tailWord_1497937 prefixEnd_1497937 170924815812002455177471 := by
  unfold tailWord_1497937
  simp only [CollatzResearch.WordTrace]
  refine ⟨54634250774237551117260065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36422833849491700744840043 54634250774237551117260065)
  ·
    refine ⟨40975688080678163337945049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54634250774237551117260065 40975688080678163337945049)
    ·
      refine ⟨30731766060508622503458787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40975688080678163337945049 30731766060508622503458787)
      ·
        refine ⟨46097649090762933755188181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30731766060508622503458787 46097649090762933755188181)
        ·
          refine ⟨1080413650564756259887223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 46097649090762933755188181 1080413650564756259887223)
          ·
            refine ⟨1620620475847134389830835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080413650564756259887223 1620620475847134389830835)
            ·
              refine ⟨2430930713770701584746253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620620475847134389830835 2430930713770701584746253)
              ·
                refine ⟨911599017664013094279845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2430930713770701584746253 911599017664013094279845)
                ·
                  refine ⟨170924815812002455177471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 911599017664013094279845 170924815812002455177471)
                  ·
                    rfl

theorem cell22_1497937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 4].length) (baseStart_1497937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497937 prefixEnd_1497937 := by exact prefixLift 1497937
  have htrace : WordTrace (prefixWord ++ tailWord_1497937) baseStart_1497937 baseEnd_1497937 := by
    simpa [prefixWord, tailWord_1497937, baseEnd_1497937] using wordTrace_append hprefix tailTrace_1497937
  have hstable : (prefixWord ++ tailWord_1497937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497937).length < 2 ^ (prefixWord ++ tailWord_1497937).sum := by decide
  have hdescent : baseEnd_1497937 < baseStart_1497937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497948 : List Nat := [2, 2, 4, 2, 1, 3, 8]
def baseStart_1497948 : Nat := 118140960795 + 1497948 * 2 ^ 59
def prefixEnd_1497948 : Nat := 4983230072969 + 3 ^ 40 * 1497948 * 2
def baseEnd_1497948 : Nat := 18991785665215074203977

theorem tailTrace_1497948 : CollatzResearch.WordTrace tailWord_1497948 prefixEnd_1497948 18991785665215074203977 := by
  unfold tailWord_1497948
  simp only [CollatzResearch.WordTrace]
  refine ⟨27317325988598849997955249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36423101318131799997273665 27317325988598849997955249)
  ·
    refine ⟨20487994491449137498466437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27317325988598849997955249 20487994491449137498466437)
    ·
      refine ⟨3841498967146713280962457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20487994491449137498466437 3841498967146713280962457)
      ·
        refine ⟨2881124225360034960721843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3841498967146713280962457 2881124225360034960721843)
        ·
          refine ⟨4321686338040052441082765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2881124225360034960721843 4321686338040052441082765)
          ·
            refine ⟨1620632376765019665406037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4321686338040052441082765 1620632376765019665406037)
            ·
              refine ⟨18991785665215074203977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1620632376765019665406037 18991785665215074203977)
              ·
                rfl

theorem cell22_1497948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 8].length) (baseStart_1497948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497948 prefixEnd_1497948 := by exact prefixLift 1497948
  have htrace : WordTrace (prefixWord ++ tailWord_1497948) baseStart_1497948 baseEnd_1497948 := by
    simpa [prefixWord, tailWord_1497948, baseEnd_1497948] using wordTrace_append hprefix tailTrace_1497948
  have hstable : (prefixWord ++ tailWord_1497948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497948).length < 2 ^ (prefixWord ++ tailWord_1497948).sum := by decide
  have hdescent : baseEnd_1497948 < baseStart_1497948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497963 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 3, 3]
def baseStart_1497963 : Nat := 118140960795 + 1497963 * 2 ^ 59
def prefixEnd_1497963 : Nat := 4983230072969 + 3 ^ 40 * 1497963 * 2
def baseEnd_1497963 : Nat := 512783347767351964382333

theorem tailTrace_1497963 : CollatzResearch.WordTrace tailWord_1497963 prefixEnd_1497963 512783347767351964382333 := by
  unfold tailWord_1497963
  simp only [CollatzResearch.WordTrace]
  refine ⟨54635199072143357557706543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36423466048095571705137695 54635199072143357557706543)
  ·
    refine ⟨81952798608215036336559815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54635199072143357557706543 81952798608215036336559815)
    ·
      refine ⟨122929197912322554504839723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81952798608215036336559815 122929197912322554504839723)
      ·
        refine ⟨184393796868483831757259585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122929197912322554504839723 184393796868483831757259585)
        ·
          refine ⟨138295347651362873817944689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184393796868483831757259585 138295347651362873817944689)
          ·
            refine ⟨103721510738522155363458517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138295347651362873817944689 103721510738522155363458517)
            ·
              refine ⟨2430972907934113016331059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 103721510738522155363458517 2430972907934113016331059)
              ·
                refine ⟨3646459361901169524496589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430972907934113016331059 3646459361901169524496589)
                ·
                  refine ⟨1367422260712938571686221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3646459361901169524496589 1367422260712938571686221)
                  ·
                    refine ⟨512783347767351964382333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1367422260712938571686221 512783347767351964382333)
                    ·
                      rfl

theorem cell22_1497963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 3].length) (baseStart_1497963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1497963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1497963 prefixEnd_1497963 := by exact prefixLift 1497963
  have htrace : WordTrace (prefixWord ++ tailWord_1497963) baseStart_1497963 baseEnd_1497963 := by
    simpa [prefixWord, tailWord_1497963, baseEnd_1497963] using wordTrace_append hprefix tailTrace_1497963
  have hstable : (prefixWord ++ tailWord_1497963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497963).length < 2 ^ (prefixWord ++ tailWord_1497963).sum := by decide
  have hdescent : baseEnd_1497963 < baseStart_1497963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498010 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_1498010 : Nat := 118140960795 + 1498010 * 2 ^ 59
def prefixEnd_1498010 : Nat := 4983230072969 + 3 ^ 40 * 1498010 * 2
def baseEnd_1498010 : Nat := 170933145609286502819063

theorem tailTrace_1498010 : CollatzResearch.WordTrace tailWord_1498010 prefixEnd_1498010 170933145609286502819063 := by
  unfold tailWord_1498010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659228325743271146166871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36424608868648723056444989 13659228325743271146166871)
  ·
    refine ⟨20488842488614906719250307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13659228325743271146166871 20488842488614906719250307)
    ·
      refine ⟨30733263732922360078875461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20488842488614906719250307 30733263732922360078875461)
      ·
        refine ⟨5762486949922942514789149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30733263732922360078875461 5762486949922942514789149)
        ·
          refine ⟨2160932606221103443045931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5762486949922942514789149 2160932606221103443045931)
          ·
            refine ⟨3241398909331655164568897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160932606221103443045931 3241398909331655164568897)
            ·
              refine ⟨2431049181998741373426673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241398909331655164568897 2431049181998741373426673)
              ·
                refine ⟨1823286886499056030070005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431049181998741373426673 1823286886499056030070005)
                ·
                  refine ⟨170933145609286502819063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1823286886499056030070005 170933145609286502819063)
                  ·
                    rfl

theorem cell22_1498010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_1498010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498010 prefixEnd_1498010 := by exact prefixLift 1498010
  have htrace : WordTrace (prefixWord ++ tailWord_1498010) baseStart_1498010 baseEnd_1498010 := by
    simpa [prefixWord, tailWord_1498010, baseEnd_1498010] using wordTrace_append hprefix tailTrace_1498010
  have hstable : (prefixWord ++ tailWord_1498010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498010).length < 2 ^ (prefixWord ++ tailWord_1498010).sum := by decide
  have hdescent : baseEnd_1498010 < baseStart_1498010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498051 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 1, 6]
def baseStart_1498051 : Nat := 118140960795 + 1498051 * 2 ^ 59
def prefixEnd_1498051 : Nat := 4983230072969 + 3 ^ 40 * 1498051 * 2
def baseEnd_1498051 : Nat := 512813471965749068182063

theorem tailTrace_1498051 : CollatzResearch.WordTrace tailWord_1498051 prefixEnd_1498051 512813471965749068182063 := by
  unfold tailWord_1498051
  simp only [CollatzResearch.WordTrace]
  refine ⟨54638408695824548586910007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36425605797216365724606671 54638408695824548586910007)
  ·
    refine ⟨81957613043736822880365011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54638408695824548586910007 81957613043736822880365011)
    ·
      refine ⟨122936419565605234320547517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81957613043736822880365011 122936419565605234320547517)
      ·
        refine ⟨46101157337101962870205319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122936419565605234320547517 46101157337101962870205319)
        ·
          refine ⟨69151736005652944305307979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46101157337101962870205319 69151736005652944305307979)
          ·
            refine ⟨103727604008479416457961969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69151736005652944305307979 103727604008479416457961969)
            ·
              refine ⟨77795703006359562343471477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103727604008479416457961969 77795703006359562343471477)
              ·
                refine ⟨7293347156846208969700451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77795703006359562343471477 7293347156846208969700451)
                ·
                  refine ⟨10940020735269313454550677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7293347156846208969700451 10940020735269313454550677)
                  ·
                    refine ⟨512813471965749068182063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10940020735269313454550677 512813471965749068182063)
                    ·
                      rfl

theorem cell22_1498051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_1498051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498051 prefixEnd_1498051 := by exact prefixLift 1498051
  have htrace : WordTrace (prefixWord ++ tailWord_1498051) baseStart_1498051 baseEnd_1498051 := by
    simpa [prefixWord, tailWord_1498051, baseEnd_1498051] using wordTrace_append hprefix tailTrace_1498051
  have hstable : (prefixWord ++ tailWord_1498051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498051).length < 2 ^ (prefixWord ++ tailWord_1498051).sum := by decide
  have hdescent : baseEnd_1498051 < baseStart_1498051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498061 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 5]
def baseStart_1498061 : Nat := 118140960795 + 1498061 * 2 ^ 59
def prefixEnd_1498061 : Nat := 4983230072969 + 3 ^ 40 * 1498061 * 2
def baseEnd_1498061 : Nat := 170938965056704125144011

theorem tailTrace_1498061 : CollatzResearch.WordTrace tailWord_1498061 prefixEnd_1498061 170938965056704125144011 := by
  unfold tailWord_1498061
  simp only [CollatzResearch.WordTrace]
  refine ⟨54638773425788320294774037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36425848950525546863182691 54638773425788320294774037)
  ·
    refine ⟨2561192504333827513817533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54638773425788320294774037 2561192504333827513817533)
    ·
      refine ⟨960447189125185317681575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2561192504333827513817533 960447189125185317681575)
      ·
        refine ⟨1440670783687777976522363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960447189125185317681575 1440670783687777976522363)
        ·
          refine ⟨2161006175531666964783545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440670783687777976522363 2161006175531666964783545)
          ·
            refine ⟨1620754631648750223587659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161006175531666964783545 1620754631648750223587659)
            ·
              refine ⟨2431131947473125335381489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620754631648750223587659 2431131947473125335381489)
              ·
                refine ⟨1823348960604844001536117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431131947473125335381489 1823348960604844001536117)
                ·
                  refine ⟨170938965056704125144011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1823348960604844001536117 170938965056704125144011)
                  ·
                    rfl

theorem cell22_1498061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_1498061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498061 prefixEnd_1498061 := by exact prefixLift 1498061
  have htrace : WordTrace (prefixWord ++ tailWord_1498061) baseStart_1498061 baseEnd_1498061 := by
    simpa [prefixWord, tailWord_1498061, baseEnd_1498061] using wordTrace_append hprefix tailTrace_1498061
  have hstable : (prefixWord ++ tailWord_1498061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498061).length < 2 ^ (prefixWord ++ tailWord_1498061).sum := by decide
  have hdescent : baseEnd_1498061 < baseStart_1498061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498145 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 5]
def baseStart_1498145 : Nat := 118140960795 + 1498145 * 2 ^ 59
def prefixEnd_1498145 : Nat := 4983230072969 + 3 ^ 40 * 1498145 * 2
def baseEnd_1498145 : Nat := 170948550028921385443925

theorem tailTrace_1498145 : CollatzResearch.WordTrace tailWord_1498145 prefixEnd_1498145 170948550028921385443925 := by
  unfold tailWord_1498145
  simp only [CollatzResearch.WordTrace]
  refine ⟨54641837157484002640831889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36427891438322668427221259 54641837157484002640831889)
  ·
    refine ⟨40981377868113001980623917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54641837157484002640831889 40981377868113001980623917)
    ·
      refine ⟨15368016700542375742733969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40981377868113001980623917 15368016700542375742733969)
      ·
        refine ⟨11526012525406781807050477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15368016700542375742733969 11526012525406781807050477)
        ·
          refine ⟨4322254697027543177643929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11526012525406781807050477 4322254697027543177643929)
          ·
            refine ⟨3241691022770657383232947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4322254697027543177643929 3241691022770657383232947)
            ·
              refine ⟨4862536534155986074849421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241691022770657383232947 4862536534155986074849421)
              ·
                refine ⟨1823451200308494778068533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4862536534155986074849421 1823451200308494778068533)
                ·
                  refine ⟨170948550028921385443925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1823451200308494778068533 170948550028921385443925)
                  ·
                    rfl

theorem cell22_1498145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_1498145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498145 prefixEnd_1498145 := by exact prefixLift 1498145
  have htrace : WordTrace (prefixWord ++ tailWord_1498145) baseStart_1498145 baseEnd_1498145 := by
    simpa [prefixWord, tailWord_1498145, baseEnd_1498145] using wordTrace_append hprefix tailTrace_1498145
  have hstable : (prefixWord ++ tailWord_1498145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498145).length < 2 ^ (prefixWord ++ tailWord_1498145).sum := by decide
  have hdescent : baseEnd_1498145 < baseStart_1498145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498188 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_1498188 : Nat := 118140960795 + 1498188 * 2 ^ 59
def prefixEnd_1498188 : Nat := 4983230072969 + 3 ^ 40 * 1498188 * 2
def baseEnd_1498188 : Nat := 512860369865526377506643

theorem tailTrace_1498188 : CollatzResearch.WordTrace tailWord_1498188 prefixEnd_1498188 512860369865526377506643 := by
  unfold tailWord_1498188
  simp only [CollatzResearch.WordTrace]
  refine ⟨27321702748164110492323609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36428936997552147323098145 27321702748164110492323609)
  ·
    refine ⟨20491277061123082869242707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27321702748164110492323609 20491277061123082869242707)
    ·
      refine ⟨30736915591684624303864061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20491277061123082869242707 30736915591684624303864061)
      ·
        refine ⟨11526343346881734113949023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30736915591684624303864061 11526343346881734113949023)
        ·
          refine ⟨17289515020322601170923535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11526343346881734113949023 17289515020322601170923535)
          ·
            refine ⟨25934272530483901756385303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17289515020322601170923535 25934272530483901756385303)
            ·
              refine ⟨38901408795725852634577955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25934272530483901756385303 38901408795725852634577955)
              ·
                refine ⟨58352113193588778951866933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38901408795725852634577955 58352113193588778951866933)
                ·
                  refine ⟨5470510611898948026737525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58352113193588778951866933 5470510611898948026737525)
                  ·
                    refine ⟨512860369865526377506643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5470510611898948026737525 512860369865526377506643)
                    ·
                      rfl

theorem cell22_1498188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_1498188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498188 prefixEnd_1498188 := by exact prefixLift 1498188
  have htrace : WordTrace (prefixWord ++ tailWord_1498188) baseStart_1498188 baseEnd_1498188 := by
    simpa [prefixWord, tailWord_1498188, baseEnd_1498188] using wordTrace_append hprefix tailTrace_1498188
  have hstable : (prefixWord ++ tailWord_1498188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498188).length < 2 ^ (prefixWord ++ tailWord_1498188).sum := by decide
  have hdescent : baseEnd_1498188 < baseStart_1498188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498314 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_1498314 : Nat := 118140960795 + 1498314 * 2 ^ 59
def prefixEnd_1498314 : Nat := 4983230072969 + 3 ^ 40 * 1498314 * 2
def baseEnd_1498314 : Nat := 170967834080168016285419

theorem tailTrace_1498314 : CollatzResearch.WordTrace tailWord_1498314 prefixEnd_1498314 170967834080168016285419 := by
  unfold tailWord_1498314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13662000273467936125933499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36432000729247829669155997 13662000273467936125933499)
  ·
    refine ⟨20493000410201904188900249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13662000273467936125933499 20493000410201904188900249)
    ·
      refine ⟨15369750307651428141675187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20493000410201904188900249 15369750307651428141675187)
      ·
        refine ⟨23054625461477142212512781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15369750307651428141675187 23054625461477142212512781)
        ·
          refine ⟨8645484548053928329692293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23054625461477142212512781 8645484548053928329692293)
          ·
            refine ⟨1621028352760111561817305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8645484548053928329692293 1621028352760111561817305)
            ·
              refine ⟨1215771264570083671362979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621028352760111561817305 1215771264570083671362979)
              ·
                refine ⟨1823656896855125507044469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215771264570083671362979 1823656896855125507044469)
                ·
                  refine ⟨170967834080168016285419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1823656896855125507044469 170967834080168016285419)
                  ·
                    rfl

theorem cell22_1498314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_1498314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498314 prefixEnd_1498314 := by exact prefixLift 1498314
  have htrace : WordTrace (prefixWord ++ tailWord_1498314) baseStart_1498314 baseEnd_1498314 := by
    simpa [prefixWord, tailWord_1498314, baseEnd_1498314] using wordTrace_append hprefix tailTrace_1498314
  have hstable : (prefixWord ++ tailWord_1498314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498314).length < 2 ^ (prefixWord ++ tailWord_1498314).sum := by decide
  have hdescent : baseEnd_1498314 < baseStart_1498314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498327 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 1, 4]
def baseStart_1498327 : Nat := 118140960795 + 1498327 * 2 ^ 59
def prefixEnd_1498327 : Nat := 4983230072969 + 3 ^ 40 * 1498327 * 2
def baseEnd_1498327 : Nat := 512907952406176348281217

theorem tailTrace_1498327 : CollatzResearch.WordTrace tailWord_1498327 prefixEnd_1498327 512907952406176348281217 := by
  unfold tailWord_1498327
  simp only [CollatzResearch.WordTrace]
  refine ⟨54648475242824647723957235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36432316828549765149304823 54648475242824647723957235)
  ·
    refine ⟨81972712864236971585935853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54648475242824647723957235 81972712864236971585935853)
    ·
      refine ⟨30739767324088864344725945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81972712864236971585935853 30739767324088864344725945)
      ·
        refine ⟨23054825493066648258544459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30739767324088864344725945 23054825493066648258544459)
        ·
          refine ⟨34582238239599972387816689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23054825493066648258544459 34582238239599972387816689)
          ·
            refine ⟨25936678679699979290862517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34582238239599972387816689 25936678679699979290862517)
            ·
              refine ⟨2431563626221873058518361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25936678679699979290862517 2431563626221873058518361)
              ·
                refine ⟨1823672719666404793888771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431563626221873058518361 1823672719666404793888771)
                ·
                  refine ⟨2735509079499607190833157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823672719666404793888771 2735509079499607190833157)
                  ·
                    refine ⟨512907952406176348281217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2735509079499607190833157 512907952406176348281217)
                    ·
                      rfl

theorem cell22_1498327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_1498327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498327 prefixEnd_1498327 := by exact prefixLift 1498327
  have htrace : WordTrace (prefixWord ++ tailWord_1498327) baseStart_1498327 baseEnd_1498327 := by
    simpa [prefixWord, tailWord_1498327, baseEnd_1498327] using wordTrace_append hprefix tailTrace_1498327
  have hstable : (prefixWord ++ tailWord_1498327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498327).length < 2 ^ (prefixWord ++ tailWord_1498327).sum := by decide
  have hdescent : baseEnd_1498327 < baseStart_1498327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498340 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1498340 : Nat := 118140960795 + 1498340 * 2 ^ 59
def prefixEnd_1498340 : Nat := 4983230072969 + 3 ^ 40 * 1498340 * 2
def baseEnd_1498340 : Nat := 512912402571848647706177

theorem tailTrace_1498340 : CollatzResearch.WordTrace tailWord_1498340 prefixEnd_1498340 512912402571848647706177 := by
  unfold tailWord_1498340
  simp only [CollatzResearch.WordTrace]
  refine ⟨27324474695888775472090237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36432632927851700629453649 27324474695888775472090237)
  ·
    refine ⟨10246678010958290802033839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27324474695888775472090237 10246678010958290802033839)
    ·
      refine ⟨15370017016437436203050759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10246678010958290802033839 15370017016437436203050759)
      ·
        refine ⟨23055025524656154304576139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15370017016437436203050759 23055025524656154304576139)
        ·
          refine ⟨34582538286984231456864209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23055025524656154304576139 34582538286984231456864209)
          ·
            refine ⟨25936903715238173592648157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34582538286984231456864209 25936903715238173592648157)
            ·
              refine ⟨9726338893214315097243059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25936903715238173592648157 9726338893214315097243059)
              ·
                refine ⟨14589508339821472645864589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9726338893214315097243059 14589508339821472645864589)
                ·
                  refine ⟨5471065627433052242199221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14589508339821472645864589 5471065627433052242199221)
                  ·
                    refine ⟨512912402571848647706177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5471065627433052242199221 512912402571848647706177)
                    ·
                      rfl

theorem cell22_1498340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1498340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498340 prefixEnd_1498340 := by exact prefixLift 1498340
  have htrace : WordTrace (prefixWord ++ tailWord_1498340) baseStart_1498340 baseEnd_1498340 := by
    simpa [prefixWord, tailWord_1498340, baseEnd_1498340] using wordTrace_append hprefix tailTrace_1498340
  have hstable : (prefixWord ++ tailWord_1498340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498340).length < 2 ^ (prefixWord ++ tailWord_1498340).sum := by decide
  have hdescent : baseEnd_1498340 < baseStart_1498340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498344 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 1, 4]
def baseStart_1498344 : Nat := 118140960795 + 1498344 * 2 ^ 59
def prefixEnd_1498344 : Nat := 4983230072969 + 3 ^ 40 * 1498344 * 2
def baseEnd_1498344 : Nat := 512913771853593970606165

theorem tailTrace_1498344 : CollatzResearch.WordTrace tailWord_1498344 prefixEnd_1498344 512913771853593970606165 := by
  unfold tailWord_1498344
  simp only [CollatzResearch.WordTrace]
  refine ⟨27324547641881529813663043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36432730189175373084884057 27324547641881529813663043)
  ·
    refine ⟨40986821462822294720494565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27324547641881529813663043 40986821462822294720494565)
    ·
      refine ⟨7685029024279180260092731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40986821462822294720494565 7685029024279180260092731)
      ·
        refine ⟨11527543536418770390139097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7685029024279180260092731 11527543536418770390139097)
        ·
          refine ⟨8645657652314077792604323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11527543536418770390139097 8645657652314077792604323)
          ·
            refine ⟨12968486478471116688906485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8645657652314077792604323 12968486478471116688906485)
            ·
              refine ⟨1215795607356667189584983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12968486478471116688906485 1215795607356667189584983)
              ·
                refine ⟨1823693411035000784377475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215795607356667189584983 1823693411035000784377475)
                ·
                  refine ⟨2735540116552501176566213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823693411035000784377475 2735540116552501176566213)
                  ·
                    refine ⟨512913771853593970606165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2735540116552501176566213 512913771853593970606165)
                    ·
                      rfl

theorem cell22_1498344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_1498344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498344 prefixEnd_1498344 := by exact prefixLift 1498344
  have htrace : WordTrace (prefixWord ++ tailWord_1498344) baseStart_1498344 baseEnd_1498344 := by
    simpa [prefixWord, tailWord_1498344, baseEnd_1498344] using wordTrace_append hprefix tailTrace_1498344
  have hstable : (prefixWord ++ tailWord_1498344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498344).length < 2 ^ (prefixWord ++ tailWord_1498344).sum := by decide
  have hdescent : baseEnd_1498344 < baseStart_1498344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498419 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 3, 3]
def baseStart_1498419 : Nat := 118140960795 + 1498419 * 2 ^ 59
def prefixEnd_1498419 : Nat := 4983230072969 + 3 ^ 40 * 1498419 * 2
def baseEnd_1498419 : Nat := 512939445886318774980935

theorem tailTrace_1498419 : CollatzResearch.WordTrace tailWord_1498419 prefixEnd_1498419 512939445886318774980935 := by
  unfold tailWord_1498419
  simp only [CollatzResearch.WordTrace]
  refine ⟨54651830758491347436306311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36434553838994231624204207 54651830758491347436306311)
  ·
    refine ⟨81977746137737021154459467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54651830758491347436306311 81977746137737021154459467)
    ·
      refine ⟨122966619206605531731689201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81977746137737021154459467 122966619206605531731689201)
      ·
        refine ⟨92224964404954148798766901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122966619206605531731689201 92224964404954148798766901)
        ·
          refine ⟨8646090412964451449884397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92224964404954148798766901 8646090412964451449884397)
          ·
            refine ⟨3242283904861669293706649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8646090412964451449884397 3242283904861669293706649)
            ·
              refine ⟨2431712928646251970279987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3242283904861669293706649 2431712928646251970279987)
              ·
                refine ⟨3647569392969377955419981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431712928646251970279987 3647569392969377955419981)
                ·
                  refine ⟨1367838522363516733282493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3647569392969377955419981 1367838522363516733282493)
                  ·
                    refine ⟨512939445886318774980935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1367838522363516733282493 512939445886318774980935)
                    ·
                      rfl

theorem cell22_1498419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 3].length) (baseStart_1498419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498419 prefixEnd_1498419 := by exact prefixLift 1498419
  have htrace : WordTrace (prefixWord ++ tailWord_1498419) baseStart_1498419 baseEnd_1498419 := by
    simpa [prefixWord, tailWord_1498419, baseEnd_1498419] using wordTrace_append hprefix tailTrace_1498419
  have hstable : (prefixWord ++ tailWord_1498419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498419).length < 2 ^ (prefixWord ++ tailWord_1498419).sum := by decide
  have hdescent : baseEnd_1498419 < baseStart_1498419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498436 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1498436 : Nat := 118140960795 + 1498436 * 2 ^ 59
def prefixEnd_1498436 : Nat := 4983230072969 + 3 ^ 40 * 1498436 * 2
def baseEnd_1498436 : Nat := 512945265333736397305883

theorem tailTrace_1498436 : CollatzResearch.WordTrace tailWord_1498436 prefixEnd_1498436 512945265333736397305883 := by
  unfold tailWord_1498436
  simp only [CollatzResearch.WordTrace]
  refine ⟨27326225399714879669837581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36434967199619839559783441 27326225399714879669837581)
  ·
    refine ⟨10247334524893079876189093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27326225399714879669837581 10247334524893079876189093)
    ·
      refine ⟨1921375223417452476785455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10247334524893079876189093 1921375223417452476785455)
      ·
        refine ⟨2882062835126178715178183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921375223417452476785455 2882062835126178715178183)
        ·
          refine ⟨4323094252689268072767275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882062835126178715178183 4323094252689268072767275)
          ·
            refine ⟨6484641379033902109150913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323094252689268072767275 6484641379033902109150913)
            ·
              refine ⟨4863481034275426581863185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6484641379033902109150913 4863481034275426581863185)
              ·
                refine ⟨3647610775706569936397389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4863481034275426581863185 3647610775706569936397389)
                ·
                  refine ⟨1367854040889963726149021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3647610775706569936397389 1367854040889963726149021)
                  ·
                    refine ⟨512945265333736397305883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1367854040889963726149021 512945265333736397305883)
                    ·
                      rfl

theorem cell22_1498436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1498436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498436 prefixEnd_1498436 := by exact prefixLift 1498436
  have htrace : WordTrace (prefixWord ++ tailWord_1498436) baseStart_1498436 baseEnd_1498436 := by
    simpa [prefixWord, tailWord_1498436, baseEnd_1498436] using wordTrace_append hprefix tailTrace_1498436
  have hstable : (prefixWord ++ tailWord_1498436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498436).length < 2 ^ (prefixWord ++ tailWord_1498436).sum := by decide
  have hdescent : baseEnd_1498436 < baseStart_1498436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498453 : List Nat := [1, 3, 2, 2, 3, 3, 1, 3, 1, 3]
def baseStart_1498453 : Nat := 118140960795 + 1498453 * 2 ^ 59
def prefixEnd_1498453 : Nat := 4983230072969 + 3 ^ 40 * 1498453 * 2
def baseEnd_1498453 : Nat := 512951084781154019630831

theorem tailTrace_1498453 : CollatzResearch.WordTrace tailWord_1498453 prefixEnd_1498453 512951084781154019630831 := by
  unfold tailWord_1498453
  simp only [CollatzResearch.WordTrace]
  refine ⟨54653070840368171243044013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36435380560245447495362675 54653070840368171243044013)
  ·
    refine ⟨20494901565138064216141505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54653070840368171243044013 20494901565138064216141505)
    ·
      refine ⟨15371176173853548162106129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20494901565138064216141505 15371176173853548162106129)
      ·
        refine ⟨11528382130390161121579597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15371176173853548162106129 11528382130390161121579597)
        ·
          refine ⟨4323143298896310420592349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11528382130390161121579597 4323143298896310420592349)
          ·
            refine ⟨1621178737086116407722131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4323143298896310420592349 1621178737086116407722131)
            ·
              refine ⟨2431768105629174611583197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621178737086116407722131 2431768105629174611583197)
              ·
                refine ⟨911913039610940479343699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2431768105629174611583197 911913039610940479343699)
                ·
                  refine ⟨1367869559416410719015549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911913039610940479343699 1367869559416410719015549)
                  ·
                    refine ⟨512951084781154019630831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1367869559416410719015549 512951084781154019630831)
                    ·
                      rfl

theorem cell22_1498453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_1498453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498453 prefixEnd_1498453 := by exact prefixLift 1498453
  have htrace : WordTrace (prefixWord ++ tailWord_1498453) baseStart_1498453 baseEnd_1498453 := by
    simpa [prefixWord, tailWord_1498453, baseEnd_1498453] using wordTrace_append hprefix tailTrace_1498453
  have hstable : (prefixWord ++ tailWord_1498453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498453).length < 2 ^ (prefixWord ++ tailWord_1498453).sum := by decide
  have hdescent : baseEnd_1498453 < baseStart_1498453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498475 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 2, 9]
def baseStart_1498475 : Nat := 118140960795 + 1498475 * 2 ^ 59
def prefixEnd_1498475 : Nat := 4983230072969 + 3 ^ 40 * 1498475 * 2
def baseEnd_1498475 : Nat := 512958615830753295580763

theorem tailTrace_1498475 : CollatzResearch.WordTrace tailWord_1498475 prefixEnd_1498475 512958615830753295580763 := by
  unfold tailWord_1498475
  simp only [CollatzResearch.WordTrace]
  refine ⟨54653873246288469000344879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36435915497525646000229919 54653873246288469000344879)
  ·
    refine ⟨81980809869432703500517319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54653873246288469000344879 81980809869432703500517319)
    ·
      refine ⟨122971214804149055250775979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81980809869432703500517319 122971214804149055250775979)
      ·
        refine ⟨184456822206223582876163969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122971214804149055250775979 184456822206223582876163969)
        ·
          refine ⟨138342616654667687157122977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184456822206223582876163969 138342616654667687157122977)
          ·
            refine ⟨103756962491000765367842233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138342616654667687157122977 103756962491000765367842233)
            ·
              refine ⟨77817721868250574025881675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103756962491000765367842233 77817721868250574025881675)
              ·
                refine ⟨116726582802375861038822513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77817721868250574025881675 116726582802375861038822513)
                ·
                  refine ⟨87544937101781895779116885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116726582802375861038822513 87544937101781895779116885)
                  ·
                    refine ⟨512958615830753295580763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 87544937101781895779116885 512958615830753295580763)
                    ·
                      rfl

theorem cell22_1498475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_1498475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498475 prefixEnd_1498475 := by exact prefixLift 1498475
  have htrace : WordTrace (prefixWord ++ tailWord_1498475) baseStart_1498475 baseEnd_1498475 := by
    simpa [prefixWord, tailWord_1498475, baseEnd_1498475] using wordTrace_append hprefix tailTrace_1498475
  have hstable : (prefixWord ++ tailWord_1498475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498475).length < 2 ^ (prefixWord ++ tailWord_1498475).sum := by decide
  have hdescent : baseEnd_1498475 < baseStart_1498475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498492 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_1498492 : Nat := 118140960795 + 1498492 * 2 ^ 59
def prefixEnd_1498492 : Nat := 4983230072969 + 3 ^ 40 * 1498492 * 2
def baseEnd_1498492 : Nat := 512964435278170917905711

theorem tailTrace_1498492 : CollatzResearch.WordTrace tailWord_1498492 prefixEnd_1498492 512964435278170917905711 := by
  unfold tailWord_1498492
  simp only [CollatzResearch.WordTrace]
  refine ⟨27327246643613440451856865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36436328858151253935809153 27327246643613440451856865)
  ·
    refine ⟨20495434982710080338892649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27327246643613440451856865 20495434982710080338892649)
    ·
      refine ⟨15371576237032560254169487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20495434982710080338892649 15371576237032560254169487)
      ·
        refine ⟨23057364355548840381254231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15371576237032560254169487 23057364355548840381254231)
        ·
          refine ⟨34586046533323260571881347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23057364355548840381254231 34586046533323260571881347)
          ·
            refine ⟨51879069799984890857822021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34586046533323260571881347 51879069799984890857822021)
            ·
              refine ⟨9727325587497167035841629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51879069799984890857822021 9727325587497167035841629)
              ·
                refine ⟨3647747095311437638440611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9727325587497167035841629 3647747095311437638440611)
                ·
                  refine ⟨5471620642967156457660917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647747095311437638440611 5471620642967156457660917)
                  ·
                    refine ⟨512964435278170917905711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5471620642967156457660917 512964435278170917905711)
                    ·
                      rfl

theorem cell22_1498492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_1498492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498492 prefixEnd_1498492 := by exact prefixLift 1498492
  have htrace : WordTrace (prefixWord ++ tailWord_1498492) baseStart_1498492 baseEnd_1498492 := by
    simpa [prefixWord, tailWord_1498492, baseEnd_1498492] using wordTrace_append hprefix tailTrace_1498492
  have hstable : (prefixWord ++ tailWord_1498492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498492).length < 2 ^ (prefixWord ++ tailWord_1498492).sum := by decide
  have hdescent : baseEnd_1498492 < baseStart_1498492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498556 : List Nat := [2, 2, 2, 4, 2, 1, 3, 6]
def baseStart_1498556 : Nat := 118140960795 + 1498556 * 2 ^ 59
def prefixEnd_1498556 : Nat := 4983230072969 + 3 ^ 40 * 1498556 * 2
def baseEnd_1498556 : Nat := 56998482642899564922835

theorem tailTrace_1498556 : CollatzResearch.WordTrace tailWord_1498556 prefixEnd_1498556 56998482642899564922835 := by
  unfold tailWord_1498556
  simp only [CollatzResearch.WordTrace]
  refine ⟨27328413779497509917021761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36437885039330013222695681 27328413779497509917021761)
  ·
    refine ⟨20496310334623132437766321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27328413779497509917021761 20496310334623132437766321)
    ·
      refine ⟨15372232750967349328324741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20496310334623132437766321 15372232750967349328324741)
      ·
        refine ⟨2882293640806377999060889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15372232750967349328324741 2882293640806377999060889)
        ·
          refine ⟨2161720230604783499295667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2882293640806377999060889 2161720230604783499295667)
          ·
            refine ⟨3242580345907175248943501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161720230604783499295667 3242580345907175248943501)
            ·
              refine ⟨1215967629715190718353813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3242580345907175248943501 1215967629715190718353813)
              ·
                refine ⟨56998482642899564922835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1215967629715190718353813 56998482642899564922835)
                ·
                  rfl

theorem cell22_1498556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 6].length) (baseStart_1498556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498556 prefixEnd_1498556 := by exact prefixLift 1498556
  have htrace : WordTrace (prefixWord ++ tailWord_1498556) baseStart_1498556 baseEnd_1498556 := by
    simpa [prefixWord, tailWord_1498556, baseEnd_1498556] using wordTrace_append hprefix tailTrace_1498556
  have hstable : (prefixWord ++ tailWord_1498556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498556).length < 2 ^ (prefixWord ++ tailWord_1498556).sum := by decide
  have hdescent : baseEnd_1498556 < baseStart_1498556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498567 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 7]
def baseStart_1498567 : Nat := 118140960795 + 1498567 * 2 ^ 59
def prefixEnd_1498567 : Nat := 4983230072969 + 3 ^ 40 * 1498567 * 2
def baseEnd_1498567 : Nat := 170996703103631907426827

theorem tailTrace_1498567 : CollatzResearch.WordTrace tailWord_1498567 prefixEnd_1498567 170996703103631907426827 := by
  unfold tailWord_1498567
  simp only [CollatzResearch.WordTrace]
  refine ⟨54657228761955168712693955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36438152507970112475129303 54657228761955168712693955)
  ·
    refine ⟨81985843142932753069040933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54657228761955168712693955 81985843142932753069040933)
    ·
      refine ⟨15372345589299891200445175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81985843142932753069040933 15372345589299891200445175)
      ·
        refine ⟨23058518383949836800667763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15372345589299891200445175 23058518383949836800667763)
        ·
          refine ⟨34587777575924755201001645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23058518383949836800667763 34587777575924755201001645)
          ·
            refine ⟨12970416590971783200375617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34587777575924755201001645 12970416590971783200375617)
            ·
              refine ⟨9727812443228837400281713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12970416590971783200375617 9727812443228837400281713)
              ·
                refine ⟨7295859332421628050211285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9727812443228837400281713 7295859332421628050211285)
                ·
                  refine ⟨170996703103631907426827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7295859332421628050211285 170996703103631907426827)
                  ·
                    rfl

theorem cell22_1498567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 7].length) (baseStart_1498567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498567 prefixEnd_1498567 := by exact prefixLift 1498567
  have htrace : WordTrace (prefixWord ++ tailWord_1498567) baseStart_1498567 baseEnd_1498567 := by
    simpa [prefixWord, tailWord_1498567, baseEnd_1498567] using wordTrace_append hprefix tailTrace_1498567
  have hstable : (prefixWord ++ tailWord_1498567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498567).length < 2 ^ (prefixWord ++ tailWord_1498567).sum := by decide
  have hdescent : baseEnd_1498567 < baseStart_1498567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498571 : List Nat := [1, 1, 1, 1, 3, 3, 3, 5, 1, 3]
def baseStart_1498571 : Nat := 118140960795 + 1498571 * 2 ^ 59
def prefixEnd_1498571 : Nat := 4983230072969 + 3 ^ 40 * 1498571 * 2
def baseEnd_1498571 : Nat := 512991478592641045180469

theorem tailTrace_1498571 : CollatzResearch.WordTrace tailWord_1498571 prefixEnd_1498571 512991478592641045180469 := by
  unfold tailWord_1498571
  simp only [CollatzResearch.WordTrace]
  refine ⟨54657374653940677395839567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36438249769293784930559711 54657374653940677395839567)
  ·
    refine ⟨81986061980911016093759351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54657374653940677395839567 81986061980911016093759351)
    ·
      refine ⟨122979092971366524140639027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81986061980911016093759351 122979092971366524140639027)
      ·
        refine ⟨184468639457049786210958541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122979092971366524140639027 184468639457049786210958541)
        ·
          refine ⟨69175739796393669829109453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184468639457049786210958541 69175739796393669829109453)
          ·
            refine ⟨25940902423647626185916045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69175739796393669829109453 25940902423647626185916045)
            ·
              refine ⟨9727838408867859819718517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25940902423647626185916045 9727838408867859819718517)
              ·
                refine ⟨911984850831361858098611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9727838408867859819718517 911984850831361858098611)
                ·
                  refine ⟨1367977276247042787147917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911984850831361858098611 1367977276247042787147917)
                  ·
                    refine ⟨512991478592641045180469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1367977276247042787147917 512991478592641045180469)
                    ·
                      rfl

theorem cell22_1498571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 1, 3].length) (baseStart_1498571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498571 prefixEnd_1498571 := by exact prefixLift 1498571
  have htrace : WordTrace (prefixWord ++ tailWord_1498571) baseStart_1498571 baseEnd_1498571 := by
    simpa [prefixWord, tailWord_1498571, baseEnd_1498571] using wordTrace_append hprefix tailTrace_1498571
  have hstable : (prefixWord ++ tailWord_1498571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498571).length < 2 ^ (prefixWord ++ tailWord_1498571).sum := by decide
  have hdescent : baseEnd_1498571 < baseStart_1498571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498584 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 5]
def baseStart_1498584 : Nat := 118140960795 + 1498584 * 2 ^ 59
def prefixEnd_1498584 : Nat := 4983230072969 + 3 ^ 40 * 1498584 * 2
def baseEnd_1498584 : Nat := 170998642919437781535143

theorem tailTrace_1498584 : CollatzResearch.WordTrace tailWord_1498584 prefixEnd_1498584 170998642919437781535143 := by
  unfold tailWord_1498584
  simp only [CollatzResearch.WordTrace]
  refine ⟨27328924401446790308031403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36438565868595720410708537 27328924401446790308031403)
  ·
    refine ⟨40993386602170185462047105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27328924401446790308031403 40993386602170185462047105)
    ·
      refine ⟨30745039951627639096535329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40993386602170185462047105 30745039951627639096535329)
      ·
        refine ⟨23058779963720729322401497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30745039951627639096535329 23058779963720729322401497)
        ·
          refine ⟨17294084972790546991801123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23058779963720729322401497 17294084972790546991801123)
          ·
            refine ⟨25941127459185820487701685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17294084972790546991801123 25941127459185820487701685)
            ·
              refine ⟨2431980699298670670722033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25941127459185820487701685 2431980699298670670722033)
              ·
                refine ⟨1823985524474003003041525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431980699298670670722033 1823985524474003003041525)
                ·
                  refine ⟨170998642919437781535143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1823985524474003003041525 170998642919437781535143)
                  ·
                    rfl

theorem cell22_1498584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_1498584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498584 prefixEnd_1498584 := by exact prefixLift 1498584
  have htrace : WordTrace (prefixWord ++ tailWord_1498584) baseStart_1498584 baseEnd_1498584 := by
    simpa [prefixWord, tailWord_1498584, baseEnd_1498584] using wordTrace_append hprefix tailTrace_1498584
  have hstable : (prefixWord ++ tailWord_1498584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498584).length < 2 ^ (prefixWord ++ tailWord_1498584).sum := by decide
  have hdescent : baseEnd_1498584 < baseStart_1498584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498599 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1498599 : Nat := 118140960795 + 1498599 * 2 ^ 59
def prefixEnd_1498599 : Nat := 4983230072969 + 3 ^ 40 * 1498599 * 2
def baseEnd_1498599 : Nat := 513001063564858305480383

theorem tailTrace_1498599 : CollatzResearch.WordTrace tailWord_1498599 prefixEnd_1498599 513001063564858305480383 := by
  unfold tailWord_1498599
  simp only [CollatzResearch.WordTrace]
  refine ⟨54658395897839238177858851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36438930598559492118572567 54658395897839238177858851)
  ·
    refine ⟨81987593846758857266788277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54658395897839238177858851 81987593846758857266788277)
    ·
      refine ⟨7686336923133642868761401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81987593846758857266788277 7686336923133642868761401)
      ·
        refine ⟨5764752692350232151571051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7686336923133642868761401 5764752692350232151571051)
        ·
          refine ⟨8647129038525348227356577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5764752692350232151571051 8647129038525348227356577)
          ·
            refine ⟨6485346778894011170517433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8647129038525348227356577 6485346778894011170517433)
            ·
              refine ⟨4864010084170508377888075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6485346778894011170517433 4864010084170508377888075)
              ·
                refine ⟨7296015126255762566832113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4864010084170508377888075 7296015126255762566832113)
                ·
                  refine ⟨5472011344691821925124085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7296015126255762566832113 5472011344691821925124085)
                  ·
                    refine ⟨513001063564858305480383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5472011344691821925124085 513001063564858305480383)
                    ·
                      rfl

theorem cell22_1498599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1498599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498599 prefixEnd_1498599 := by exact prefixLift 1498599
  have htrace : WordTrace (prefixWord ++ tailWord_1498599) baseStart_1498599 baseEnd_1498599 := by
    simpa [prefixWord, tailWord_1498599, baseEnd_1498599] using wordTrace_append hprefix tailTrace_1498599
  have hstable : (prefixWord ++ tailWord_1498599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498599).length < 2 ^ (prefixWord ++ tailWord_1498599).sum := by decide
  have hdescent : baseEnd_1498599 < baseStart_1498599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498631 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 1, 4]
def baseStart_1498631 : Nat := 118140960795 + 1498631 * 2 ^ 59
def prefixEnd_1498631 : Nat := 4983230072969 + 3 ^ 40 * 1498631 * 2
def baseEnd_1498631 : Nat := 513012017818820888680285

theorem tailTrace_1498631 : CollatzResearch.WordTrace tailWord_1498631 prefixEnd_1498631 513012017818820888680285 := by
  unfold tailWord_1498631
  simp only [CollatzResearch.WordTrace]
  refine ⟨54659563033723307643023747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36439708689148871762015831 54659563033723307643023747)
  ·
    refine ⟨81989344550584961464535621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54659563033723307643023747 81989344550584961464535621)
    ·
      refine ⟨15373002103234680274600429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81989344550584961464535621 15373002103234680274600429)
      ·
        refine ⟨5764875788713005102975161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15373002103234680274600429 5764875788713005102975161)
        ·
          refine ⟨4323656841534753827231371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5764875788713005102975161 4323656841534753827231371)
          ·
            refine ⟨6485485262302130740847057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323656841534753827231371 6485485262302130740847057)
            ·
              refine ⟨4864113946726598055635293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6485485262302130740847057 4864113946726598055635293)
              ·
                refine ⟨1824042730022474270863235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4864113946726598055635293 1824042730022474270863235)
                ·
                  refine ⟨2736064095033711406294853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824042730022474270863235 2736064095033711406294853)
                  ·
                    refine ⟨513012017818820888680285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2736064095033711406294853 513012017818820888680285)
                    ·
                      rfl

theorem cell22_1498631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_1498631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498631 prefixEnd_1498631 := by exact prefixLift 1498631
  have htrace : WordTrace (prefixWord ++ tailWord_1498631) baseStart_1498631 baseEnd_1498631 := by
    simpa [prefixWord, tailWord_1498631, baseEnd_1498631] using wordTrace_append hprefix tailTrace_1498631
  have hstable : (prefixWord ++ tailWord_1498631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498631).length < 2 ^ (prefixWord ++ tailWord_1498631).sum := by decide
  have hdescent : baseEnd_1498631 < baseStart_1498631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498678 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1498678 : Nat := 118140960795 + 1498678 * 2 ^ 59
def prefixEnd_1498678 : Nat := 4983230072969 + 3 ^ 40 * 1498678 * 2
def baseEnd_1498678 : Nat := 513028106879328432755141

theorem tailTrace_1498678 : CollatzResearch.WordTrace tailWord_1498678 prefixEnd_1498678 513028106879328432755141 := by
  unfold tailWord_1498678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416329829034564666874043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36440851509702023113323125 3416329829034564666874043)
  ·
    refine ⟨5124494743551847000311065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3416329829034564666874043 5124494743551847000311065)
    ·
      refine ⟨3843371057663885250233299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5124494743551847000311065 3843371057663885250233299)
      ·
        refine ⟨5765056586495827875349949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843371057663885250233299 5765056586495827875349949)
        ·
          refine ⟨2161896219935935453256231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5765056586495827875349949 2161896219935935453256231)
          ·
            refine ⟨3242844329903903179884347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161896219935935453256231 3242844329903903179884347)
            ·
              refine ⟨4864266494855854769826521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242844329903903179884347 4864266494855854769826521)
              ·
                refine ⟨3648199871141891077369891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4864266494855854769826521 3648199871141891077369891)
                ·
                  refine ⟨5472299806712836616054837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3648199871141891077369891 5472299806712836616054837)
                  ·
                    refine ⟨513028106879328432755141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5472299806712836616054837 513028106879328432755141)
                    ·
                      rfl

theorem cell22_1498678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1498678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498678 prefixEnd_1498678 := by exact prefixLift 1498678
  have htrace : WordTrace (prefixWord ++ tailWord_1498678) baseStart_1498678 baseEnd_1498678 := by
    simpa [prefixWord, tailWord_1498678, baseEnd_1498678] using wordTrace_append hprefix tailTrace_1498678
  have hstable : (prefixWord ++ tailWord_1498678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498678).length < 2 ^ (prefixWord ++ tailWord_1498678).sum := by decide
  have hdescent : baseEnd_1498678 < baseStart_1498678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498753 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 5]
def baseStart_1498753 : Nat := 118140960795 + 1498753 * 2 ^ 59
def prefixEnd_1498753 : Nat := 4983230072969 + 3 ^ 40 * 1498753 * 2
def baseEnd_1498753 : Nat := 171017926970684412376637

theorem tailTrace_1498753 : CollatzResearch.WordTrace tailWord_1498753 prefixEnd_1498753 171017926970684412376637 := by
  unfold tailWord_1498753
  simp only [CollatzResearch.WordTrace]
  refine ⟨54664012739281322478964913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36442675159520881652643275 54664012739281322478964913)
  ·
    refine ⟨40998009554460991859223685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54664012739281322478964913 40998009554460991859223685)
    ·
      refine ⟨7687126791461435973604441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40998009554460991859223685 7687126791461435973604441)
      ·
        refine ⟨5765345093596076980203331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7687126791461435973604441 5765345093596076980203331)
        ·
          refine ⟨8648017640394115470304997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5765345093596076980203331 8648017640394115470304997)
          ·
            refine ⟨1621503307573896650682187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8648017640394115470304997 1621503307573896650682187)
            ·
              refine ⟨2432254961360844976023281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621503307573896650682187 2432254961360844976023281)
              ·
                refine ⟨1824191221020633732017461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2432254961360844976023281 1824191221020633732017461)
                ·
                  refine ⟨171017926970684412376637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1824191221020633732017461 171017926970684412376637)
                  ·
                    rfl

theorem cell22_1498753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 5].length) (baseStart_1498753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498753 prefixEnd_1498753 := by exact prefixLift 1498753
  have htrace : WordTrace (prefixWord ++ tailWord_1498753) baseStart_1498753 baseEnd_1498753 := by
    simpa [prefixWord, tailWord_1498753, baseEnd_1498753] using wordTrace_append hprefix tailTrace_1498753
  have hstable : (prefixWord ++ tailWord_1498753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498753).length < 2 ^ (prefixWord ++ tailWord_1498753).sum := by decide
  have hdescent : baseEnd_1498753 < baseStart_1498753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498770 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_1498770 : Nat := 118140960795 + 1498770 * 2 ^ 59
def prefixEnd_1498770 : Nat := 4983230072969 + 3 ^ 40 * 1498770 * 2
def baseEnd_1498770 : Nat := 171019866786490286484953

theorem tailTrace_1498770 : CollatzResearch.WordTrace tailWord_1498770 prefixEnd_1498770 171019866786490286484953 := by
  unfold tailWord_1498770
  simp only [CollatzResearch.WordTrace]
  refine ⟨13666158195054933595583441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36443088520146489588222509 13666158195054933595583441)
  ·
    refine ⟨10249618646291200196687581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13666158195054933595583441 10249618646291200196687581)
    ·
      refine ⟨3843606992359200073757843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10249618646291200196687581 3843606992359200073757843)
      ·
        refine ⟨5765410488538800110636765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843606992359200073757843 5765410488538800110636765)
        ·
          refine ⟨2162028933202050041488787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5765410488538800110636765 2162028933202050041488787)
          ·
            refine ⟨3243043399803075062233181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162028933202050041488787 3243043399803075062233181)
            ·
              refine ⟨1216141274926153148337443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3243043399803075062233181 1216141274926153148337443)
              ·
                refine ⟨1824211912389229722506165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216141274926153148337443 1824211912389229722506165)
                ·
                  refine ⟨171019866786490286484953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1824211912389229722506165 171019866786490286484953)
                  ·
                    rfl

theorem cell22_1498770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_1498770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498770 prefixEnd_1498770 := by exact prefixLift 1498770
  have htrace : WordTrace (prefixWord ++ tailWord_1498770) baseStart_1498770 baseEnd_1498770 := by
    simpa [prefixWord, tailWord_1498770, baseEnd_1498770] using wordTrace_append hprefix tailTrace_1498770
  have hstable : (prefixWord ++ tailWord_1498770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498770).length < 2 ^ (prefixWord ++ tailWord_1498770).sum := by decide
  have hdescent : baseEnd_1498770 < baseStart_1498770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498809 : List Nat := [1, 2, 1, 4, 1, 1, 12]
def baseStart_1498809 : Nat := 118140960795 + 1498809 * 2 ^ 59
def prefixEnd_1498809 : Nat := 4983230072969 + 3 ^ 40 * 1498809 * 2
def baseEnd_1498809 : Nat := 19002701883573620656657

theorem tailTrace_1498809 : CollatzResearch.WordTrace tailWord_1498809 prefixEnd_1498809 19002701883573620656657 := by
  unfold tailWord_1498809
  simp only [CollatzResearch.WordTrace]
  refine ⟨54666055227078444043003481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36444036818052296028668987 54666055227078444043003481)
  ·
    refine ⟨40999541420308833032252611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54666055227078444043003481 40999541420308833032252611)
    ·
      refine ⟨61499312130463249548378917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40999541420308833032252611 61499312130463249548378917)
      ·
        refine ⟨11531121024461859290321047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61499312130463249548378917 11531121024461859290321047)
        ·
          refine ⟨17296681536692788935481571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11531121024461859290321047 17296681536692788935481571)
          ·
            refine ⟨25945022305039183403222357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17296681536692788935481571 25945022305039183403222357)
            ·
              refine ⟨19002701883573620656657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 25945022305039183403222357 19002701883573620656657)
              ·
                rfl

theorem cell22_1498809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 12].length) (baseStart_1498809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498809 prefixEnd_1498809 := by exact prefixLift 1498809
  have htrace : WordTrace (prefixWord ++ tailWord_1498809) baseStart_1498809 baseEnd_1498809 := by
    simpa [prefixWord, tailWord_1498809, baseEnd_1498809] using wordTrace_append hprefix tailTrace_1498809
  have hstable : (prefixWord ++ tailWord_1498809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498809).length < 2 ^ (prefixWord ++ tailWord_1498809).sum := by decide
  have hdescent : baseEnd_1498809 < baseStart_1498809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498813 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_1498813 : Nat := 118140960795 + 1498813 * 2 ^ 59
def prefixEnd_1498813 : Nat := 4983230072969 + 3 ^ 40 * 1498813 * 2
def baseEnd_1498813 : Nat := 513074320138233080629727

theorem tailTrace_1498813 : CollatzResearch.WordTrace tailWord_1498813 prefixEnd_1498813 513074320138233080629727 := by
  unfold tailWord_1498813
  simp only [CollatzResearch.WordTrace]
  refine ⟨54666201119063952726149093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36444134079375968484099395 54666201119063952726149093)
  ·
    refine ⟨10249912709824491136152955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54666201119063952726149093 10249912709824491136152955)
    ·
      refine ⟨15374869064736736704229433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10249912709824491136152955 15374869064736736704229433)
      ·
        refine ⟨11531151798552552528172075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15374869064736736704229433 11531151798552552528172075)
        ·
          refine ⟨17296727697828828792258113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11531151798552552528172075 17296727697828828792258113)
          ·
            refine ⟨12972545773371621594193585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17296727697828828792258113 12972545773371621594193585)
            ·
              refine ⟨9729409330028716195645189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12972545773371621594193585 9729409330028716195645189)
              ·
                refine ⟨1824264249380384286683473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9729409330028716195645189 1824264249380384286683473)
                ·
                  refine ⟨1368198187035288215012605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1824264249380384286683473 1368198187035288215012605)
                  ·
                    refine ⟨513074320138233080629727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1368198187035288215012605 513074320138233080629727)
                    ·
                      rfl

theorem cell22_1498813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_1498813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498813 prefixEnd_1498813 := by exact prefixLift 1498813
  have htrace : WordTrace (prefixWord ++ tailWord_1498813) baseStart_1498813 baseEnd_1498813 := by
    simpa [prefixWord, tailWord_1498813, baseEnd_1498813] using wordTrace_append hprefix tailTrace_1498813
  have hstable : (prefixWord ++ tailWord_1498813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498813).length < 2 ^ (prefixWord ++ tailWord_1498813).sum := by decide
  have hdescent : baseEnd_1498813 < baseStart_1498813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498871 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 5]
def baseStart_1498871 : Nat := 118140960795 + 1498871 * 2 ^ 59
def prefixEnd_1498871 : Nat := 4983230072969 + 3 ^ 40 * 1498871 * 2
def baseEnd_1498871 : Nat := 171031391574513420893183

theorem tailTrace_1498871 : CollatzResearch.WordTrace tailWord_1498871 prefixEnd_1498871 171031391574513420893183 := by
  unfold tailWord_1498871
  simp only [CollatzResearch.WordTrace]
  refine ⟨54668316552853828631760467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36445544368569219087840311 54668316552853828631760467)
  ·
    refine ⟨82002474829280742947640701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54668316552853828631760467 82002474829280742947640701)
    ·
      refine ⟨30750928060980278605365263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82002474829280742947640701 30750928060980278605365263)
      ·
        refine ⟨46126392091470417908047895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30750928060980278605365263 46126392091470417908047895)
        ·
          refine ⟨69189588137205626862071843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46126392091470417908047895 69189588137205626862071843)
          ·
            refine ⟨103784382205808440293107765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69189588137205626862071843 103784382205808440293107765)
            ·
              refine ⟨9729785831794541277478853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103784382205808440293107765 9729785831794541277478853)
              ·
                refine ⟨1824334843461476489527285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9729785831794541277478853 1824334843461476489527285)
                ·
                  refine ⟨171031391574513420893183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1824334843461476489527285 171031391574513420893183)
                  ·
                    rfl

theorem cell22_1498871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 5].length) (baseStart_1498871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498871 prefixEnd_1498871 := by exact prefixLift 1498871
  have htrace : WordTrace (prefixWord ++ tailWord_1498871) baseStart_1498871 baseEnd_1498871 := by
    simpa [prefixWord, tailWord_1498871, baseEnd_1498871] using wordTrace_append hprefix tailTrace_1498871
  have hstable : (prefixWord ++ tailWord_1498871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498871).length < 2 ^ (prefixWord ++ tailWord_1498871).sum := by decide
  have hdescent : baseEnd_1498871 < baseStart_1498871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498967 : List Nat := [1, 1, 3, 2, 5, 2, 1, 3, 4]
def baseStart_1498967 : Nat := 118140960795 + 1498967 * 2 ^ 59
def prefixEnd_1498967 : Nat := 4983230072969 + 3 ^ 40 * 1498967 * 2
def baseEnd_1498967 : Nat := 171042345828476004093085

theorem tailTrace_1498967 : CollatzResearch.WordTrace tailWord_1498967 prefixEnd_1498967 171042345828476004093085 := by
  unfold tailWord_1498967
  simp only [CollatzResearch.WordTrace]
  refine ⟨54671817960506037027255155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36447878640337358018170103 54671817960506037027255155)
  ·
    refine ⟨82007726940759055540882733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54671817960506037027255155 82007726940759055540882733)
    ·
      refine ⟨30752897602784645827831025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82007726940759055540882733 30752897602784645827831025)
      ·
        refine ⟨23064673202088484370873269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30752897602784645827831025 23064673202088484370873269)
        ·
          refine ⟨2162313112695795409769369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23064673202088484370873269 2162313112695795409769369)
          ·
            refine ⟨1621734834521846557327027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2162313112695795409769369 1621734834521846557327027)
            ·
              refine ⟨2432602251782769835990541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621734834521846557327027 2432602251782769835990541)
              ·
                refine ⟨912225844418538688496453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2432602251782769835990541 912225844418538688496453)
                ·
                  refine ⟨171042345828476004093085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 912225844418538688496453 171042345828476004093085)
                  ·
                    rfl

theorem cell22_1498967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 4].length) (baseStart_1498967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498967 prefixEnd_1498967 := by exact prefixLift 1498967
  have htrace : WordTrace (prefixWord ++ tailWord_1498967) baseStart_1498967 baseEnd_1498967 := by
    simpa [prefixWord, tailWord_1498967, baseEnd_1498967] using wordTrace_append hprefix tailTrace_1498967
  have hstable : (prefixWord ++ tailWord_1498967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498967).length < 2 ^ (prefixWord ++ tailWord_1498967).sum := by decide
  have hdescent : baseEnd_1498967 < baseStart_1498967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498978 : List Nat := [3, 3, 2, 1, 2, 1, 10]
def baseStart_1498978 : Nat := 118140960795 + 1498978 * 2 ^ 59
def prefixEnd_1498978 : Nat := 4983230072969 + 3 ^ 40 * 1498978 * 2
def baseEnd_1498978 : Nat := 19004844555934357416823

theorem tailTrace_1498978 : CollatzResearch.WordTrace tailWord_1498978 prefixEnd_1498978 19004844555934357416823 := by
  unfold tailWord_1498978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13668054790866546476476397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36448146108977457270603725 13668054790866546476476397)
  ·
    refine ⟨5125520546574954928678649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13668054790866546476476397 5125520546574954928678649)
    ·
      refine ⟨3844140409931216196508987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5125520546574954928678649 3844140409931216196508987)
      ·
        refine ⟨5766210614896824294763481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844140409931216196508987 5766210614896824294763481)
        ·
          refine ⟨4324657961172618221072611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5766210614896824294763481 4324657961172618221072611)
          ·
            refine ⟨6486986941758927331608917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324657961172618221072611 6486986941758927331608917)
            ·
              refine ⟨19004844555934357416823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6486986941758927331608917 19004844555934357416823)
              ·
                rfl

theorem cell22_1498978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 10].length) (baseStart_1498978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498978 prefixEnd_1498978 := by exact prefixLift 1498978
  have htrace : WordTrace (prefixWord ++ tailWord_1498978) baseStart_1498978 baseEnd_1498978 := by
    simpa [prefixWord, tailWord_1498978, baseEnd_1498978] using wordTrace_append hprefix tailTrace_1498978
  have hstable : (prefixWord ++ tailWord_1498978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498978).length < 2 ^ (prefixWord ++ tailWord_1498978).sum := by decide
  have hdescent : baseEnd_1498978 < baseStart_1498978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
