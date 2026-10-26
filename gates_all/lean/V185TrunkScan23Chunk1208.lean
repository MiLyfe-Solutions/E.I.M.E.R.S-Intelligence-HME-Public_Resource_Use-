import V185TrunkScan23Chunk1207

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7156063 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 1, 7]
def baseStart_7156063 : Nat := 118140960795 + 7156063 * 2 ^ 59
def prefixEnd_7156063 : Nat := 4983230072969 + 3 ^ 40 * 7156063 * 2
def baseEnd_7156063 : Nat := 1224833304285113534767457

theorem tailTrace_7156063 : CollatzResearch.WordTrace tailWord_7156063 prefixEnd_7156063 1224833304285113534767457 := by
  unfold tailWord_7156063
  simp only [CollatzResearch.WordTrace]
  refine ⟨261003059873813384104520843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174002039915875589403013895 261003059873813384104520843)
  ·
    refine ⟨391504589810720076156781265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261003059873813384104520843 391504589810720076156781265)
    ·
      refine ⟨293628442358040057117585949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391504589810720076156781265 293628442358040057117585949)
      ·
        refine ⟨110110665884265021419094731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293628442358040057117585949 110110665884265021419094731)
        ·
          refine ⟨165165998826397532128642097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110110665884265021419094731 165165998826397532128642097)
          ·
            refine ⟨123874499119798149096481573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165165998826397532128642097 123874499119798149096481573)
            ·
              refine ⟨23226468584962152955590295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123874499119798149096481573 23226468584962152955590295)
              ·
                refine ⟨34839702877443229433385443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23226468584962152955590295 34839702877443229433385443)
                ·
                  refine ⟨52259554316164844150078165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34839702877443229433385443 52259554316164844150078165)
                  ·
                    refine ⟨1224833304285113534767457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52259554316164844150078165 1224833304285113534767457)
                    ·
                      rfl

theorem cell23_7156063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_7156063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156063 prefixEnd_7156063 := by exact prefixLift 7156063
  have htrace : WordTrace (prefixWord ++ tailWord_7156063) baseStart_7156063 baseEnd_7156063 := by
    simpa [prefixWord, tailWord_7156063, baseEnd_7156063] using wordTrace_append hprefix tailTrace_7156063
  have hstable : (prefixWord ++ tailWord_7156063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156063).length < 2 ^ (prefixWord ++ tailWord_7156063).sum := by decide
  have hdescent : baseEnd_7156063 < baseStart_7156063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156073 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_7156073 : Nat := 118140960795 + 7156073 * 2 ^ 59
def prefixEnd_7156073 : Nat := 4983230072969 + 3 ^ 40 * 7156073 * 2
def baseEnd_7156073 : Nat := 3674505047661885565177325

theorem tailTrace_7156073 : CollatzResearch.WordTrace tailWord_7156073 prefixEnd_7156073 3674505047661885565177325 := by
  unfold tailWord_7156073
  simp only [CollatzResearch.WordTrace]
  refine ⟨261003424603777155812384873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174002283069184770541589915 261003424603777155812384873)
  ·
    refine ⟨195752568452832866859288655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261003424603777155812384873 195752568452832866859288655)
    ·
      refine ⟨293628852679249300288932983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195752568452832866859288655 293628852679249300288932983)
      ·
        refine ⟨440443279018873950433399475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293628852679249300288932983 440443279018873950433399475)
        ·
          refine ⟨660664918528310925650099213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440443279018873950433399475 660664918528310925650099213)
          ·
            refine ⟨247749344448116597118787205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 660664918528310925650099213 247749344448116597118787205)
            ·
              refine ⟨46453002084021861959772601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247749344448116597118787205 46453002084021861959772601)
              ·
                refine ⟨34839751563016396469829451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46453002084021861959772601 34839751563016396469829451)
                ·
                  refine ⟨52259627344524594704744177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34839751563016396469829451 52259627344524594704744177)
                  ·
                    refine ⟨39194720508393446028558133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52259627344524594704744177 39194720508393446028558133)
                    ·
                      refine ⟨3674505047661885565177325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39194720508393446028558133 3674505047661885565177325)
                      ·
                        rfl

theorem cell23_7156073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_7156073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156073 prefixEnd_7156073 := by exact prefixLift 7156073
  have htrace : WordTrace (prefixWord ++ tailWord_7156073) baseStart_7156073 baseEnd_7156073 := by
    simpa [prefixWord, tailWord_7156073, baseEnd_7156073] using wordTrace_append hprefix tailTrace_7156073
  have hstable : (prefixWord ++ tailWord_7156073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156073).length < 2 ^ (prefixWord ++ tailWord_7156073).sum := by decide
  have hdescent : baseEnd_7156073 < baseStart_7156073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156080 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 2, 5]
def baseStart_7156080 : Nat := 118140960795 + 7156080 * 2 ^ 59
def prefixEnd_7156080 : Nat := 4983230072969 + 3 ^ 40 * 7156080 * 2
def baseEnd_7156080 : Nat := 1224836214008822345929931

theorem tailTrace_7156080 : CollatzResearch.WordTrace tailWord_7156080 prefixEnd_7156080 1224836214008822345929931 := by
  unfold tailWord_7156080
  simp only [CollatzResearch.WordTrace]
  refine ⟨130501839957375898003944847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174002453276501197338593129 130501839957375898003944847)
  ·
    refine ⟨195752759936063847005917271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130501839957375898003944847 195752759936063847005917271)
    ·
      refine ⟨293629139904095770508875907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195752759936063847005917271 293629139904095770508875907)
      ·
        refine ⟨440443709856143655763313861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293629139904095770508875907 440443709856143655763313861)
        ·
          refine ⟨82583195598026935455621349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440443709856143655763313861 82583195598026935455621349)
          ·
            refine ⟨15484349174630050397929003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82583195598026935455621349 15484349174630050397929003)
            ·
              refine ⟨23226523761945075596893505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15484349174630050397929003 23226523761945075596893505)
              ·
                refine ⟨17419892821458806697670129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23226523761945075596893505 17419892821458806697670129)
                ·
                  refine ⟨13064919616094105023252597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17419892821458806697670129 13064919616094105023252597)
                  ·
                    refine ⟨1224836214008822345929931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13064919616094105023252597 1224836214008822345929931)
                    ·
                      rfl

theorem cell23_7156080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_7156080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156080 prefixEnd_7156080 := by exact prefixLift 7156080
  have htrace : WordTrace (prefixWord ++ tailWord_7156080) baseStart_7156080 baseEnd_7156080 := by
    simpa [prefixWord, tailWord_7156080, baseEnd_7156080] using wordTrace_append hprefix tailTrace_7156080
  have hstable : (prefixWord ++ tailWord_7156080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156080).length < 2 ^ (prefixWord ++ tailWord_7156080).sum := by decide
  have hdescent : baseEnd_7156080 < baseStart_7156080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156100 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_7156100 : Nat := 118140960795 + 7156100 * 2 ^ 59
def prefixEnd_7156100 : Nat := 4983230072969 + 3 ^ 40 * 7156100 * 2
def baseEnd_7156100 : Nat := 3674518911639556959539701

theorem tailTrace_7156100 : CollatzResearch.WordTrace tailWord_7156100 prefixEnd_7156100 3674518911639556959539701 := by
  unfold tailWord_7156100
  simp only [CollatzResearch.WordTrace]
  refine ⟨130502204687339669711808877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174002939583119559615745169 130502204687339669711808877)
  ·
    refine ⟨48938326757752376141928329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130502204687339669711808877 48938326757752376141928329)
    ·
      refine ⟨36703745068314282106446247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48938326757752376141928329 36703745068314282106446247)
      ·
        refine ⟨55055617602471423159669371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36703745068314282106446247 55055617602471423159669371)
        ·
          refine ⟨82583426403707134739504057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55055617602471423159669371 82583426403707134739504057)
          ·
            refine ⟨61937569802780351054628043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82583426403707134739504057 61937569802780351054628043)
            ·
              refine ⟨92906354704170526581942065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61937569802780351054628043 92906354704170526581942065)
              ·
                refine ⟨69679766028127894936456549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92906354704170526581942065 69679766028127894936456549)
                ·
                  refine ⟨13064956130273980300585603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69679766028127894936456549 13064956130273980300585603)
                  ·
                    refine ⟨19597434195410970450878405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13064956130273980300585603 19597434195410970450878405)
                    ·
                      refine ⟨3674518911639556959539701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19597434195410970450878405 3674518911639556959539701)
                      ·
                        rfl

theorem cell23_7156100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_7156100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156100 prefixEnd_7156100 := by exact prefixLift 7156100
  have htrace : WordTrace (prefixWord ++ tailWord_7156100) baseStart_7156100 baseEnd_7156100 := by
    simpa [prefixWord, tailWord_7156100, baseEnd_7156100] using wordTrace_append hprefix tailTrace_7156100
  have hstable : (prefixWord ++ tailWord_7156100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156100).length < 2 ^ (prefixWord ++ tailWord_7156100).sum := by decide
  have hdescent : baseEnd_7156100 < baseStart_7156100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156130 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_7156130 : Nat := 118140960795 + 7156130 * 2 ^ 59
def prefixEnd_7156130 : Nat := 4983230072969 + 3 ^ 40 * 7156130 * 2
def baseEnd_7156130 : Nat := 3674534316059191842164563

theorem tailTrace_7156130 : CollatzResearch.WordTrace tailWord_7156130 prefixEnd_7156130 3674534316059191842164563 := by
  unfold tailWord_7156130
  simp only [CollatzResearch.WordTrace]
  refine ⟨65251375891142663636802461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174003669043047103031473229 65251375891142663636802461)
  ·
    refine ⟨24469265959178498863800923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65251375891142663636802461 24469265959178498863800923)
    ·
      refine ⟨36703898938767748295701385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24469265959178498863800923 36703898938767748295701385)
      ·
        refine ⟨27527924204075811221776039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36703898938767748295701385 27527924204075811221776039)
        ·
          refine ⟨41291886306113716832664059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27527924204075811221776039 41291886306113716832664059)
          ·
            refine ⟨61937829459170575248996089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41291886306113716832664059 61937829459170575248996089)
            ·
              refine ⟨46453372094377931436747067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61937829459170575248996089 46453372094377931436747067)
              ·
                refine ⟨69680058141566897155120601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46453372094377931436747067 69680058141566897155120601)
                ·
                  refine ⟨52260043606175172866340451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69680058141566897155120601 52260043606175172866340451)
                  ·
                    refine ⟨78390065409262759299510677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52260043606175172866340451 78390065409262759299510677)
                    ·
                      refine ⟨3674534316059191842164563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78390065409262759299510677 3674534316059191842164563)
                      ·
                        rfl

theorem cell23_7156130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_7156130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156130 prefixEnd_7156130 := by exact prefixLift 7156130
  have htrace : WordTrace (prefixWord ++ tailWord_7156130) baseStart_7156130 baseEnd_7156130 := by
    simpa [prefixWord, tailWord_7156130, baseEnd_7156130] using wordTrace_append hprefix tailTrace_7156130
  have hstable : (prefixWord ++ tailWord_7156130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156130).length < 2 ^ (prefixWord ++ tailWord_7156130).sum := by decide
  have hdescent : baseEnd_7156130 < baseStart_7156130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156163 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 7]
def baseStart_7156163 : Nat := 118140960795 + 7156163 * 2 ^ 59
def prefixEnd_7156163 : Nat := 4983230072969 + 3 ^ 40 * 7156163 * 2
def baseEnd_7156163 : Nat := 3674551260920790213051911

theorem tailTrace_7156163 : CollatzResearch.WordTrace tailWord_7156163 prefixEnd_7156163 3674551260920790213051911 := by
  unfold tailWord_7156163
  simp only [CollatzResearch.WordTrace]
  refine ⟨261006707173451101183161143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174004471448967400788774095 261006707173451101183161143)
  ·
    refine ⟨391510060760176651774741715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261006707173451101183161143 391510060760176651774741715)
    ·
      refine ⟨587265091140264977662112573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391510060760176651774741715 587265091140264977662112573)
      ·
        refine ⟨220224409177599366623292215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587265091140264977662112573 220224409177599366623292215)
        ·
          refine ⟨330336613766399049934938323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220224409177599366623292215 330336613766399049934938323)
          ·
            refine ⟨495504920649598574902407485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330336613766399049934938323 495504920649598574902407485)
            ·
              refine ⟨185814345243599465588402807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 495504920649598574902407485 185814345243599465588402807)
              ·
                refine ⟨278721517865399198382604211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185814345243599465588402807 278721517865399198382604211)
                ·
                  refine ⟨418082276798098797573906317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278721517865399198382604211 418082276798098797573906317)
                  ·
                    refine ⟨156780853799287049090214869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418082276798098797573906317 156780853799287049090214869)
                    ·
                      refine ⟨3674551260920790213051911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156780853799287049090214869 3674551260920790213051911)
                      ·
                        rfl

theorem cell23_7156163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_7156163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156163 prefixEnd_7156163 := by exact prefixLift 7156163
  have htrace : WordTrace (prefixWord ++ tailWord_7156163) baseStart_7156163 baseEnd_7156163 := by
    simpa [prefixWord, tailWord_7156163, baseEnd_7156163] using wordTrace_append hprefix tailTrace_7156163
  have hstable : (prefixWord ++ tailWord_7156163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156163).length < 2 ^ (prefixWord ++ tailWord_7156163).sum := by decide
  have hdescent : baseEnd_7156163 < baseStart_7156163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156167 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_7156167 : Nat := 118140960795 + 7156167 * 2 ^ 59
def prefixEnd_7156167 : Nat := 4983230072969 + 3 ^ 40 * 7156167 * 2
def baseEnd_7156167 : Nat := 3674553314843408197401893

theorem tailTrace_7156167 : CollatzResearch.WordTrace tailWord_7156167 prefixEnd_7156167 3674553314843408197401893 := by
  unfold tailWord_7156167
  simp only [CollatzResearch.WordTrace]
  refine ⟨261006853065436609866306755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174004568710291073244204503 261006853065436609866306755)
  ·
    refine ⟨391510279598154914799460133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261006853065436609866306755 391510279598154914799460133)
    ·
      refine ⟨73408177424654046524898775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391510279598154914799460133 73408177424654046524898775)
      ·
        refine ⟨110112266136981069787348163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73408177424654046524898775 110112266136981069787348163)
        ·
          refine ⟨165168399205471604681022245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110112266136981069787348163 165168399205471604681022245)
          ·
            refine ⟨30969074851025925877691671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165168399205471604681022245 30969074851025925877691671)
            ·
              refine ⟨46453612276538888816537507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30969074851025925877691671 46453612276538888816537507)
              ·
                refine ⟨69680418414808333224806261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46453612276538888816537507 69680418414808333224806261)
                ·
                  refine ⟨6532539226388281239825587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69680418414808333224806261 6532539226388281239825587)
                  ·
                    refine ⟨9798808839582421859738381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6532539226388281239825587 9798808839582421859738381)
                    ·
                      refine ⟨3674553314843408197401893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9798808839582421859738381 3674553314843408197401893)
                      ·
                        rfl

theorem cell23_7156167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_7156167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156167 prefixEnd_7156167 := by exact prefixLift 7156167
  have htrace : WordTrace (prefixWord ++ tailWord_7156167) baseStart_7156167 baseEnd_7156167 := by
    simpa [prefixWord, tailWord_7156167, baseEnd_7156167] using wordTrace_append hprefix tailTrace_7156167
  have hstable : (prefixWord ++ tailWord_7156167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156167).length < 2 ^ (prefixWord ++ tailWord_7156167).sum := by decide
  have hdescent : baseEnd_7156167 < baseStart_7156167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156170 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_7156170 : Nat := 118140960795 + 7156170 * 2 ^ 59
def prefixEnd_7156170 : Nat := 4983230072969 + 3 ^ 40 * 7156170 * 2
def baseEnd_7156170 : Nat := 1224851618428457228554793

theorem tailTrace_7156170 : CollatzResearch.WordTrace tailWord_7156170 prefixEnd_7156170 1224851618428457228554793 := by
  unfold tailWord_7156170
  simp only [CollatzResearch.WordTrace]
  refine ⟨65251740621106435344666491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174004641656283827585777309 65251740621106435344666491)
  ·
    refine ⟨97877610931659653016999737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65251740621106435344666491 97877610931659653016999737)
    ·
      refine ⟨73408208198744739762749803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97877610931659653016999737 73408208198744739762749803)
      ·
        refine ⟨110112312298117109644124705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73408208198744739762749803 110112312298117109644124705)
        ·
          refine ⟨82584234223587832233093529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110112312298117109644124705 82584234223587832233093529)
          ·
            refine ⟨61938175667690874174820147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82584234223587832233093529 61938175667690874174820147)
            ·
              refine ⟨92907263501536311262230221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61938175667690874174820147 92907263501536311262230221)
              ·
                refine ⟨34840223813076116723336333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92907263501536311262230221 34840223813076116723336333)
                ·
                  refine ⟨13065083929903543771251125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34840223813076116723336333 13065083929903543771251125)
                  ·
                    refine ⟨1224851618428457228554793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13065083929903543771251125 1224851618428457228554793)
                    ·
                      rfl

theorem cell23_7156170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_7156170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156170 prefixEnd_7156170 := by exact prefixLift 7156170
  have htrace : WordTrace (prefixWord ++ tailWord_7156170) baseStart_7156170 baseEnd_7156170 := by
    simpa [prefixWord, tailWord_7156170, baseEnd_7156170] using wordTrace_append hprefix tailTrace_7156170
  have hstable : (prefixWord ++ tailWord_7156170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156170).length < 2 ^ (prefixWord ++ tailWord_7156170).sum := by decide
  have hdescent : baseEnd_7156170 < baseStart_7156170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156178 : List Nat := [3, 2, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_7156178 : Nat := 118140960795 + 7156178 * 2 ^ 59
def prefixEnd_7156178 : Nat := 4983230072969 + 3 ^ 40 * 7156178 * 2
def baseEnd_7156178 : Nat := 1224852987710202551454781

theorem tailTrace_7156178 : CollatzResearch.WordTrace tailWord_7156178 prefixEnd_7156178 1224852987710202551454781 := by
  unfold tailWord_7156178
  simp only [CollatzResearch.WordTrace]
  refine ⟨65251813567099189686239297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174004836178931172496638125 65251813567099189686239297)
  ·
    refine ⟨48938860175324392264679473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65251813567099189686239297 48938860175324392264679473)
    ·
      refine ⟨36704145131493294198509605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48938860175324392264679473 36704145131493294198509605)
      ·
        refine ⟨6882027212154992662220551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36704145131493294198509605 6882027212154992662220551)
        ·
          refine ⟨10323040818232488993330827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6882027212154992662220551 10323040818232488993330827)
          ·
            refine ⟨15484561227348733489996241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10323040818232488993330827 15484561227348733489996241)
            ·
              refine ⟨11613420920511550117497181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15484561227348733489996241 11613420920511550117497181)
              ·
                refine ⟨4355032845191831294061443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11613420920511550117497181 4355032845191831294061443)
                ·
                  refine ⟨6532549267787746941092165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355032845191831294061443 6532549267787746941092165)
                  ·
                    refine ⟨1224852987710202551454781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532549267787746941092165 1224852987710202551454781)
                    ·
                      rfl

theorem cell23_7156178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_7156178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156178 prefixEnd_7156178 := by exact prefixLift 7156178
  have htrace : WordTrace (prefixWord ++ tailWord_7156178) baseStart_7156178 baseEnd_7156178 := by
    simpa [prefixWord, tailWord_7156178, baseEnd_7156178] using wordTrace_append hprefix tailTrace_7156178
  have hstable : (prefixWord ++ tailWord_7156178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156178).length < 2 ^ (prefixWord ++ tailWord_7156178).sum := by decide
  have hdescent : baseEnd_7156178 < baseStart_7156178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156217 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 2, 4]
def baseStart_7156217 : Nat := 118140960795 + 7156217 * 2 ^ 59
def prefixEnd_7156217 : Nat := 4983230072969 + 3 ^ 40 * 7156217 * 2
def baseEnd_7156217 : Nat := 1224859662958711000592221

theorem tailTrace_7156217 : CollatzResearch.WordTrace tailWord_7156217 prefixEnd_7156217 1224859662958711000592221 := by
  unfold tailWord_7156217
  simp only [CollatzResearch.WordTrace]
  refine ⟨261008676715255468405626905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174005784476836978937084603 261008676715255468405626905)
  ·
    refine ⟨195756507536441601304220179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261008676715255468405626905 195756507536441601304220179)
    ·
      refine ⟨293634761304662401956330269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195756507536441601304220179 293634761304662401956330269)
      ·
        refine ⟨110113035489248400733623851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293634761304662401956330269 110113035489248400733623851)
        ·
          refine ⟨165169553233872601100435777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110113035489248400733623851 165169553233872601100435777)
          ·
            refine ⟨123877164925404450825326833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165169553233872601100435777 123877164925404450825326833)
            ·
              refine ⟨92907873694053338118995125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123877164925404450825326833 92907873694053338118995125)
              ·
                refine ⟨8710113158817500448655793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92907873694053338118995125 8710113158817500448655793)
                ·
                  refine ⟨6532584869113125336491845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8710113158817500448655793 6532584869113125336491845)
                  ·
                    refine ⟨1224859662958711000592221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532584869113125336491845 1224859662958711000592221)
                    ·
                      rfl

theorem cell23_7156217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 4].length) (baseStart_7156217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156217 prefixEnd_7156217 := by exact prefixLift 7156217
  have htrace : WordTrace (prefixWord ++ tailWord_7156217) baseStart_7156217 baseEnd_7156217 := by
    simpa [prefixWord, tailWord_7156217, baseEnd_7156217] using wordTrace_append hprefix tailTrace_7156217
  have hstable : (prefixWord ++ tailWord_7156217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156217).length < 2 ^ (prefixWord ++ tailWord_7156217).sum := by decide
  have hdescent : baseEnd_7156217 < baseStart_7156217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156241 : List Nat := [1, 2, 2, 1, 1, 2, 2, 7, 1, 2, 2]
def baseStart_7156241 : Nat := 118140960795 + 7156241 * 2 ^ 59
def prefixEnd_7156241 : Nat := 4983230072969 + 3 ^ 40 * 7156241 * 2
def baseEnd_7156241 : Nat := 3674591312411840907876553

theorem tailTrace_7156241 : CollatzResearch.WordTrace tailWord_7156241 prefixEnd_7156241 3674591312411840907876553 := by
  unfold tailWord_7156241
  simp only [CollatzResearch.WordTrace]
  refine ⟨261009552067168520504500577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174006368044779013669667051 261009552067168520504500577)
  ·
    refine ⟨195757164050376390378375433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261009552067168520504500577 195757164050376390378375433)
    ·
      refine ⟨146817873037782292783781575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195757164050376390378375433 146817873037782292783781575)
      ·
        refine ⟨220226809556673439175672363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146817873037782292783781575 220226809556673439175672363)
        ·
          refine ⟨330340214335010158763508545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220226809556673439175672363 330340214335010158763508545)
          ·
            refine ⟨247755160751257619072631409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330340214335010158763508545 247755160751257619072631409)
            ·
              refine ⟨185816370563443214304473557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247755160751257619072631409 185816370563443214304473557)
              ·
                refine ⟨4355071185080700335261099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 185816370563443214304473557 4355071185080700335261099)
                ·
                  refine ⟨6532606777621050502891649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355071185080700335261099 6532606777621050502891649)
                  ·
                    refine ⟨4899455083215787877168737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6532606777621050502891649 4899455083215787877168737)
                    ·
                      refine ⟨3674591312411840907876553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4899455083215787877168737 3674591312411840907876553)
                      ·
                        rfl

theorem cell23_7156241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 1, 2, 2].length) (baseStart_7156241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156241 prefixEnd_7156241 := by exact prefixLift 7156241
  have htrace : WordTrace (prefixWord ++ tailWord_7156241) baseStart_7156241 baseEnd_7156241 := by
    simpa [prefixWord, tailWord_7156241, baseEnd_7156241] using wordTrace_append hprefix tailTrace_7156241
  have hstable : (prefixWord ++ tailWord_7156241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156241).length < 2 ^ (prefixWord ++ tailWord_7156241).sum := by decide
  have hdescent : baseEnd_7156241 < baseStart_7156241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156244 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7156244 : Nat := 118140960795 + 7156244 * 2 ^ 59
def prefixEnd_7156244 : Nat := 4983230072969 + 3 ^ 40 * 7156244 * 2
def baseEnd_7156244 : Nat := 3674592852853804396139039

theorem tailTrace_7156244 : CollatzResearch.WordTrace tailWord_7156244 prefixEnd_7156244 3674592852853804396139039 := by
  unfold tailWord_7156244
  simp only [CollatzResearch.WordTrace]
  refine ⟨130504830743078826008429893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174006440990771768011239857 130504830743078826008429893)
  ·
    refine ⟨24469655764327279876580605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130504830743078826008429893 24469655764327279876580605)
    ·
      refine ⟨9176120911622729953717727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24469655764327279876580605 9176120911622729953717727)
      ·
        refine ⟨13764181367434094930576591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9176120911622729953717727 13764181367434094930576591)
        ·
          refine ⟨20646272051151142395864887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13764181367434094930576591 20646272051151142395864887)
          ·
            refine ⟨30969408076726713593797331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20646272051151142395864887 30969408076726713593797331)
            ·
              refine ⟨46454112115090070390695997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30969408076726713593797331 46454112115090070390695997)
              ·
                refine ⟨17420292043158776396510999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46454112115090070390695997 17420292043158776396510999)
                ·
                  refine ⟨26130438064738164594766499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17420292043158776396510999 26130438064738164594766499)
                  ·
                    refine ⟨39195657097107246892149749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26130438064738164594766499 39195657097107246892149749)
                    ·
                      refine ⟨3674592852853804396139039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39195657097107246892149749 3674592852853804396139039)
                      ·
                        rfl

theorem cell23_7156244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7156244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156244 prefixEnd_7156244 := by exact prefixLift 7156244
  have htrace : WordTrace (prefixWord ++ tailWord_7156244) baseStart_7156244 baseEnd_7156244 := by
    simpa [prefixWord, tailWord_7156244, baseEnd_7156244] using wordTrace_append hprefix tailTrace_7156244
  have hstable : (prefixWord ++ tailWord_7156244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156244).length < 2 ^ (prefixWord ++ tailWord_7156244).sum := by decide
  have hdescent : baseEnd_7156244 < baseStart_7156244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156278 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_7156278 : Nat := 118140960795 + 7156278 * 2 ^ 59
def prefixEnd_7156278 : Nat := 4983230072969 + 3 ^ 40 * 7156278 * 2
def baseEnd_7156278 : Nat := 3674610311196057263113883

theorem tailTrace_7156278 : CollatzResearch.WordTrace tailWord_7156278 prefixEnd_7156278 3674610311196057263113883 := by
  unfold tailWord_7156278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16313181348002154738974843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174007267712022983882398325 16313181348002154738974843)
  ·
    refine ⟨24469772022003232108462265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16313181348002154738974843 24469772022003232108462265)
    ·
      refine ⟨18352329016502424081346699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24469772022003232108462265 18352329016502424081346699)
      ·
        refine ⟨27528493524753636122020049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18352329016502424081346699 27528493524753636122020049)
        ·
          refine ⟨20646370143565227091515037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27528493524753636122020049 20646370143565227091515037)
          ·
            refine ⟨7742388803836960159318139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20646370143565227091515037 7742388803836960159318139)
            ·
              refine ⟨11613583205755440238977209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7742388803836960159318139 11613583205755440238977209)
              ·
                refine ⟨8710187404316580179232907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11613583205755440238977209 8710187404316580179232907)
                ·
                  refine ⟨13065281106474870268849361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8710187404316580179232907 13065281106474870268849361)
                  ·
                    refine ⟨9798960829856152701637021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13065281106474870268849361 9798960829856152701637021)
                    ·
                      refine ⟨3674610311196057263113883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9798960829856152701637021 3674610311196057263113883)
                      ·
                        rfl

theorem cell23_7156278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_7156278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156278 prefixEnd_7156278 := by exact prefixLift 7156278
  have htrace : WordTrace (prefixWord ++ tailWord_7156278) baseStart_7156278 baseEnd_7156278 := by
    simpa [prefixWord, tailWord_7156278, baseEnd_7156278] using wordTrace_append hprefix tailTrace_7156278
  have hstable : (prefixWord ++ tailWord_7156278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156278).length < 2 ^ (prefixWord ++ tailWord_7156278).sum := by decide
  have hdescent : baseEnd_7156278 < baseStart_7156278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156387 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 4]
def baseStart_7156387 : Nat := 118140960795 + 7156387 * 2 ^ 59
def prefixEnd_7156387 : Nat := 4983230072969 + 3 ^ 40 * 7156387 * 2
def baseEnd_7156387 : Nat := 3674666280587397336650881

theorem tailTrace_7156387 : CollatzResearch.WordTrace tailWord_7156387 prefixEnd_7156387 3674666280587397336650881 := by
  unfold tailWord_7156387
  simp only [CollatzResearch.WordTrace]
  refine ⟨261014877124639587439315415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174009918083093058292876943 261014877124639587439315415)
  ·
    refine ⟨391522315686959381158973123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261014877124639587439315415 391522315686959381158973123)
    ·
      refine ⟨587283473530439071738459685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391522315686959381158973123 587283473530439071738459685)
      ·
        refine ⟨110115651286957325950961191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 587283473530439071738459685 110115651286957325950961191)
        ·
          refine ⟨165173476930435988926441787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110115651286957325950961191 165173476930435988926441787)
          ·
            refine ⟨247760215395653983389662681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165173476930435988926441787 247760215395653983389662681)
            ·
              refine ⟨185820161546740487542247011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247760215395653983389662681 185820161546740487542247011)
              ·
                refine ⟨278730242320110731313370517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185820161546740487542247011 278730242320110731313370517)
                ·
                  refine ⟨13065480108755190530314243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 278730242320110731313370517 13065480108755190530314243)
                  ·
                    refine ⟨19598220163132785795471365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13065480108755190530314243 19598220163132785795471365)
                    ·
                      refine ⟨3674666280587397336650881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19598220163132785795471365 3674666280587397336650881)
                      ·
                        rfl

theorem cell23_7156387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_7156387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156387 prefixEnd_7156387 := by exact prefixLift 7156387
  have htrace : WordTrace (prefixWord ++ tailWord_7156387) baseStart_7156387 baseEnd_7156387 := by
    simpa [prefixWord, tailWord_7156387, baseEnd_7156387] using wordTrace_append hprefix tailTrace_7156387
  have hstable : (prefixWord ++ tailWord_7156387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156387).length < 2 ^ (prefixWord ++ tailWord_7156387).sum := by decide
  have hdescent : baseEnd_7156387 < baseStart_7156387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156422 : List Nat := [6, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_7156422 : Nat := 118140960795 + 7156422 * 2 ^ 59
def prefixEnd_7156422 : Nat := 4983230072969 + 3 ^ 40 * 7156422 * 2
def baseEnd_7156422 : Nat := 408298250267811633301469

theorem tailTrace_7156422 : CollatzResearch.WordTrace tailWord_7156422 prefixEnd_7156422 408298250267811633301469 := by
  unfold tailWord_7156422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8156754802484774638026235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174010769119675192277893013 8156754802484774638026235)
  ·
    refine ⟨12235132203727161957039353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8156754802484774638026235 12235132203727161957039353)
    ·
      refine ⟨9176349152795371467779515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12235132203727161957039353 9176349152795371467779515)
      ·
        refine ⟨13764523729193057201669273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9176349152795371467779515 13764523729193057201669273)
        ·
          refine ⟨10323392796894792901251955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13764523729193057201669273 10323392796894792901251955)
          ·
            refine ⟨15485089195342189351877933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10323392796894792901251955 15485089195342189351877933)
            ·
              refine ⟨5806908448253321006954225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15485089195342189351877933 5806908448253321006954225)
              ·
                refine ⟨4355181336189990755215669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5806908448253321006954225 4355181336189990755215669)
                ·
                  refine ⟨408298250267811633301469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4355181336189990755215669 408298250267811633301469)
                  ·
                    rfl

theorem cell23_7156422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_7156422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156422 prefixEnd_7156422 := by exact prefixLift 7156422
  have htrace : WordTrace (prefixWord ++ tailWord_7156422) baseStart_7156422 baseEnd_7156422 := by
    simpa [prefixWord, tailWord_7156422, baseEnd_7156422] using wordTrace_append hprefix tailTrace_7156422
  have hstable : (prefixWord ++ tailWord_7156422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156422).length < 2 ^ (prefixWord ++ tailWord_7156422).sum := by decide
  have hdescent : baseEnd_7156422 < baseStart_7156422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156424 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_7156424 : Nat := 118140960795 + 7156424 * 2 ^ 59
def prefixEnd_7156424 : Nat := 4983230072969 + 3 ^ 40 * 7156424 * 2
def baseEnd_7156424 : Nat := 3674685279371613691888211

theorem tailTrace_7156424 : CollatzResearch.WordTrace tailWord_7156424 prefixEnd_7156424 3674685279371613691888211 := by
  unfold tailWord_7156424
  simp only [CollatzResearch.WordTrace]
  refine ⟨130508113312752771379206163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174010817750337028505608217 130508113312752771379206163)
  ·
    refine ⟨195762169969129157068809245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130508113312752771379206163 195762169969129157068809245)
    ·
      refine ⟨73410813738423433900803467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195762169969129157068809245 73410813738423433900803467)
      ·
        refine ⟨110116220607635150851205201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73410813738423433900803467 110116220607635150851205201)
        ·
          refine ⟨82587165455726363138403901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110116220607635150851205201 82587165455726363138403901)
          ·
            refine ⟨30970187045897386176901463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82587165455726363138403901 30970187045897386176901463)
            ·
              refine ⟨46455280568846079265352195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30970187045897386176901463 46455280568846079265352195)
              ·
                refine ⟨69682920853269118898028293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46455280568846079265352195 69682920853269118898028293)
                ·
                  refine ⟨13065547659987959793380305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69682920853269118898028293 13065547659987959793380305)
                  ·
                    refine ⟨9799160744990969845035229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13065547659987959793380305 9799160744990969845035229)
                    ·
                      refine ⟨3674685279371613691888211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9799160744990969845035229 3674685279371613691888211)
                      ·
                        rfl

theorem cell23_7156424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_7156424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156424 prefixEnd_7156424 := by exact prefixLift 7156424
  have htrace : WordTrace (prefixWord ++ tailWord_7156424) baseStart_7156424 baseEnd_7156424 := by
    simpa [prefixWord, tailWord_7156424, baseEnd_7156424] using wordTrace_append hprefix tailTrace_7156424
  have hstable : (prefixWord ++ tailWord_7156424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156424).length < 2 ^ (prefixWord ++ tailWord_7156424).sum := by decide
  have hdescent : baseEnd_7156424 < baseStart_7156424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156474 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_7156474 : Nat := 118140960795 + 7156474 * 2 ^ 59
def prefixEnd_7156474 : Nat := 4983230072969 + 3 ^ 40 * 7156474 * 2
def baseEnd_7156474 : Nat := 1224903651134779498754327

theorem tailTrace_7156474 : CollatzResearch.WordTrace tailWord_7156474 prefixEnd_7156474 1224903651134779498754327 := by
  unfold tailWord_7156474
  simp only [CollatzResearch.WordTrace]
  refine ⟨65254512568831100324433119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174012033516882934198488317 65254512568831100324433119)
  ·
    refine ⟨97881768853246650486649679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65254512568831100324433119 97881768853246650486649679)
    ·
      refine ⟨146822653279869975729974519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97881768853246650486649679 146822653279869975729974519)
      ·
        refine ⟨220233979919804963594961779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146822653279869975729974519 220233979919804963594961779)
        ·
          refine ⟨330350969879707445392442669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220233979919804963594961779 330350969879707445392442669)
          ·
            refine ⟨123881613704890292022166001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330350969879707445392442669 123881613704890292022166001)
            ·
              refine ⟨92911210278667719016624501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123881613704890292022166001 92911210278667719016624501)
              ·
                refine ⟨8710425963625098657808547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92911210278667719016624501 8710425963625098657808547)
                ·
                  refine ⟨13065638945437647986712821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8710425963625098657808547 13065638945437647986712821)
                  ·
                    refine ⟨1224903651134779498754327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13065638945437647986712821 1224903651134779498754327)
                    ·
                      rfl

theorem cell23_7156474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_7156474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156474 prefixEnd_7156474 := by exact prefixLift 7156474
  have htrace : WordTrace (prefixWord ++ tailWord_7156474) baseStart_7156474 baseEnd_7156474 := by
    simpa [prefixWord, tailWord_7156474, baseEnd_7156474] using wordTrace_append hprefix tailTrace_7156474
  have hstable : (prefixWord ++ tailWord_7156474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156474).length < 2 ^ (prefixWord ++ tailWord_7156474).sum := by decide
  have hdescent : baseEnd_7156474 < baseStart_7156474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156482 : List Nat := [3, 4, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_7156482 : Nat := 118140960795 + 7156482 * 2 ^ 59
def prefixEnd_7156482 : Nat := 4983230072969 + 3 ^ 40 * 7156482 * 2
def baseEnd_7156482 : Nat := 1224905020416524821654315

theorem tailTrace_7156482 : CollatzResearch.WordTrace tailWord_7156482 prefixEnd_7156482 1224905020416524821654315 := by
  unfold tailWord_7156482
  simp only [CollatzResearch.WordTrace]
  refine ⟨65254585514823854666005925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174012228039530279109349133 65254585514823854666005925)
  ·
    refine ⟨12235234784029472749876111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65254585514823854666005925 12235234784029472749876111)
    ·
      refine ⟨18352852176044209124814167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12235234784029472749876111 18352852176044209124814167)
      ·
        refine ⟨27529278264066313687221251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18352852176044209124814167 27529278264066313687221251)
        ·
          refine ⟨41293917396099470530831877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27529278264066313687221251 41293917396099470530831877)
          ·
            refine ⟨7742609511768650724530977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41293917396099470530831877 7742609511768650724530977)
            ·
              refine ⟨5806957133826488043398233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7742609511768650724530977 5806957133826488043398233)
              ·
                refine ⟨4355217850369866032548675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5806957133826488043398233 4355217850369866032548675)
                ·
                  refine ⟨6532826775554799048823013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355217850369866032548675 6532826775554799048823013)
                  ·
                    refine ⟨1224905020416524821654315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532826775554799048823013 1224905020416524821654315)
                    ·
                      rfl

theorem cell23_7156482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_7156482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156482 prefixEnd_7156482 := by exact prefixLift 7156482
  have htrace : WordTrace (prefixWord ++ tailWord_7156482) baseStart_7156482 baseEnd_7156482 := by
    simpa [prefixWord, tailWord_7156482, baseEnd_7156482] using wordTrace_append hprefix tailTrace_7156482
  have hstable : (prefixWord ++ tailWord_7156482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156482).length < 2 ^ (prefixWord ++ tailWord_7156482).sum := by decide
  have hdescent : baseEnd_7156482 < baseStart_7156482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156504 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 6, 4]
def baseStart_7156504 : Nat := 118140960795 + 7156504 * 2 ^ 59
def prefixEnd_7156504 : Nat := 4983230072969 + 3 ^ 40 * 7156504 * 2
def baseEnd_7156504 : Nat := 1224908785941324459629281

theorem tailTrace_7156504 : CollatzResearch.WordTrace tailWord_7156504 prefixEnd_7156504 1224908785941324459629281 := by
  unfold tailWord_7156504
  simp only [CollatzResearch.WordTrace]
  refine ⟨130509572232607858210662283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174012762976810477614216377 130509572232607858210662283)
  ·
    refine ⟨195764358348911787315993425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130509572232607858210662283 195764358348911787315993425)
    ·
      refine ⟨146823268761683840486995069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195764358348911787315993425 146823268761683840486995069)
      ·
        refine ⟨55058725785631440182623151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146823268761683840486995069 55058725785631440182623151)
        ·
          refine ⟨82588088678447160273934727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55058725785631440182623151 82588088678447160273934727)
          ·
            refine ⟨123882133017670740410902091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82588088678447160273934727 123882133017670740410902091)
            ·
              refine ⟨185823199526506110616353137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123882133017670740410902091 185823199526506110616353137)
              ·
                refine ⟨139367399644879582962264853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185823199526506110616353137 139367399644879582962264853)
                ·
                  refine ⟨6532846858353730451356165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139367399644879582962264853 6532846858353730451356165)
                  ·
                    refine ⟨1224908785941324459629281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532846858353730451356165 1224908785941324459629281)
                    ·
                      rfl

theorem cell23_7156504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_7156504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156504 prefixEnd_7156504 := by exact prefixLift 7156504
  have htrace : WordTrace (prefixWord ++ tailWord_7156504) baseStart_7156504 baseEnd_7156504 := by
    simpa [prefixWord, tailWord_7156504, baseEnd_7156504] using wordTrace_append hprefix tailTrace_7156504
  have hstable : (prefixWord ++ tailWord_7156504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156504).length < 2 ^ (prefixWord ++ tailWord_7156504).sum := by decide
  have hdescent : baseEnd_7156504 < baseStart_7156504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156524 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_7156524 : Nat := 118140960795 + 7156524 * 2 ^ 59
def prefixEnd_7156524 : Nat := 4983230072969 + 3 ^ 40 * 7156524 * 2
def baseEnd_7156524 : Nat := 3674736627437063300637751

theorem tailTrace_7156524 : CollatzResearch.WordTrace tailWord_7156524 prefixEnd_7156524 3674736627437063300637751 := by
  unfold tailWord_7156524
  simp only [CollatzResearch.WordTrace]
  refine ⟨130509936962571629918526313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174013249283428839891368417 130509936962571629918526313)
  ·
    refine ⟨97882452721928722438894735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130509936962571629918526313 97882452721928722438894735)
    ·
      refine ⟨146823679082893083658342103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97882452721928722438894735 146823679082893083658342103)
      ·
        refine ⟨220235518624339625487513155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146823679082893083658342103 220235518624339625487513155)
        ·
          refine ⟨330353277936509438231269733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220235518624339625487513155 330353277936509438231269733)
          ·
            refine ⟨61941239613095519668363075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330353277936509438231269733 61941239613095519668363075)
            ·
              refine ⟨92911859419643279502544613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61941239613095519668363075 92911859419643279502544613)
              ·
                refine ⟨17420973641183114906727115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92911859419643279502544613 17420973641183114906727115)
                ·
                  refine ⟨26131460461774672360090673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17420973641183114906727115 26131460461774672360090673)
                  ·
                    refine ⟨19598595346331004270068005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26131460461774672360090673 19598595346331004270068005)
                    ·
                      refine ⟨3674736627437063300637751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19598595346331004270068005 3674736627437063300637751)
                      ·
                        rfl

theorem cell23_7156524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_7156524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156524 prefixEnd_7156524 := by exact prefixLift 7156524
  have htrace : WordTrace (prefixWord ++ tailWord_7156524) baseStart_7156524 baseEnd_7156524 := by
    simpa [prefixWord, tailWord_7156524, baseEnd_7156524] using wordTrace_append hprefix tailTrace_7156524
  have hstable : (prefixWord ++ tailWord_7156524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156524).length < 2 ^ (prefixWord ++ tailWord_7156524).sum := by decide
  have hdescent : baseEnd_7156524 < baseStart_7156524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156525 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7156525 : Nat := 118140960795 + 7156525 * 2 ^ 59
def prefixEnd_7156525 : Nat := 4983230072969 + 3 ^ 40 * 7156525 * 2
def baseEnd_7156525 : Nat := 1224912380305905932241749

theorem tailTrace_7156525 : CollatzResearch.WordTrace tailWord_7156525 prefixEnd_7156525 1224912380305905932241749 := by
  unfold tailWord_7156525
  simp only [CollatzResearch.WordTrace]
  refine ⟨261019910398139637007839029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174013273598759758005226019 261019910398139637007839029)
  ·
    refine ⟨24470616599825590969484909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261019910398139637007839029 24470616599825590969484909)
    ·
      refine ⟨9176481224934596613556841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24470616599825590969484909 9176481224934596613556841)
      ·
        refine ⟨6882360918700947460167631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9176481224934596613556841 6882360918700947460167631)
        ·
          refine ⟨10323541378051421190251447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6882360918700947460167631 10323541378051421190251447)
          ·
            refine ⟨15485312067077131785377171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10323541378051421190251447 15485312067077131785377171)
            ·
              refine ⟨23227968100615697678065757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15485312067077131785377171 23227968100615697678065757)
              ·
                refine ⟨8710488037730886629274659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23227968100615697678065757 8710488037730886629274659)
                ·
                  refine ⟨13065732056596329943911989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8710488037730886629274659 13065732056596329943911989)
                  ·
                    refine ⟨1224912380305905932241749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13065732056596329943911989 1224912380305905932241749)
                    ·
                      rfl

theorem cell23_7156525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7156525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156525 prefixEnd_7156525 := by exact prefixLift 7156525
  have htrace : WordTrace (prefixWord ++ tailWord_7156525) baseStart_7156525 baseEnd_7156525 := by
    simpa [prefixWord, tailWord_7156525, baseEnd_7156525] using wordTrace_append hprefix tailTrace_7156525
  have hstable : (prefixWord ++ tailWord_7156525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156525).length < 2 ^ (prefixWord ++ tailWord_7156525).sum := by decide
  have hdescent : baseEnd_7156525 < baseStart_7156525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156544 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 3]
def baseStart_7156544 : Nat := 118140960795 + 7156544 * 2 ^ 59
def prefixEnd_7156544 : Nat := 4983230072969 + 3 ^ 40 * 7156544 * 2
def baseEnd_7156544 : Nat := 3674746897050153222387659

theorem tailTrace_7156544 : CollatzResearch.WordTrace tailWord_7156544 prefixEnd_7156544 3674746897050153222387659 := by
  unfold tailWord_7156544
  simp only [CollatzResearch.WordTrace]
  refine ⟨130510301692535401626390343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174013735590047202168520457 130510301692535401626390343)
  ·
    refine ⟨195765452538803102439585515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130510301692535401626390343 195765452538803102439585515)
    ·
      refine ⟨293648178808204653659378273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195765452538803102439585515 293648178808204653659378273)
      ·
        refine ⟨220236134106153490244533705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293648178808204653659378273 220236134106153490244533705)
        ·
          refine ⟨165177100579615117683400279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220236134106153490244533705 165177100579615117683400279)
          ·
            refine ⟨247765650869422676525100419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165177100579615117683400279 247765650869422676525100419)
            ·
              refine ⟨371648476304134014787650629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247765650869422676525100419 371648476304134014787650629)
              ·
                refine ⟨69684089307025127772684493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371648476304134014787650629 69684089307025127772684493)
                ·
                  refine ⟨26131533490134422914756685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69684089307025127772684493 26131533490134422914756685)
                  ·
                    refine ⟨9799325058800408593033757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26131533490134422914756685 9799325058800408593033757)
                    ·
                      refine ⟨3674746897050153222387659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9799325058800408593033757 3674746897050153222387659)
                      ·
                        rfl

theorem cell23_7156544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_7156544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156544 prefixEnd_7156544 := by exact prefixLift 7156544
  have htrace : WordTrace (prefixWord ++ tailWord_7156544) baseStart_7156544 baseEnd_7156544 := by
    simpa [prefixWord, tailWord_7156544, baseEnd_7156544] using wordTrace_append hprefix tailTrace_7156544
  have hstable : (prefixWord ++ tailWord_7156544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156544).length < 2 ^ (prefixWord ++ tailWord_7156544).sum := by decide
  have hdescent : baseEnd_7156544 < baseStart_7156544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156588 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 1, 3, 2]
def baseStart_7156588 : Nat := 118140960795 + 7156588 * 2 ^ 59
def prefixEnd_7156588 : Nat := 4983230072969 + 3 ^ 40 * 7156588 * 2
def baseEnd_7156588 : Nat := 3674769490198951050237457

theorem tailTrace_7156588 : CollatzResearch.WordTrace tailWord_7156588 prefixEnd_7156588 3674769490198951050237457 := by
  unfold tailWord_7156588
  simp only [CollatzResearch.WordTrace]
  refine ⟨130511104098455699383691209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174014805464607599178254945 130511104098455699383691209)
  ·
    refine ⟨97883328073841774537768407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130511104098455699383691209 97883328073841774537768407)
    ·
      refine ⟨146824992110762661806652611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97883328073841774537768407 146824992110762661806652611)
      ·
        refine ⟨220237488166143992709978917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146824992110762661806652611 220237488166143992709978917)
        ·
          refine ⟨41294529031151998633121047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220237488166143992709978917 41294529031151998633121047)
          ·
            refine ⟨61941793546727997949681571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41294529031151998633121047 61941793546727997949681571)
            ·
              refine ⟨92912690320091996924522357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61941793546727997949681571 92912690320091996924522357)
              ·
                refine ⟨8710564717508624711673971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92912690320091996924522357 8710564717508624711673971)
                ·
                  refine ⟨13065847076262937067510957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8710564717508624711673971 13065847076262937067510957)
                  ·
                    refine ⟨4899692653598601400316609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13065847076262937067510957 4899692653598601400316609)
                    ·
                      refine ⟨3674769490198951050237457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4899692653598601400316609 3674769490198951050237457)
                      ·
                        rfl

theorem cell23_7156588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_7156588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156588 prefixEnd_7156588 := by exact prefixLift 7156588
  have htrace : WordTrace (prefixWord ++ tailWord_7156588) baseStart_7156588 baseEnd_7156588 := by
    simpa [prefixWord, tailWord_7156588, baseEnd_7156588] using wordTrace_append hprefix tailTrace_7156588
  have hstable : (prefixWord ++ tailWord_7156588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156588).length < 2 ^ (prefixWord ++ tailWord_7156588).sum := by decide
  have hdescent : baseEnd_7156588 < baseStart_7156588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156594 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_7156594 : Nat := 118140960795 + 7156594 * 2 ^ 59
def prefixEnd_7156594 : Nat := 4983230072969 + 3 ^ 40 * 7156594 * 2
def baseEnd_7156594 : Nat := 1224924190360959342254143

theorem tailTrace_7156594 : CollatzResearch.WordTrace tailWord_7156594 prefixEnd_7156594 1224924190360959342254143 := by
  unfold tailWord_7156594
  simp only [CollatzResearch.WordTrace]
  refine ⟨65255606758722415448025209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174014951356593107861400557 65255606758722415448025209)
  ·
    refine ⟨48941705069041811586018907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65255606758722415448025209 48941705069041811586018907)
    ·
      refine ⟨73412557603562717379028361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48941705069041811586018907 73412557603562717379028361)
      ·
        refine ⟨55059418202672038034271271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73412557603562717379028361 55059418202672038034271271)
        ·
          refine ⟨82589127304008057051406907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55059418202672038034271271 82589127304008057051406907)
          ·
            refine ⟨123883690956012085577110361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82589127304008057051406907 123883690956012085577110361)
            ·
              refine ⟨92912768217009064182832771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123883690956012085577110361 92912768217009064182832771)
              ·
                refine ⟨139369152325513596274249157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92912768217009064182832771 139369152325513596274249157)
                ·
                  refine ⟨26131716061033799301421717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139369152325513596274249157 26131716061033799301421717)
                  ·
                    refine ⟨1224924190360959342254143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26131716061033799301421717 1224924190360959342254143)
                    ·
                      rfl

theorem cell23_7156594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_7156594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156594 prefixEnd_7156594 := by exact prefixLift 7156594
  have htrace : WordTrace (prefixWord ++ tailWord_7156594) baseStart_7156594 baseEnd_7156594 := by
    simpa [prefixWord, tailWord_7156594, baseEnd_7156594] using wordTrace_append hprefix tailTrace_7156594
  have hstable : (prefixWord ++ tailWord_7156594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156594).length < 2 ^ (prefixWord ++ tailWord_7156594).sum := by decide
  have hdescent : baseEnd_7156594 < baseStart_7156594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156662 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_7156662 : Nat := 118140960795 + 7156662 * 2 ^ 59
def prefixEnd_7156662 : Nat := 4983230072969 + 3 ^ 40 * 7156662 * 2
def baseEnd_7156662 : Nat := 1224935829255794586904039

theorem tailTrace_7156662 : CollatzResearch.WordTrace tailWord_7156662 prefixEnd_7156662 1224935829255794586904039 := by
  unfold tailWord_7156662
  simp only [CollatzResearch.WordTrace]
  refine ⟨16314056699915206837848515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174016604799095539603717493 16314056699915206837848515)
  ·
    refine ⟨24471085049872810256772773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16314056699915206837848515 24471085049872810256772773)
    ·
      refine ⟨4588328446851151923144895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24471085049872810256772773 4588328446851151923144895)
      ·
        refine ⟨6882492670276727884717343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588328446851151923144895 6882492670276727884717343)
        ·
          refine ⟨10323739005415091827076015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6882492670276727884717343 10323739005415091827076015)
          ·
            refine ⟨15485608508122637740614023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10323739005415091827076015 15485608508122637740614023)
            ·
              refine ⟨23228412762183956610921035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15485608508122637740614023 23228412762183956610921035)
              ·
                refine ⟨34842619143275934916381553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23228412762183956610921035 34842619143275934916381553)
                ·
                  refine ⟨26131964357456951187286165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34842619143275934916381553 26131964357456951187286165)
                  ·
                    refine ⟨1224935829255794586904039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26131964357456951187286165 1224935829255794586904039)
                    ·
                      rfl

theorem cell23_7156662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_7156662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156662 prefixEnd_7156662 := by exact prefixLift 7156662
  have htrace : WordTrace (prefixWord ++ tailWord_7156662) baseStart_7156662 baseEnd_7156662 := by
    simpa [prefixWord, tailWord_7156662, baseEnd_7156662] using wordTrace_append hprefix tailTrace_7156662
  have hstable : (prefixWord ++ tailWord_7156662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156662).length < 2 ^ (prefixWord ++ tailWord_7156662).sum := by decide
  have hdescent : baseEnd_7156662 < baseStart_7156662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156741 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 2, 5, 3]
def baseStart_7156741 : Nat := 118140960795 + 7156741 * 2 ^ 59
def prefixEnd_7156741 : Nat := 4983230072969 + 3 ^ 40 * 7156741 * 2
def baseEnd_7156741 : Nat := 3674848052739088951624253

theorem tailTrace_7156741 : CollatzResearch.WordTrace tailWord_7156741 prefixEnd_7156741 3674848052739088951624253 := by
  unfold tailWord_7156741
  simp only [CollatzResearch.WordTrace]
  refine ⟨261027788565357105897702077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174018525710238070598468051 261027788565357105897702077)
  ·
    refine ⟨97885420712008914711638279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261027788565357105897702077 97885420712008914711638279)
    ·
      refine ⟨146828131068013372067457419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97885420712008914711638279 146828131068013372067457419)
      ·
        refine ⟨220242196602020058101186129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146828131068013372067457419 220242196602020058101186129)
        ·
          refine ⟨165181647451515043575889597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220242196602020058101186129 165181647451515043575889597)
          ·
            refine ⟨61943117794318141340958599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165181647451515043575889597 61943117794318141340958599)
            ·
              refine ⟨92914676691477212011437899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61943117794318141340958599 92914676691477212011437899)
              ·
                refine ⟨139372015037215818017156849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92914676691477212011437899 139372015037215818017156849)
                ·
                  refine ⟨104529011277911863512867637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139372015037215818017156849 104529011277911863512867637)
                  ·
                    refine ⟨9799594807304237204331341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104529011277911863512867637 9799594807304237204331341)
                    ·
                      refine ⟨3674848052739088951624253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9799594807304237204331341 3674848052739088951624253)
                      ·
                        rfl

theorem cell23_7156741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_7156741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156741 prefixEnd_7156741 := by exact prefixLift 7156741
  have htrace : WordTrace (prefixWord ++ tailWord_7156741) baseStart_7156741 baseEnd_7156741 := by
    simpa [prefixWord, tailWord_7156741, baseEnd_7156741] using wordTrace_append hprefix tailTrace_7156741
  have hstable : (prefixWord ++ tailWord_7156741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156741).length < 2 ^ (prefixWord ++ tailWord_7156741).sum := by decide
  have hdescent : baseEnd_7156741 < baseStart_7156741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156791 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 1, 6]
def baseStart_7156791 : Nat := 118140960795 + 7156791 * 2 ^ 59
def prefixEnd_7156791 : Nat := 4983230072969 + 3 ^ 40 * 7156791 * 2
def baseEnd_7156791 : Nat := 1224957908923937918666341

theorem tailTrace_7156791 : CollatzResearch.WordTrace tailWord_7156791 prefixEnd_7156791 1224957908923937918666341 := by
  unfold tailWord_7156791
  simp only [CollatzResearch.WordTrace]
  refine ⟨261029612215175964437022227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174019741476783976291348151 261029612215175964437022227)
  ·
    refine ⟨391544418322763946655533341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261029612215175964437022227 391544418322763946655533341)
    ·
      refine ⟨146829156871036479995825003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391544418322763946655533341 146829156871036479995825003)
      ·
        refine ⟨220243735306554719993737505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146829156871036479995825003 220243735306554719993737505)
        ·
          refine ⟨165182801479916039995303129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220243735306554719993737505 165182801479916039995303129)
          ·
            refine ⟨123887101109937029996477347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165182801479916039995303129 123887101109937029996477347)
            ·
              refine ⟨185830651664905544994716021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123887101109937029996477347 185830651664905544994716021)
              ·
                refine ⟨17421623593584894843254627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185830651664905544994716021 17421623593584894843254627)
                ·
                  refine ⟨26132435390377342264881941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17421623593584894843254627 26132435390377342264881941)
                  ·
                    refine ⟨1224957908923937918666341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26132435390377342264881941 1224957908923937918666341)
                    ·
                      rfl

theorem cell23_7156791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_7156791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156791 prefixEnd_7156791 := by exact prefixLift 7156791
  have htrace : WordTrace (prefixWord ++ tailWord_7156791) baseStart_7156791 baseEnd_7156791 := by
    simpa [prefixWord, tailWord_7156791, baseEnd_7156791] using wordTrace_append hprefix tailTrace_7156791
  have hstable : (prefixWord ++ tailWord_7156791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156791).length < 2 ^ (prefixWord ++ tailWord_7156791).sum := by decide
  have hdescent : baseEnd_7156791 < baseStart_7156791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156828 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_7156828 : Nat := 118140960795 + 7156828 * 2 ^ 59
def prefixEnd_7156828 : Nat := 4983230072969 + 3 ^ 40 * 7156828 * 2
def baseEnd_7156828 : Nat := 3674892725556030111236353

theorem tailTrace_7156828 : CollatzResearch.WordTrace tailWord_7156828 prefixEnd_7156828 3674892725556030111236353 := by
  unfold tailWord_7156828
  simp only [CollatzResearch.WordTrace]
  refine ⟨130515480858020959878059569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174020641144027946504079425 130515480858020959878059569)
  ·
    refine ⟨97886610643515719908544677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130515480858020959878059569 97886610643515719908544677)
    ·
      refine ⟨18353739495659197482852127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97886610643515719908544677 18353739495659197482852127)
      ·
        refine ⟨27530609243488796224278191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18353739495659197482852127 27530609243488796224278191)
        ·
          refine ⟨41295913865233194336417287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27530609243488796224278191 41295913865233194336417287)
          ·
            refine ⟨61943870797849791504625931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41295913865233194336417287 61943870797849791504625931)
            ·
              refine ⟨92915806196774687256938897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61943870797849791504625931 92915806196774687256938897)
              ·
                refine ⟨69686854647581015442704173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92915806196774687256938897 69686854647581015442704173)
                ·
                  refine ⟨26132570492842880791014065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69686854647581015442704173 26132570492842880791014065)
                  ·
                    refine ⟨19599427869632160593260549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26132570492842880791014065 19599427869632160593260549)
                    ·
                      refine ⟨3674892725556030111236353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19599427869632160593260549 3674892725556030111236353)
                      ·
                        rfl

theorem cell23_7156828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_7156828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156828 prefixEnd_7156828 := by exact prefixLift 7156828
  have htrace : WordTrace (prefixWord ++ tailWord_7156828) baseStart_7156828 baseEnd_7156828 := by
    simpa [prefixWord, tailWord_7156828, baseEnd_7156828] using wordTrace_append hprefix tailTrace_7156828
  have hstable : (prefixWord ++ tailWord_7156828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156828).length < 2 ^ (prefixWord ++ tailWord_7156828).sum := by decide
  have hdescent : baseEnd_7156828 < baseStart_7156828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156845 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_7156845 : Nat := 118140960795 + 7156845 * 2 ^ 59
def prefixEnd_7156845 : Nat := 4983230072969 + 3 ^ 40 * 7156845 * 2
def baseEnd_7156845 : Nat := 3674901454727156544723775

theorem tailTrace_7156845 : CollatzResearch.WordTrace tailWord_7156845 prefixEnd_7156845 3674901454727156544723775 := by
  unfold tailWord_7156845
  simp only [CollatzResearch.WordTrace]
  refine ⟨261031581756980331659487989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174021054504653554439658659 261031581756980331659487989)
  ·
    refine ⟨24471710789716906093076999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261031581756980331659487989 24471710789716906093076999)
    ·
      refine ⟨36707566184575359139615499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24471710789716906093076999 36707566184575359139615499)
      ·
        refine ⟨55061349276863038709423249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36707566184575359139615499 55061349276863038709423249)
        ·
          refine ⟨41296011957647279032067437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55061349276863038709423249 41296011957647279032067437)
          ·
            refine ⟨15486004484117729637025289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41296011957647279032067437 15486004484117729637025289)
            ·
              refine ⟨11614503363088297227768967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15486004484117729637025289 11614503363088297227768967)
              ·
                refine ⟨17421755044632445841653451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11614503363088297227768967 17421755044632445841653451)
                ·
                  refine ⟨26132632566948668762480177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17421755044632445841653451 26132632566948668762480177)
                  ·
                    refine ⟨19599474425211501571860133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26132632566948668762480177 19599474425211501571860133)
                    ·
                      refine ⟨3674901454727156544723775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19599474425211501571860133 3674901454727156544723775)
                      ·
                        rfl

theorem cell23_7156845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_7156845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156845 prefixEnd_7156845 := by exact prefixLift 7156845
  have htrace : WordTrace (prefixWord ++ tailWord_7156845) baseStart_7156845 baseEnd_7156845 := by
    simpa [prefixWord, tailWord_7156845, baseEnd_7156845] using wordTrace_append hprefix tailTrace_7156845
  have hstable : (prefixWord ++ tailWord_7156845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156845).length < 2 ^ (prefixWord ++ tailWord_7156845).sum := by decide
  have hdescent : baseEnd_7156845 < baseStart_7156845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156865 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_7156865 : Nat := 118140960795 + 7156865 * 2 ^ 59
def prefixEnd_7156865 : Nat := 4983230072969 + 3 ^ 40 * 7156865 * 2
def baseEnd_7156865 : Nat := 3674911724340246466473683

theorem tailTrace_7156865 : CollatzResearch.WordTrace tailWord_7156865 prefixEnd_7156865 3674911724340246466473683 := by
  unfold tailWord_7156865
  simp only [CollatzResearch.WordTrace]
  refine ⟨261032311216907875075216049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174021540811271916716810699 261032311216907875075216049)
  ·
    refine ⟨195774233412680906306412037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261032311216907875075216049 195774233412680906306412037)
    ·
      refine ⟨36707668764877669932452257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195774233412680906306412037 36707668764877669932452257)
      ·
        refine ⟨27530751573658252449339193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36707668764877669932452257 27530751573658252449339193)
        ·
          refine ⟨20648063680243689337004395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27530751573658252449339193 20648063680243689337004395)
          ·
            refine ⟨30972095520365534005506593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20648063680243689337004395 30972095520365534005506593)
            ·
              refine ⟨23229071640274150504129945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30972095520365534005506593 23229071640274150504129945)
              ·
                refine ⟨17421803730205612878097459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23229071640274150504129945 17421803730205612878097459)
                ·
                  refine ⟨26132705595308419317146189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17421803730205612878097459 26132705595308419317146189)
                  ·
                    refine ⟨9799764598240657243929821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26132705595308419317146189 9799764598240657243929821)
                    ·
                      refine ⟨3674911724340246466473683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9799764598240657243929821 3674911724340246466473683)
                      ·
                        rfl

theorem cell23_7156865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_7156865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156865 prefixEnd_7156865 := by exact prefixLift 7156865
  have htrace : WordTrace (prefixWord ++ tailWord_7156865) baseStart_7156865 baseEnd_7156865 := by
    simpa [prefixWord, tailWord_7156865, baseEnd_7156865] using wordTrace_append hprefix tailTrace_7156865
  have hstable : (prefixWord ++ tailWord_7156865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156865).length < 2 ^ (prefixWord ++ tailWord_7156865).sum := by decide
  have hdescent : baseEnd_7156865 < baseStart_7156865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156869 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 1, 2, 3]
def baseStart_7156869 : Nat := 118140960795 + 7156869 * 2 ^ 59
def prefixEnd_7156869 : Nat := 4983230072969 + 3 ^ 40 * 7156869 * 2
def baseEnd_7156869 : Nat := 3674913778262864450823665

theorem tailTrace_7156869 : CollatzResearch.WordTrace tailWord_7156869 prefixEnd_7156869 3674913778262864450823665 := by
  unfold tailWord_7156869
  simp only [CollatzResearch.WordTrace]
  refine ⟨261032457108893383758361661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174021638072595589172241107 261032457108893383758361661)
  ·
    refine ⟨97887171415835018909385623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261032457108893383758361661 97887171415835018909385623)
    ·
      refine ⟨146830757123752528364078435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97887171415835018909385623 146830757123752528364078435)
      ·
        refine ⟨220246135685628792546117653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146830757123752528364078435 220246135685628792546117653)
        ·
          refine ⟨10324037610263849650599265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 220246135685628792546117653 10324037610263849650599265)
          ·
            refine ⟨7743028207697887237949449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10324037610263849650599265 7743028207697887237949449)
            ·
              refine ⟨5807271155773415428462087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7743028207697887237949449 5807271155773415428462087)
              ·
                refine ⟨8710906733660123142693131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807271155773415428462087 8710906733660123142693131)
                ·
                  refine ⟨13066360100490184714039697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8710906733660123142693131 13066360100490184714039697)
                  ·
                    refine ⟨9799770075367638535529773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13066360100490184714039697 9799770075367638535529773)
                    ·
                      refine ⟨3674913778262864450823665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9799770075367638535529773 3674913778262864450823665)
                      ·
                        rfl

theorem cell23_7156869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_7156869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156869 prefixEnd_7156869 := by exact prefixLift 7156869
  have htrace : WordTrace (prefixWord ++ tailWord_7156869) baseStart_7156869 baseEnd_7156869 := by
    simpa [prefixWord, tailWord_7156869, baseEnd_7156869] using wordTrace_append hprefix tailTrace_7156869
  have hstable : (prefixWord ++ tailWord_7156869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156869).length < 2 ^ (prefixWord ++ tailWord_7156869).sum := by decide
  have hdescent : baseEnd_7156869 < baseStart_7156869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156882 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_7156882 : Nat := 118140960795 + 7156882 * 2 ^ 59
def prefixEnd_7156882 : Nat := 4983230072969 + 3 ^ 40 * 7156882 * 2
def baseEnd_7156882 : Nat := 3674920453511372899961105

theorem tailTrace_7156882 : CollatzResearch.WordTrace tailWord_7156882 prefixEnd_7156882 3674920453511372899961105 := by
  unfold tailWord_7156882
  simp only [CollatzResearch.WordTrace]
  refine ⟨65258232814461571744646225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174021954171897524652389933 65258232814461571744646225)
  ·
    refine ⟨48943674610846178808484669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65258232814461571744646225 48943674610846178808484669)
    ·
      refine ⟨18353877979067317053181751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48943674610846178808484669 18353877979067317053181751)
      ·
        refine ⟨27530816968600975579772627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18353877979067317053181751 27530816968600975579772627)
        ·
          refine ⟨41296225452901463369658941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27530816968600975579772627 41296225452901463369658941)
          ·
            refine ⟨15486084544838048763622103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41296225452901463369658941 15486084544838048763622103)
            ·
              refine ⟨23229126817257073145433155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15486084544838048763622103 23229126817257073145433155)
              ·
                refine ⟨34843690225885609718149733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23229126817257073145433155 34843690225885609718149733)
                ·
                  refine ⟨6533191917353551822153075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34843690225885609718149733 6533191917353551822153075)
                  ·
                    refine ⟨9799787876030327733229613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6533191917353551822153075 9799787876030327733229613)
                    ·
                      refine ⟨3674920453511372899961105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9799787876030327733229613 3674920453511372899961105)
                      ·
                        rfl

theorem cell23_7156882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_7156882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156882 prefixEnd_7156882 := by exact prefixLift 7156882
  have htrace : WordTrace (prefixWord ++ tailWord_7156882) baseStart_7156882 baseEnd_7156882 := by
    simpa [prefixWord, tailWord_7156882, baseEnd_7156882] using wordTrace_append hprefix tailTrace_7156882
  have hstable : (prefixWord ++ tailWord_7156882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156882).length < 2 ^ (prefixWord ++ tailWord_7156882).sum := by decide
  have hdescent : baseEnd_7156882 < baseStart_7156882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156950 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_7156950 : Nat := 118140960795 + 7156950 * 2 ^ 59
def prefixEnd_7156950 : Nat := 4983230072969 + 3 ^ 40 * 7156950 * 2
def baseEnd_7156950 : Nat := 3674955370195878633910793

theorem tailTrace_7156950 : CollatzResearch.WordTrace tailWord_7156950 prefixEnd_7156950 3674955370195878633910793 := by
  unfold tailWord_7156950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16314713213849995912003769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174023607614399956394706869 16314713213849995912003769)
  ·
    refine ⟨12236034910387496934002827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16314713213849995912003769 12236034910387496934002827)
    ·
      refine ⟨18354052365581245401004241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12236034910387496934002827 18354052365581245401004241)
      ·
        refine ⟨13765539274185934050753181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18354052365581245401004241 13765539274185934050753181)
        ·
          refine ⟨5162077227819725269032443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13765539274185934050753181 5162077227819725269032443)
          ·
            refine ⟨7743115841729587903548665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162077227819725269032443 7743115841729587903548665)
            ·
              refine ⟨5807336881297190927661499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7743115841729587903548665 5807336881297190927661499)
              ·
                refine ⟨8711005321945786391492249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807336881297190927661499 8711005321945786391492249)
                ·
                  refine ⟨6533253991459339793619187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8711005321945786391492249 6533253991459339793619187)
                  ·
                    refine ⟨9799880987189009690428781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6533253991459339793619187 9799880987189009690428781)
                    ·
                      refine ⟨3674955370195878633910793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9799880987189009690428781 3674955370195878633910793)
                      ·
                        rfl

theorem cell23_7156950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_7156950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156950 prefixEnd_7156950 := by exact prefixLift 7156950
  have htrace : WordTrace (prefixWord ++ tailWord_7156950) baseStart_7156950 baseEnd_7156950 := by
    simpa [prefixWord, tailWord_7156950, baseEnd_7156950] using wordTrace_append hprefix tailTrace_7156950
  have hstable : (prefixWord ++ tailWord_7156950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156950).length < 2 ^ (prefixWord ++ tailWord_7156950).sum := by decide
  have hdescent : baseEnd_7156950 < baseStart_7156950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156968 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7156968 : Nat := 118140960795 + 7156968 * 2 ^ 59
def prefixEnd_7156968 : Nat := 4983230072969 + 3 ^ 40 * 7156968 * 2
def baseEnd_7156968 : Nat := 3674964612847659563485709

theorem tailTrace_7156968 : CollatzResearch.WordTrace tailWord_7156968 prefixEnd_7156968 3674964612847659563485709 := by
  unfold tailWord_7156968
  simp only [CollatzResearch.WordTrace]
  refine ⟨130518033967767361833107779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174024045290356482444143705 130518033967767361833107779)
  ·
    refine ⟨195777050951651042749661669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130518033967767361833107779 195777050951651042749661669)
    ·
      refine ⟨36708197053434570515561563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195777050951651042749661669 36708197053434570515561563)
      ·
        refine ⟨55062295580151855773342345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36708197053434570515561563 55062295580151855773342345)
        ·
          refine ⟨41296721685113891830006759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55062295580151855773342345 41296721685113891830006759)
          ·
            refine ⟨61945082527670837745010139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41296721685113891830006759 61945082527670837745010139)
            ·
              refine ⟨92917623791506256617515209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61945082527670837745010139 92917623791506256617515209)
              ·
                refine ⟨69688217843629692463136407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92917623791506256617515209 69688217843629692463136407)
                ·
                  refine ⟨104532326765444538694704611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69688217843629692463136407 104532326765444538694704611)
                  ·
                    refine ⟨156798490148166808042056917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104532326765444538694704611 156798490148166808042056917)
                    ·
                      refine ⟨3674964612847659563485709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156798490148166808042056917 3674964612847659563485709)
                      ·
                        rfl

theorem cell23_7156968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7156968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156968 prefixEnd_7156968 := by exact prefixLift 7156968
  have htrace : WordTrace (prefixWord ++ tailWord_7156968) baseStart_7156968 baseEnd_7156968 := by
    simpa [prefixWord, tailWord_7156968, baseEnd_7156968] using wordTrace_append hprefix tailTrace_7156968
  have hstable : (prefixWord ++ tailWord_7156968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156968).length < 2 ^ (prefixWord ++ tailWord_7156968).sum := by decide
  have hdescent : baseEnd_7156968 < baseStart_7156968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156995 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 4]
def baseStart_7156995 : Nat := 118140960795 + 7156995 * 2 ^ 59
def prefixEnd_7156995 : Nat := 4983230072969 + 3 ^ 40 * 7156995 * 2
def baseEnd_7156995 : Nat := 3674978476825330957848085

theorem tailTrace_7156995 : CollatzResearch.WordTrace tailWord_7156995 prefixEnd_7156995 3674978476825330957848085 := by
  unfold tailWord_7156995
  simp only [CollatzResearch.WordTrace]
  refine ⟨261037052706436907277448439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174024701804291271518298959 261037052706436907277448439)
  ·
    refine ⟨391555579059655360916172659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261037052706436907277448439 391555579059655360916172659)
    ·
      refine ⟨587333368589483041374258989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391555579059655360916172659 587333368589483041374258989)
      ·
        refine ⟨220250013221056140515347121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587333368589483041374258989 220250013221056140515347121)
        ·
          refine ⟨165187509915792105386510341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220250013221056140515347121 165187509915792105386510341)
          ·
            refine ⟨30972658109211019759970689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165187509915792105386510341 30972658109211019759970689)
            ·
              refine ⟨23229493581908264819978017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30972658109211019759970689 23229493581908264819978017)
              ·
                refine ⟨17422120186431198614983513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23229493581908264819978017 17422120186431198614983513)
                ·
                  refine ⟨13066590139823398961237635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17422120186431198614983513 13066590139823398961237635)
                  ·
                    refine ⟨19599885209735098441856453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13066590139823398961237635 19599885209735098441856453)
                    ·
                      refine ⟨3674978476825330957848085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19599885209735098441856453 3674978476825330957848085)
                      ·
                        rfl

theorem cell23_7156995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_7156995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156995 prefixEnd_7156995 := by exact prefixLift 7156995
  have htrace : WordTrace (prefixWord ++ tailWord_7156995) baseStart_7156995 baseEnd_7156995 := by
    simpa [prefixWord, tailWord_7156995, baseEnd_7156995] using wordTrace_append hprefix tailTrace_7156995
  have hstable : (prefixWord ++ tailWord_7156995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156995).length < 2 ^ (prefixWord ++ tailWord_7156995).sum := by decide
  have hdescent : baseEnd_7156995 < baseStart_7156995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157015 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 3]
def baseStart_7157015 : Nat := 118140960795 + 7157015 * 2 ^ 59
def prefixEnd_7157015 : Nat := 4983230072969 + 3 ^ 40 * 7157015 * 2
def baseEnd_7157015 : Nat := 3674988746438420879597993

theorem tailTrace_7157015 : CollatzResearch.WordTrace tailWord_7157015 prefixEnd_7157015 3674988746438420879597993 := by
  unfold tailWord_7157015
  simp only [CollatzResearch.WordTrace]
  refine ⟨261037782166364450693176499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174025188110909633795450999 261037782166364450693176499)
  ·
    refine ⟨391556673249546676039764749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261037782166364450693176499 391556673249546676039764749)
    ·
      refine ⟨146833752468580003514911781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391556673249546676039764749 146833752468580003514911781)
      ·
        refine ⟨27531328587858750659045959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146833752468580003514911781 27531328587858750659045959)
        ·
          refine ⟨41296992881788125988568939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27531328587858750659045959 41296992881788125988568939)
          ·
            refine ⟨61945489322682188982853409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41296992881788125988568939 61945489322682188982853409)
            ·
              refine ⟨46459116992011641737140057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61945489322682188982853409 46459116992011641737140057)
              ·
                refine ⟨34844337744008731302855043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46459116992011641737140057 34844337744008731302855043)
                ·
                  refine ⟨52266506616013096954282565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34844337744008731302855043 52266506616013096954282565)
                  ·
                    refine ⟨9799969990502455678927981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52266506616013096954282565 9799969990502455678927981)
                    ·
                      refine ⟨3674988746438420879597993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9799969990502455678927981 3674988746438420879597993)
                      ·
                        rfl

theorem cell23_7157015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_7157015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157015 prefixEnd_7157015 := by exact prefixLift 7157015
  have htrace : WordTrace (prefixWord ++ tailWord_7157015) baseStart_7157015 baseEnd_7157015 := by
    simpa [prefixWord, tailWord_7157015, baseEnd_7157015] using wordTrace_append hprefix tailTrace_7157015
  have hstable : (prefixWord ++ tailWord_7157015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157015).length < 2 ^ (prefixWord ++ tailWord_7157015).sum := by decide
  have hdescent : baseEnd_7157015 < baseStart_7157015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157032 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_7157032 : Nat := 118140960795 + 7157032 * 2 ^ 59
def prefixEnd_7157032 : Nat := 4983230072969 + 3 ^ 40 * 7157032 * 2
def baseEnd_7157032 : Nat := 3674997475609547313085415

theorem tailTrace_7157032 : CollatzResearch.WordTrace tailWord_7157032 prefixEnd_7157032 3674997475609547313085415 := by
  unfold tailWord_7157032
  simp only [CollatzResearch.WordTrace]
  refine ⟨130519201103651431298272675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174025601471535241731030233 130519201103651431298272675)
  ·
    refine ⟨195778801655477146947409013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130519201103651431298272675 195778801655477146947409013)
    ·
      refine ⟨18354262655200982526319595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195778801655477146947409013 18354262655200982526319595)
      ·
        refine ⟨27531393982801473789479393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18354262655200982526319595 27531393982801473789479393)
        ·
          refine ⟨20648545487101105342109545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27531393982801473789479393 20648545487101105342109545)
          ·
            refine ⟨15486409115325829006582159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20648545487101105342109545 15486409115325829006582159)
            ·
              refine ⟨23229613672988743509873239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15486409115325829006582159 23229613672988743509873239)
              ·
                refine ⟨34844420509483115264809859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23229613672988743509873239 34844420509483115264809859)
                ·
                  refine ⟨52266630764224672897214789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34844420509483115264809859 52266630764224672897214789)
                  ·
                    refine ⟨9799993268292126168227773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52266630764224672897214789 9799993268292126168227773)
                    ·
                      refine ⟨3674997475609547313085415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9799993268292126168227773 3674997475609547313085415)
                      ·
                        rfl

theorem cell23_7157032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_7157032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157032 prefixEnd_7157032 := by exact prefixLift 7157032
  have htrace : WordTrace (prefixWord ++ tailWord_7157032) baseStart_7157032 baseEnd_7157032 := by
    simpa [prefixWord, tailWord_7157032, baseEnd_7157032] using wordTrace_append hprefix tailTrace_7157032
  have hstable : (prefixWord ++ tailWord_7157032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157032).length < 2 ^ (prefixWord ++ tailWord_7157032).sum := by decide
  have hdescent : baseEnd_7157032 < baseStart_7157032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157052 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 6]
def baseStart_7157052 : Nat := 118140960795 + 7157052 * 2 ^ 59
def prefixEnd_7157052 : Nat := 4983230072969 + 3 ^ 40 * 7157052 * 2
def baseEnd_7157052 : Nat := 408334193913626359426147

theorem tailTrace_7157052 : CollatzResearch.WordTrace tailWord_7157052 prefixEnd_7157052 408334193913626359426147 := by
  unfold tailWord_7157052
  simp only [CollatzResearch.WordTrace]
  refine ⟨130519565833615203006136705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174026087778153604008182273 130519565833615203006136705)
  ·
    refine ⟨97889674375211402254602529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130519565833615203006136705 97889674375211402254602529)
    ·
      refine ⟨73417255781408551690951897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97889674375211402254602529 73417255781408551690951897)
      ·
        refine ⟨55062941836056413768213923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73417255781408551690951897 55062941836056413768213923)
        ·
          refine ⟨82594412754084620652320885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55062941836056413768213923 82594412754084620652320885)
          ·
            refine ⟨7743226195695433186155083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82594412754084620652320885 7743226195695433186155083)
            ·
              refine ⟨11614839293543149779232625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743226195695433186155083 11614839293543149779232625)
              ·
                refine ⟨8711129470157362334424469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11614839293543149779232625 8711129470157362334424469)
                ·
                  refine ⟨408334193913626359426147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8711129470157362334424469 408334193913626359426147)
                  ·
                    rfl

theorem cell23_7157052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_7157052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157052 prefixEnd_7157052 := by exact prefixLift 7157052
  have htrace : WordTrace (prefixWord ++ tailWord_7157052) baseStart_7157052 baseEnd_7157052 := by
    simpa [prefixWord, tailWord_7157052, baseEnd_7157052] using wordTrace_append hprefix tailTrace_7157052
  have hstable : (prefixWord ++ tailWord_7157052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157052).length < 2 ^ (prefixWord ++ tailWord_7157052).sum := by decide
  have hdescent : baseEnd_7157052 < baseStart_7157052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157105 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_7157105 : Nat := 118140960795 + 7157105 * 2 ^ 59
def prefixEnd_7157105 : Nat := 4983230072969 + 3 ^ 40 * 7157105 * 2
def baseEnd_7157105 : Nat := 3675034959697325527472579

theorem tailTrace_7157105 : CollatzResearch.WordTrace tailWord_7157105 prefixEnd_7157105 3675034959697325527472579 := by
  unfold tailWord_7157105
  simp only [CollatzResearch.WordTrace]
  refine ⟨261041064736038396063952769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174027376490692264042635179 261041064736038396063952769)
  ·
    refine ⟨195780798552028797047964577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261041064736038396063952769 195780798552028797047964577)
    ·
      refine ⟨146835598914021597785973433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195780798552028797047964577 146835598914021597785973433)
      ·
        refine ⟨110126699185516198339480075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146835598914021597785973433 110126699185516198339480075)
        ·
          refine ⟨165190048778274297509220113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110126699185516198339480075 165190048778274297509220113)
          ·
            refine ⟨123892536583705723131915085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165190048778274297509220113 123892536583705723131915085)
            ·
              refine ⟨46459701218889646174468157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123892536583705723131915085 46459701218889646174468157)
              ·
                refine ⟨17422387957083617315425559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46459701218889646174468157 17422387957083617315425559)
                ·
                  refine ⟨26133581935625425973138339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17422387957083617315425559 26133581935625425973138339)
                  ·
                    refine ⟨39200372903438138959707509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26133581935625425973138339 39200372903438138959707509)
                    ·
                      refine ⟨3675034959697325527472579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39200372903438138959707509 3675034959697325527472579)
                      ·
                        rfl

theorem cell23_7157105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_7157105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157105 prefixEnd_7157105 := by exact prefixLift 7157105
  have htrace : WordTrace (prefixWord ++ tailWord_7157105) baseStart_7157105 baseEnd_7157105 := by
    simpa [prefixWord, tailWord_7157105, baseEnd_7157105] using wordTrace_append hprefix tailTrace_7157105
  have hstable : (prefixWord ++ tailWord_7157105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157105).length < 2 ^ (prefixWord ++ tailWord_7157105).sum := by decide
  have hdescent : baseEnd_7157105 < baseStart_7157105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157129 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 2, 4]
def baseStart_7157129 : Nat := 118140960795 + 7157129 * 2 ^ 59
def prefixEnd_7157129 : Nat := 4983230072969 + 3 ^ 40 * 7157129 * 2
def baseEnd_7157129 : Nat := 1225015761077677811190823

theorem tailTrace_7157129 : CollatzResearch.WordTrace tailWord_7157129 prefixEnd_7157129 1225015761077677811190823 := by
  unfold tailWord_7157129
  simp only [CollatzResearch.WordTrace]
  refine ⟨261041940087951448162826441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174027960058634298775217627 261041940087951448162826441)
  ·
    refine ⟨195781455065963586122119831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261041940087951448162826441 195781455065963586122119831)
    ·
      refine ⟨293672182598945379183179747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195781455065963586122119831 293672182598945379183179747)
      ·
        refine ⟨440508273898418068774769621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293672182598945379183179747 440508273898418068774769621)
        ·
          refine ⟨10324412669494173486908663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 440508273898418068774769621 10324412669494173486908663)
          ·
            refine ⟨15486619004241260230362995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10324412669494173486908663 15486619004241260230362995)
            ·
              refine ⟨23229928506361890345544493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15486619004241260230362995 23229928506361890345544493)
              ·
                refine ⟨8711223189885708879579185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23229928506361890345544493 8711223189885708879579185)
                ·
                  refine ⟨6533417392414281659684389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8711223189885708879579185 6533417392414281659684389)
                  ·
                    refine ⟨1225015761077677811190823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6533417392414281659684389 1225015761077677811190823)
                    ·
                      rfl

theorem cell23_7157129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 4].length) (baseStart_7157129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157129 prefixEnd_7157129 := by exact prefixLift 7157129
  have htrace : WordTrace (prefixWord ++ tailWord_7157129) baseStart_7157129 baseEnd_7157129 := by
    simpa [prefixWord, tailWord_7157129, baseEnd_7157129] using wordTrace_append hprefix tailTrace_7157129
  have hstable : (prefixWord ++ tailWord_7157129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157129).length < 2 ^ (prefixWord ++ tailWord_7157129).sum := by decide
  have hdescent : baseEnd_7157129 < baseStart_7157129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157152 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 3]
def baseStart_7157152 : Nat := 118140960795 + 7157152 * 2 ^ 59
def prefixEnd_7157152 : Nat := 4983230072969 + 3 ^ 40 * 7157152 * 2
def baseEnd_7157152 : Nat := 3675059093288086843584863

theorem tailTrace_7157152 : CollatzResearch.WordTrace tailWord_7157152 prefixEnd_7157152 3675059093288086843584863 := by
  unfold tailWord_7157152
  simp only [CollatzResearch.WordTrace]
  refine ⟨130521389483434061545456855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174028519311245415393942473 130521389483434061545456855)
  ·
    refine ⟨195782084225151092318185283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130521389483434061545456855 195782084225151092318185283)
    ·
      refine ⟨293673126337726638477277925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195782084225151092318185283 293673126337726638477277925)
      ·
        refine ⟨55063711188323744714489611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293673126337726638477277925 55063711188323744714489611)
        ·
          refine ⟨82595566782485617071734417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55063711188323744714489611 82595566782485617071734417)
          ·
            refine ⟨61946675086864212803800813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82595566782485617071734417 61946675086864212803800813)
            ·
              refine ⟨23230003157574079801425305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61946675086864212803800813 23230003157574079801425305)
              ·
                refine ⟨17422502368180559851068979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23230003157574079801425305 17422502368180559851068979)
                ·
                  refine ⟨26133753552270839776603469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17422502368180559851068979 26133753552270839776603469)
                  ·
                    refine ⟨9800157582101564916226301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26133753552270839776603469 9800157582101564916226301)
                    ·
                      refine ⟨3675059093288086843584863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9800157582101564916226301 3675059093288086843584863)
                      ·
                        rfl

theorem cell23_7157152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_7157152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157152 prefixEnd_7157152 := by exact prefixLift 7157152
  have htrace : WordTrace (prefixWord ++ tailWord_7157152) baseStart_7157152 baseEnd_7157152 := by
    simpa [prefixWord, tailWord_7157152, baseEnd_7157152] using wordTrace_append hprefix tailTrace_7157152
  have hstable : (prefixWord ++ tailWord_7157152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157152).length < 2 ^ (prefixWord ++ tailWord_7157152).sum := by decide
  have hdescent : baseEnd_7157152 < baseStart_7157152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157175 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_7157175 : Nat := 118140960795 + 7157175 * 2 ^ 59
def prefixEnd_7157175 : Nat := 4983230072969 + 3 ^ 40 * 7157175 * 2
def baseEnd_7157175 : Nat := 3675070903343140253597257

theorem tailTrace_7157175 : CollatzResearch.WordTrace tailWord_7157175 prefixEnd_7157175 3675070903343140253597257 := by
  unfold tailWord_7157175
  simp only [CollatzResearch.WordTrace]
  refine ⟨261043617845784798019000979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174029078563856532012667319 261043617845784798019000979)
  ·
    refine ⟨391565426768677197028501469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261043617845784798019000979 391565426768677197028501469)
    ·
      refine ⟨146837035038253948885688051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391565426768677197028501469 146837035038253948885688051)
      ·
        refine ⟨220255552557380923328532077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146837035038253948885688051 220255552557380923328532077)
        ·
          refine ⟨82595832209017846248199529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220255552557380923328532077 82595832209017846248199529)
          ·
            refine ⟨61946874156763384686149647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82595832209017846248199529 61946874156763384686149647)
            ·
              refine ⟨92920311235145077029224471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61946874156763384686149647 92920311235145077029224471)
              ·
                refine ⟨139380466852717615543836707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92920311235145077029224471 139380466852717615543836707)
                ·
                  refine ⟨209070700279076423315755061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139380466852717615543836707 209070700279076423315755061)
                  ·
                    refine ⟨19600378151163414685852037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209070700279076423315755061 19600378151163414685852037)
                    ·
                      refine ⟨3675070903343140253597257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19600378151163414685852037 3675070903343140253597257)
                      ·
                        rfl

theorem cell23_7157175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_7157175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157175 prefixEnd_7157175 := by exact prefixLift 7157175
  have htrace : WordTrace (prefixWord ++ tailWord_7157175) baseStart_7157175 baseEnd_7157175 := by
    simpa [prefixWord, tailWord_7157175, baseEnd_7157175] using wordTrace_append hprefix tailTrace_7157175
  have hstable : (prefixWord ++ tailWord_7157175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157175).length < 2 ^ (prefixWord ++ tailWord_7157175).sum := by decide
  have hdescent : baseEnd_7157175 < baseStart_7157175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157195 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 5]
def baseStart_7157195 : Nat := 118140960795 + 7157195 * 2 ^ 59
def prefixEnd_7157195 : Nat := 4983230072969 + 3 ^ 40 * 7157195 * 2
def baseEnd_7157195 : Nat := 3675081172956230175347165

theorem tailTrace_7157195 : CollatzResearch.WordTrace tailWord_7157195 prefixEnd_7157195 3675081172956230175347165 := by
  unfold tailWord_7157195
  simp only [CollatzResearch.WordTrace]
  refine ⟨261044347305712341434729039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174029564870474894289819359 261044347305712341434729039)
  ·
    refine ⟨391566520958568512152093559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261044347305712341434729039 391566520958568512152093559)
    ·
      refine ⟨587349781437852768228140339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391566520958568512152093559 587349781437852768228140339)
      ·
        refine ⟨881024672156779152342210509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587349781437852768228140339 881024672156779152342210509)
        ·
          refine ⟨330384252058792182128328941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 881024672156779152342210509 330384252058792182128328941)
          ·
            refine ⟨123894094522047068298123353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330384252058792182128328941 123894094522047068298123353)
            ·
              refine ⟨92920570891535301223592515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123894094522047068298123353 92920570891535301223592515)
              ·
                refine ⟨139380856337302951835388773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92920570891535301223592515 139380856337302951835388773)
                ·
                  refine ⟨26133910563244303469135395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139380856337302951835388773 26133910563244303469135395)
                  ·
                    refine ⟨39200865844866455203703093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26133910563244303469135395 39200865844866455203703093)
                    ·
                      refine ⟨3675081172956230175347165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39200865844866455203703093 3675081172956230175347165)
                      ·
                        rfl

theorem cell23_7157195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 5].length) (baseStart_7157195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157195 prefixEnd_7157195 := by exact prefixLift 7157195
  have htrace : WordTrace (prefixWord ++ tailWord_7157195) baseStart_7157195 baseEnd_7157195 := by
    simpa [prefixWord, tailWord_7157195, baseEnd_7157195] using wordTrace_append hprefix tailTrace_7157195
  have hstable : (prefixWord ++ tailWord_7157195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157195).length < 2 ^ (prefixWord ++ tailWord_7157195).sum := by decide
  have hdescent : baseEnd_7157195 < baseStart_7157195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157209 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 1, 4, 2]
def baseStart_7157209 : Nat := 118140960795 + 7157209 * 2 ^ 59
def prefixEnd_7157209 : Nat := 4983230072969 + 3 ^ 40 * 7157209 * 2
def baseEnd_7157209 : Nat := 3675088361685393120572101

theorem tailTrace_7157209 : CollatzResearch.WordTrace tailWord_7157209 prefixEnd_7157209 3675088361685393120572101 := by
  unfold tailWord_7157209
  simp only [CollatzResearch.WordTrace]
  refine ⟨261044857927661621825738681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174029905285107747883825787 261044857927661621825738681)
  ·
    refine ⟨195783643445746216369304011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261044857927661621825738681 195783643445746216369304011)
    ·
      refine ⟨293675465168619324553956017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195783643445746216369304011 293675465168619324553956017)
      ·
        refine ⟨220256598876464493415467013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293675465168619324553956017 220256598876464493415467013)
        ·
          refine ⟨41298112289337092515400065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220256598876464493415467013 41298112289337092515400065)
          ·
            refine ⟨30973584217002819386550049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41298112289337092515400065 30973584217002819386550049)
            ·
              refine ⟨23230188162752114539912537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30973584217002819386550049 23230188162752114539912537)
              ·
                refine ⟨17422641122064085904934403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23230188162752114539912537 17422641122064085904934403)
                ·
                  refine ⟨26133961683096128857401605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17422641122064085904934403 26133961683096128857401605)
                  ·
                    refine ⟨4900117815580524160762801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26133961683096128857401605 4900117815580524160762801)
                    ·
                      refine ⟨3675088361685393120572101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900117815580524160762801 3675088361685393120572101)
                      ·
                        rfl

theorem cell23_7157209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_7157209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157209 prefixEnd_7157209 := by exact prefixLift 7157209
  have htrace : WordTrace (prefixWord ++ tailWord_7157209) baseStart_7157209 baseEnd_7157209 := by
    simpa [prefixWord, tailWord_7157209, baseEnd_7157209] using wordTrace_append hprefix tailTrace_7157209
  have hstable : (prefixWord ++ tailWord_7157209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157209).length < 2 ^ (prefixWord ++ tailWord_7157209).sum := by decide
  have hdescent : baseEnd_7157209 < baseStart_7157209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157213 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_7157213 : Nat := 118140960795 + 7157213 * 2 ^ 59
def prefixEnd_7157213 : Nat := 4983230072969 + 3 ^ 40 * 7157213 * 2
def baseEnd_7157213 : Nat := 3675090415608011104922083

theorem tailTrace_7157213 : CollatzResearch.WordTrace tailWord_7157213 prefixEnd_7157213 3675090415608011104922083 := by
  unfold tailWord_7157213
  simp only [CollatzResearch.WordTrace]
  refine ⟨261045003819647130508884293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174030002546431420339256195 261045003819647130508884293)
  ·
    refine ⟨48945938216183836970415805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261045003819647130508884293 48945938216183836970415805)
    ·
      refine ⟨18354726831068938863905927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48945938216183836970415805 18354726831068938863905927)
      ·
        refine ⟨27532090246603408295858891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18354726831068938863905927 27532090246603408295858891)
        ·
          refine ⟨41298135369905112443788337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27532090246603408295858891 41298135369905112443788337)
          ·
            refine ⟨30973601527428834332841253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41298135369905112443788337 30973601527428834332841253)
            ·
              refine ⟨5807550286392906437407735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30973601527428834332841253 5807550286392906437407735)
              ·
                refine ⟨8711325429589359656111603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807550286392906437407735 8711325429589359656111603)
                ·
                  refine ⟨13066988144384039484167405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711325429589359656111603 13066988144384039484167405)
                  ·
                    refine ⟨4900120554144014806562777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13066988144384039484167405 4900120554144014806562777)
                    ·
                      refine ⟨3675090415608011104922083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900120554144014806562777 3675090415608011104922083)
                      ·
                        rfl

theorem cell23_7157213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_7157213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157213 prefixEnd_7157213 := by exact prefixLift 7157213
  have htrace : WordTrace (prefixWord ++ tailWord_7157213) baseStart_7157213 baseEnd_7157213 := by
    simpa [prefixWord, tailWord_7157213, baseEnd_7157213] using wordTrace_append hprefix tailTrace_7157213
  have hstable : (prefixWord ++ tailWord_7157213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157213).length < 2 ^ (prefixWord ++ tailWord_7157213).sum := by decide
  have hdescent : baseEnd_7157213 < baseStart_7157213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157215 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 9]
def baseStart_7157215 : Nat := 118140960795 + 7157215 * 2 ^ 59
def prefixEnd_7157215 : Nat := 4983230072969 + 3 ^ 40 * 7157215 * 2
def baseEnd_7157215 : Nat := 408343493618813344121897

theorem tailTrace_7157215 : CollatzResearch.WordTrace tailWord_7157215 prefixEnd_7157215 408343493618813344121897 := by
  unfold tailWord_7157215
  simp only [CollatzResearch.WordTrace]
  refine ⟨261045076765639884850457099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174030051177093256566971399 261045076765639884850457099)
  ·
    refine ⟨391567615148459827275685649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261045076765639884850457099 391567615148459827275685649)
    ·
      refine ⟨293675711361344870456764237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391567615148459827275685649 293675711361344870456764237)
      ·
        refine ⟨110128391760504326421286589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293675711361344870456764237 110128391760504326421286589)
        ·
          refine ⟨41298146910189122407982471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110128391760504326421286589 41298146910189122407982471)
          ·
            refine ⟨61947220365283683611973707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41298146910189122407982471 61947220365283683611973707)
            ·
              refine ⟨92920830547925525417960561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61947220365283683611973707 92920830547925525417960561)
              ·
                refine ⟨69690622910944144063470421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92920830547925525417960561 69690622910944144063470421)
                ·
                  refine ⟨408343493618813344121897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69690622910944144063470421 408343493618813344121897)
                  ·
                    rfl

theorem cell23_7157215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 9].length) (baseStart_7157215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157215 prefixEnd_7157215 := by exact prefixLift 7157215
  have htrace : WordTrace (prefixWord ++ tailWord_7157215) baseStart_7157215 baseEnd_7157215 := by
    simpa [prefixWord, tailWord_7157215, baseEnd_7157215] using wordTrace_append hprefix tailTrace_7157215
  have hstable : (prefixWord ++ tailWord_7157215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157215).length < 2 ^ (prefixWord ++ tailWord_7157215).sum := by decide
  have hdescent : baseEnd_7157215 < baseStart_7157215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157232 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 7]
def baseStart_7157232 : Nat := 118140960795 + 7157232 * 2 ^ 59
def prefixEnd_7157232 : Nat := 4983230072969 + 3 ^ 40 * 7157232 * 2
def baseEnd_7157232 : Nat := 408344463526716281176055

theorem tailTrace_7157232 : CollatzResearch.WordTrace tailWord_7157232 prefixEnd_7157232 408344463526716281176055 := by
  unfold tailWord_7157232
  simp only [CollatzResearch.WordTrace]
  refine ⟨130522848403289148376912975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174030464537718864502550633 130522848403289148376912975)
  ·
    refine ⟨195784272604933722565369463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130522848403289148376912975 195784272604933722565369463)
    ·
      refine ⟨293676408907400583848054195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195784272604933722565369463 293676408907400583848054195)
      ·
        refine ⟨440514613361100875772081293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293676408907400583848054195 440514613361100875772081293)
        ·
          refine ⟨165192980010412828414530485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440514613361100875772081293 165192980010412828414530485)
          ·
            refine ⟨15486841875976202663862233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165192980010412828414530485 15486841875976202663862233)
            ·
              refine ⟨11615131406982151997896675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15486841875976202663862233 11615131406982151997896675)
              ·
                refine ⟨17422697110473227996845013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11615131406982151997896675 17422697110473227996845013)
                ·
                  refine ⟨408344463526716281176055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17422697110473227996845013 408344463526716281176055)
                  ·
                    rfl

theorem cell23_7157232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 7].length) (baseStart_7157232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157232 prefixEnd_7157232 := by exact prefixLift 7157232
  have htrace : WordTrace (prefixWord ++ tailWord_7157232) baseStart_7157232 baseEnd_7157232 := by
    simpa [prefixWord, tailWord_7157232, baseEnd_7157232] using wordTrace_append hprefix tailTrace_7157232
  have hstable : (prefixWord ++ tailWord_7157232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157232).length < 2 ^ (prefixWord ++ tailWord_7157232).sum := by decide
  have hdescent : baseEnd_7157232 < baseStart_7157232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157242 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3]
def baseStart_7157242 : Nat := 118140960795 + 7157242 * 2 ^ 59
def prefixEnd_7157242 : Nat := 4983230072969 + 3 ^ 40 * 7157242 * 2
def baseEnd_7157242 : Nat := 3675105306546991491459449

theorem tailTrace_7157242 : CollatzResearch.WordTrace tailWord_7157242 prefixEnd_7157242 3675105306546991491459449 := by
  unfold tailWord_7157242
  simp only [CollatzResearch.WordTrace]
  refine ⟨65261515384135517115422495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174030707691028045641126653 65261515384135517115422495)
  ·
    refine ⟨97892273076203275673133743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65261515384135517115422495 97892273076203275673133743)
    ·
      refine ⟨146838409614304913509700615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97892273076203275673133743 146838409614304913509700615)
      ·
        refine ⟨220257614421457370264550923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146838409614304913509700615 220257614421457370264550923)
        ·
          refine ⟨330386421632186055396826385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220257614421457370264550923 330386421632186055396826385)
          ·
            refine ⟨247789816224139541547619789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330386421632186055396826385 247789816224139541547619789)
            ·
              refine ⟨92921181084052328080357421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247789816224139541547619789 92921181084052328080357421)
              ·
                refine ⟨34845442906519623030134033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92921181084052328080357421 34845442906519623030134033)
                ·
                  refine ⟨26134082179889717272600525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34845442906519623030134033 26134082179889717272600525)
                  ·
                    refine ⟨9800280817458643977225197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26134082179889717272600525 9800280817458643977225197)
                    ·
                      refine ⟨3675105306546991491459449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9800280817458643977225197 3675105306546991491459449)
                      ·
                        rfl

theorem cell23_7157242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_7157242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157242 prefixEnd_7157242 := by exact prefixLift 7157242
  have htrace : WordTrace (prefixWord ++ tailWord_7157242) baseStart_7157242 baseEnd_7157242 := by
    simpa [prefixWord, tailWord_7157242, baseEnd_7157242] using wordTrace_append hprefix tailTrace_7157242
  have hstable : (prefixWord ++ tailWord_7157242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157242).length < 2 ^ (prefixWord ++ tailWord_7157242).sum := by decide
  have hdescent : baseEnd_7157242 < baseStart_7157242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157326 : List Nat := [4, 1, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_7157326 : Nat := 118140960795 + 7157326 * 2 ^ 59
def prefixEnd_7157326 : Nat := 4983230072969 + 3 ^ 40 * 7157326 * 2
def baseEnd_7157326 : Nat := 1225049479640656387603021

theorem tailTrace_7157326 : CollatzResearch.WordTrace tailWord_7157326 prefixEnd_7157326 1225049479640656387603021 := by
  unfold tailWord_7157326
  simp only [CollatzResearch.WordTrace]
  refine ⟨32631140658529718850968479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174032750178825167205165221 32631140658529718850968479)
  ·
    refine ⟨48946710987794578276452719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32631140658529718850968479 48946710987794578276452719)
    ·
      refine ⟨73420066481691867414679079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48946710987794578276452719 73420066481691867414679079)
      ·
        refine ⟨110130099722537801122018619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73420066481691867414679079 110130099722537801122018619)
        ·
          refine ⟨165195149583806701683027929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110130099722537801122018619 165195149583806701683027929)
          ·
            refine ⟨123896362187855026262270947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165195149583806701683027929 123896362187855026262270947)
            ·
              refine ⟨185844543281782539393406421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123896362187855026262270947 185844543281782539393406421)
              ·
                refine ⟨4355731483166778267032963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 185844543281782539393406421 4355731483166778267032963)
                ·
                  refine ⟨6533597224750167400549445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355731483166778267032963 6533597224750167400549445)
                  ·
                    refine ⟨1225049479640656387603021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6533597224750167400549445 1225049479640656387603021)
                    ·
                      rfl

theorem cell23_7157326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_7157326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157326 prefixEnd_7157326 := by exact prefixLift 7157326
  have htrace : WordTrace (prefixWord ++ tailWord_7157326) baseStart_7157326 baseEnd_7157326 := by
    simpa [prefixWord, tailWord_7157326, baseEnd_7157326] using wordTrace_append hprefix tailTrace_7157326
  have hstable : (prefixWord ++ tailWord_7157326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157326).length < 2 ^ (prefixWord ++ tailWord_7157326).sum := by decide
  have hdescent : baseEnd_7157326 < baseStart_7157326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157334 : List Nat := [5, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_7157334 : Nat := 118140960795 + 7157334 * 2 ^ 59
def prefixEnd_7157334 : Nat := 4983230072969 + 3 ^ 40 * 7157334 * 2
def baseEnd_7157334 : Nat := 408350282974133903501003

theorem tailTrace_7157334 : CollatzResearch.WordTrace tailWord_7157334 prefixEnd_7157334 408350282974133903501003 := by
  unfold tailWord_7157334
  simp only [CollatzResearch.WordTrace]
  refine ⟨16315588565763048010877441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174032944701472512116026037 16315588565763048010877441)
  ·
    refine ⟨12236691424322286008158081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16315588565763048010877441 12236691424322286008158081)
    ·
      refine ⟨9177518568241714506118561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12236691424322286008158081 9177518568241714506118561)
      ·
        refine ⟨6883138926181285879588921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9177518568241714506118561 6883138926181285879588921)
        ·
          refine ⟨5162354194635964409691691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6883138926181285879588921 5162354194635964409691691)
          ·
            refine ⟨7743531291953946614537537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162354194635964409691691 7743531291953946614537537)
            ·
              refine ⟨5807648468965459960903153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7743531291953946614537537 5807648468965459960903153)
              ·
                refine ⟨4355736351724094970677365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5807648468965459960903153 4355736351724094970677365)
                ·
                  refine ⟨408350282974133903501003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4355736351724094970677365 408350282974133903501003)
                  ·
                    rfl

theorem cell23_7157334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_7157334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157334 prefixEnd_7157334 := by exact prefixLift 7157334
  have htrace : WordTrace (prefixWord ++ tailWord_7157334) baseStart_7157334 baseEnd_7157334 := by
    simpa [prefixWord, tailWord_7157334, baseEnd_7157334] using wordTrace_append hprefix tailTrace_7157334
  have hstable : (prefixWord ++ tailWord_7157334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157334).length < 2 ^ (prefixWord ++ tailWord_7157334).sum := by decide
  have hdescent : baseEnd_7157334 < baseStart_7157334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157359 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 1, 5, 2]
def baseStart_7157359 : Nat := 118140960795 + 7157359 * 2 ^ 59
def prefixEnd_7157359 : Nat := 4983230072969 + 3 ^ 40 * 7157359 * 2
def baseEnd_7157359 : Nat := 3675165383783567533696411

theorem tailTrace_7157359 : CollatzResearch.WordTrace tailWord_7157359 prefixEnd_7157359 3675165383783567533696411 := by
  unfold tailWord_7157359
  simp only [CollatzResearch.WordTrace]
  refine ⟨261050328877118197443699131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174033552584745464962466087 261050328877118197443699131)
  ·
    refine ⟨391575493315677296165548697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261050328877118197443699131 391575493315677296165548697)
    ·
      refine ⟨293681619986757972124161523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391575493315677296165548697 293681619986757972124161523)
      ·
        refine ⟨440522429980136958186242285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293681619986757972124161523 440522429980136958186242285)
        ·
          refine ⟨165195911242551359319840857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440522429980136958186242285 165195911242551359319840857)
          ·
            refine ⟨123896933431913519489880643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165195911242551359319840857 123896933431913519489880643)
            ·
              refine ⟨185845400147870279234820965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123896933431913519489880643 185845400147870279234820965)
              ·
                refine ⟨34846012527725677356528931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185845400147870279234820965 34846012527725677356528931)
                ·
                  refine ⟨52269018791588516034793397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34846012527725677356528931 52269018791588516034793397)
                  ·
                    refine ⟨4900220511711423378261881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52269018791588516034793397 4900220511711423378261881)
                    ·
                      refine ⟨3675165383783567533696411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900220511711423378261881 3675165383783567533696411)
                      ·
                        rfl

theorem cell23_7157359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 5, 2].length) (baseStart_7157359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157359 prefixEnd_7157359 := by exact prefixLift 7157359
  have htrace : WordTrace (prefixWord ++ tailWord_7157359) baseStart_7157359 baseEnd_7157359 := by
    simpa [prefixWord, tailWord_7157359, baseEnd_7157359] using wordTrace_append hprefix tailTrace_7157359
  have hstable : (prefixWord ++ tailWord_7157359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157359).length < 2 ^ (prefixWord ++ tailWord_7157359).sum := by decide
  have hdescent : baseEnd_7157359 < baseStart_7157359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157369 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 1, 5]
def baseStart_7157369 : Nat := 118140960795 + 7157369 * 2 ^ 59
def prefixEnd_7157369 : Nat := 4983230072969 + 3 ^ 40 * 7157369 * 2
def baseEnd_7157369 : Nat := 1225056839530037498190455

theorem tailTrace_7157369 : CollatzResearch.WordTrace tailWord_7157369 prefixEnd_7157369 1225056839530037498190455 := by
  unfold tailWord_7157369
  simp only [CollatzResearch.WordTrace]
  refine ⟨261050693607081969151563161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174033795738054646101042107 261050693607081969151563161)
  ·
    refine ⟨195788020205311476863672371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261050693607081969151563161 195788020205311476863672371)
    ·
      refine ⟨293682030307967215295508557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195788020205311476863672371 293682030307967215295508557)
      ·
        refine ⟨110130761365487705735815709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293682030307967215295508557 110130761365487705735815709)
        ·
          refine ⟨41299035512057889650930891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110130761365487705735815709 41299035512057889650930891)
          ·
            refine ⟨61948553268086834476396337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41299035512057889650930891 61948553268086834476396337)
            ·
              refine ⟨46461414951065125857297253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61948553268086834476396337 46461414951065125857297253)
              ·
                refine ⟨8711515303324711098243235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46461414951065125857297253 8711515303324711098243235)
                ·
                  refine ⟨13067272954987066647364853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711515303324711098243235 13067272954987066647364853)
                  ·
                    refine ⟨1225056839530037498190455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13067272954987066647364853 1225056839530037498190455)
                    ·
                      rfl

theorem cell23_7157369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 5].length) (baseStart_7157369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157369 prefixEnd_7157369 := by exact prefixLift 7157369
  have htrace : WordTrace (prefixWord ++ tailWord_7157369) baseStart_7157369 baseEnd_7157369 := by
    simpa [prefixWord, tailWord_7157369, baseEnd_7157369] using wordTrace_append hprefix tailTrace_7157369
  have hstable : (prefixWord ++ tailWord_7157369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157369).length < 2 ^ (prefixWord ++ tailWord_7157369).sum := by decide
  have hdescent : baseEnd_7157369 < baseStart_7157369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157383 : List Nat := [1, 1, 4, 2, 1, 3, 1, 5, 1, 1, 3]
def baseStart_7157383 : Nat := 118140960795 + 7157383 * 2 ^ 59
def prefixEnd_7157383 : Nat := 4983230072969 + 3 ^ 40 * 7157383 * 2
def baseEnd_7157383 : Nat := 3675177707319275439796301

theorem tailTrace_7157383 : CollatzResearch.WordTrace tailWord_7157383 prefixEnd_7157383 3675177707319275439796301 := by
  unfold tailWord_7157383
  simp only [CollatzResearch.WordTrace]
  refine ⟨261051204229031249542572803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174034136152687499695048535 261051204229031249542572803)
  ·
    refine ⟨391576806343546874313859205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261051204229031249542572803 391576806343546874313859205)
    ·
      refine ⟨73420651189415038933848601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391576806343546874313859205 73420651189415038933848601)
      ·
        refine ⟨55065488392061279200386451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73420651189415038933848601 55065488392061279200386451)
        ·
          refine ⟨82598232588091918800579677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55065488392061279200386451 82598232588091918800579677)
          ·
            refine ⟨30974337220534469550217379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82598232588091918800579677 30974337220534469550217379)
            ·
              refine ⟨46461505830801704325326069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30974337220534469550217379 46461505830801704325326069)
              ·
                refine ⟨4355766171637659780499319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46461505830801704325326069 4355766171637659780499319)
                ·
                  refine ⟨6533649257456489670748979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355766171637659780499319 6533649257456489670748979)
                  ·
                    refine ⟨9800473886184734506123469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6533649257456489670748979 9800473886184734506123469)
                    ·
                      refine ⟨3675177707319275439796301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9800473886184734506123469 3675177707319275439796301)
                      ·
                        rfl

theorem cell23_7157383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_7157383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157383 prefixEnd_7157383 := by exact prefixLift 7157383
  have htrace : WordTrace (prefixWord ++ tailWord_7157383) baseStart_7157383 baseEnd_7157383 := by
    simpa [prefixWord, tailWord_7157383, baseEnd_7157383] using wordTrace_append hprefix tailTrace_7157383
  have hstable : (prefixWord ++ tailWord_7157383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157383).length < 2 ^ (prefixWord ++ tailWord_7157383).sum := by decide
  have hdescent : baseEnd_7157383 < baseStart_7157383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157386 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_7157386 : Nat := 118140960795 + 7157386 * 2 ^ 59
def prefixEnd_7157386 : Nat := 4983230072969 + 3 ^ 40 * 7157386 * 2
def baseEnd_7157386 : Nat := 1225059749253746309352929

theorem tailTrace_7157386 : CollatzResearch.WordTrace tailWord_7157386 prefixEnd_7157386 1225059749253746309352929 := by
  unfold tailWord_7157386
  simp only [CollatzResearch.WordTrace]
  refine ⟨65262828412005095263733003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174034209098680254036621341 65262828412005095263733003)
  ·
    refine ⟨97894242618007642895599505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65262828412005095263733003 97894242618007642895599505)
    ·
      refine ⟨73420681963505732171699629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97894242618007642895599505 73420681963505732171699629)
      ·
        refine ⟨27532755736314649564387361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73420681963505732171699629 27532755736314649564387361)
        ·
          refine ⟨20649566802235987173290521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27532755736314649564387361 20649566802235987173290521)
          ·
            refine ⟨15487175101676990379967891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20649566802235987173290521 15487175101676990379967891)
            ·
              refine ⟨23230762652515485569951837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15487175101676990379967891 23230762652515485569951837)
              ·
                refine ⟨8711535994693307088731939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23230762652515485569951837 8711535994693307088731939)
                ·
                  refine ⟨13067303992039960633097909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711535994693307088731939 13067303992039960633097909)
                  ·
                    refine ⟨1225059749253746309352929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13067303992039960633097909 1225059749253746309352929)
                    ·
                      rfl

theorem cell23_7157386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_7157386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157386 prefixEnd_7157386 := by exact prefixLift 7157386
  have htrace : WordTrace (prefixWord ++ tailWord_7157386) baseStart_7157386 baseEnd_7157386 := by
    simpa [prefixWord, tailWord_7157386, baseEnd_7157386] using wordTrace_append hprefix tailTrace_7157386
  have hstable : (prefixWord ++ tailWord_7157386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157386).length < 2 ^ (prefixWord ++ tailWord_7157386).sum := by decide
  have hdescent : baseEnd_7157386 < baseStart_7157386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157392 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_7157392 : Nat := 118140960795 + 7157392 * 2 ^ 59
def prefixEnd_7157392 : Nat := 4983230072969 + 3 ^ 40 * 7157392 * 2
def baseEnd_7157392 : Nat := 3675182328645165904583759

theorem tailTrace_7157392 : CollatzResearch.WordTrace tailWord_7157392 prefixEnd_7157392 3675182328645165904583759 := by
  unfold tailWord_7157392
  simp only [CollatzResearch.WordTrace]
  refine ⟨130525766242999322039825215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174034354990665762719766953 130525766242999322039825215)
  ·
    refine ⟨195788649364498983059737823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130525766242999322039825215 195788649364498983059737823)
    ·
      refine ⟨293682974046748474589606735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195788649364498983059737823 293682974046748474589606735)
      ·
        refine ⟨440524461070122711884410103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293682974046748474589606735 440524461070122711884410103)
        ·
          refine ⟨660786691605184067826615155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440524461070122711884410103 660786691605184067826615155)
          ·
            refine ⟨991180037407776101739922733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660786691605184067826615155 991180037407776101739922733)
            ·
              refine ⟨371692514027916038152471025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 991180037407776101739922733 371692514027916038152471025)
              ·
                refine ⟨278769385520937028614353269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371692514027916038152471025 278769385520937028614353269)
                ·
                  refine ⟨26134629892587846432595619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278769385520937028614353269 26134629892587846432595619)
                  ·
                    refine ⟨39201944838881769648893429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26134629892587846432595619 39201944838881769648893429)
                    ·
                      refine ⟨3675182328645165904583759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39201944838881769648893429 3675182328645165904583759)
                      ·
                        rfl

theorem cell23_7157392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_7157392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157392 prefixEnd_7157392 := by exact prefixLift 7157392
  have htrace : WordTrace (prefixWord ++ tailWord_7157392) baseStart_7157392 baseEnd_7157392 := by
    simpa [prefixWord, tailWord_7157392, baseEnd_7157392] using wordTrace_append hprefix tailTrace_7157392
  have hstable : (prefixWord ++ tailWord_7157392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157392).length < 2 ^ (prefixWord ++ tailWord_7157392).sum := by decide
  have hdescent : baseEnd_7157392 < baseStart_7157392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157409 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7157409 : Nat := 118140960795 + 7157409 * 2 ^ 59
def prefixEnd_7157409 : Nat := 4983230072969 + 3 ^ 40 * 7157409 * 2
def baseEnd_7157409 : Nat := 3675191057816292338071181

theorem tailTrace_7157409 : CollatzResearch.WordTrace tailWord_7157409 prefixEnd_7157409 3675191057816292338071181 := by
  unfold tailWord_7157409
  simp only [CollatzResearch.WordTrace]
  refine ⟨261052152526937055983019281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174034768351291370655346187 261052152526937055983019281)
  ·
    refine ⟨195789114395202791987264461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261052152526937055983019281 195789114395202791987264461)
    ·
      refine ⟨73420917898201046995224173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195789114395202791987264461 73420917898201046995224173)
      ·
        refine ⟨27532844211825392623209065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73420917898201046995224173 27532844211825392623209065)
        ·
          refine ⟨20649633158869044467406799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27532844211825392623209065 20649633158869044467406799)
          ·
            refine ⟨30974449738303566701110199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20649633158869044467406799 30974449738303566701110199)
            ·
              refine ⟨46461674607455350051665299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30974449738303566701110199 46461674607455350051665299)
              ·
                refine ⟨69692511911183025077497949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46461674607455350051665299 69692511911183025077497949)
                ·
                  refine ⟨26134691966693634404061731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69692511911183025077497949 26134691966693634404061731)
                  ·
                    refine ⟨39202037950040451606092597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26134691966693634404061731 39202037950040451606092597)
                    ·
                      refine ⟨3675191057816292338071181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39202037950040451606092597 3675191057816292338071181)
                      ·
                        rfl

theorem cell23_7157409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7157409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157409 prefixEnd_7157409 := by exact prefixLift 7157409
  have htrace : WordTrace (prefixWord ++ tailWord_7157409) baseStart_7157409 baseEnd_7157409 := by
    simpa [prefixWord, tailWord_7157409, baseEnd_7157409] using wordTrace_append hprefix tailTrace_7157409
  have hstable : (prefixWord ++ tailWord_7157409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157409).length < 2 ^ (prefixWord ++ tailWord_7157409).sum := by decide
  have hdescent : baseEnd_7157409 < baseStart_7157409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157426 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_7157426 : Nat := 118140960795 + 7157426 * 2 ^ 59
def prefixEnd_7157426 : Nat := 4983230072969 + 3 ^ 40 * 7157426 * 2
def baseEnd_7157426 : Nat := 3675199786987418771558603

theorem tailTrace_7157426 : CollatzResearch.WordTrace tailWord_7157426 prefixEnd_7157426 3675199786987418771558603 := by
  unfold tailWord_7157426
  simp only [CollatzResearch.WordTrace]
  refine ⟨65263193141968866971597033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174035181711916978590925421 65263193141968866971597033)
  ·
    refine ⟨48947394856476650228697775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65263193141968866971597033 48947394856476650228697775)
    ·
      refine ⟨73421092284714975343046663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48947394856476650228697775 73421092284714975343046663)
      ·
        refine ⟨110131638427072463014569995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73421092284714975343046663 110131638427072463014569995)
        ·
          refine ⟨165197457640608694521854993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110131638427072463014569995 165197457640608694521854993)
          ·
            refine ⟨123898093230456520891391245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165197457640608694521854993 123898093230456520891391245)
            ·
              refine ⟨46461784961421195334271717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123898093230456520891391245 46461784961421195334271717)
              ·
                refine ⟨8711584680266474125175947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46461784961421195334271717 8711584680266474125175947)
                ·
                  refine ⟨13067377020399711187763921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711584680266474125175947 13067377020399711187763921)
                  ·
                    refine ⟨9800532765299783390822941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13067377020399711187763921 9800532765299783390822941)
                    ·
                      refine ⟨3675199786987418771558603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9800532765299783390822941 3675199786987418771558603)
                      ·
                        rfl

theorem cell23_7157426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_7157426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157426 prefixEnd_7157426 := by exact prefixLift 7157426
  have htrace : WordTrace (prefixWord ++ tailWord_7157426) baseStart_7157426 baseEnd_7157426 := by
    simpa [prefixWord, tailWord_7157426, baseEnd_7157426] using wordTrace_append hprefix tailTrace_7157426
  have hstable : (prefixWord ++ tailWord_7157426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157426).length < 2 ^ (prefixWord ++ tailWord_7157426).sum := by decide
  have hdescent : baseEnd_7157426 < baseStart_7157426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157432 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_7157432 : Nat := 118140960795 + 7157432 * 2 ^ 59
def prefixEnd_7157432 : Nat := 4983230072969 + 3 ^ 40 * 7157432 * 2
def baseEnd_7157432 : Nat := 3675202867871345748083575

theorem tailTrace_7157432 : CollatzResearch.WordTrace tailWord_7157432 prefixEnd_7157432 3675202867871345748083575 := by
  unfold tailWord_7157432
  simp only [CollatzResearch.WordTrace]
  refine ⟨130526495702926865455553275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174035327603902487274071033 130526495702926865455553275)
  ·
    refine ⟨195789743554390298183329913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130526495702926865455553275 195789743554390298183329913)
    ·
      refine ⟨146842307665792723637497435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195789743554390298183329913 146842307665792723637497435)
      ·
        refine ⟨220263461498689085456246153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146842307665792723637497435 220263461498689085456246153)
        ·
          refine ⟨165197596124016814092184615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220263461498689085456246153 165197596124016814092184615)
          ·
            refine ⟨247796394186025221138276923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165197596124016814092184615 247796394186025221138276923)
            ·
              refine ⟨371694591279037831707415385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247796394186025221138276923 371694591279037831707415385)
              ·
                refine ⟨278770943459278373780561539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371694591279037831707415385 278770943459278373780561539)
                ·
                  refine ⟨418156415188917560670842309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278770943459278373780561539 418156415188917560670842309)
                  ·
                    refine ⟨78404327847922042625782933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 418156415188917560670842309 78404327847922042625782933)
                    ·
                      refine ⟨3675202867871345748083575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78404327847922042625782933 3675202867871345748083575)
                      ·
                        rfl

theorem cell23_7157432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_7157432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157432 prefixEnd_7157432 := by exact prefixLift 7157432
  have htrace : WordTrace (prefixWord ++ tailWord_7157432) baseStart_7157432 baseEnd_7157432 := by
    simpa [prefixWord, tailWord_7157432, baseEnd_7157432] using wordTrace_append hprefix tailTrace_7157432
  have hstable : (prefixWord ++ tailWord_7157432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157432).length < 2 ^ (prefixWord ++ tailWord_7157432).sum := by decide
  have hdescent : baseEnd_7157432 < baseStart_7157432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157439 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 3]
def baseStart_7157439 : Nat := 118140960795 + 7157439 * 2 ^ 59
def prefixEnd_7157439 : Nat := 4983230072969 + 3 ^ 40 * 7157439 * 2
def baseEnd_7157439 : Nat := 3675206462235927220696043

theorem tailTrace_7157439 : CollatzResearch.WordTrace tailWord_7157439 prefixEnd_7157439 3675206462235927220696043 := by
  unfold tailWord_7157439
  simp only [CollatzResearch.WordTrace]
  refine ⟨261053246716828371106611371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174035497811218914071074247 261053246716828371106611371)
  ·
    refine ⟨391579870075242556659917057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261053246716828371106611371 391579870075242556659917057)
    ·
      refine ⟨293684902556431917494937793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391579870075242556659917057 293684902556431917494937793)
      ·
        refine ⟨220263676917323938121203345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293684902556431917494937793 220263676917323938121203345)
        ·
          refine ⟨165197757687992953590902509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220263676917323938121203345 165197757687992953590902509)
          ·
            refine ⟨61949159132997357596588441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165197757687992953590902509 61949159132997357596588441)
            ·
              refine ⟨46461869349748018197441331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61949159132997357596588441 46461869349748018197441331)
              ·
                refine ⟨69692804024622027296161997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46461869349748018197441331 69692804024622027296161997)
                ·
                  refine ⟨26134801509233260236060749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69692804024622027296161997 26134801509233260236060749)
                  ·
                    refine ⟨9800550565962472588522781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26134801509233260236060749 9800550565962472588522781)
                    ·
                      refine ⟨3675206462235927220696043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9800550565962472588522781 3675206462235927220696043)
                      ·
                        rfl

theorem cell23_7157439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_7157439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157439 prefixEnd_7157439 := by exact prefixLift 7157439
  have htrace : WordTrace (prefixWord ++ tailWord_7157439) baseStart_7157439 baseEnd_7157439 := by
    simpa [prefixWord, tailWord_7157439, baseEnd_7157439] using wordTrace_append hprefix tailTrace_7157439
  have hstable : (prefixWord ++ tailWord_7157439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157439).length < 2 ^ (prefixWord ++ tailWord_7157439).sum := by decide
  have hdescent : baseEnd_7157439 < baseStart_7157439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157457 : List Nat := [1, 2, 2, 1, 2, 5, 3, 2, 1, 2, 2]
def baseStart_7157457 : Nat := 118140960795 + 7157457 * 2 ^ 59
def prefixEnd_7157457 : Nat := 4983230072969 + 3 ^ 40 * 7157457 * 2
def baseEnd_7157457 : Nat := 3675215704887708150270961

theorem tailTrace_7157457 : CollatzResearch.WordTrace tailWord_7157457 prefixEnd_7157457 3675215704887708150270961 := by
  unfold tailWord_7157457
  simp only [CollatzResearch.WordTrace]
  refine ⟨261053903230763160180766625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174035935487175440120511083 261053903230763160180766625)
  ·
    refine ⟨195790427423072370135574969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261053903230763160180766625 195790427423072370135574969)
    ·
      refine ⟨146842820567304277601681227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195790427423072370135574969 146842820567304277601681227)
      ·
        refine ⟨220264230850956416402521841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146842820567304277601681227 220264230850956416402521841)
        ·
          refine ⟨165198173138217312301891381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220264230850956416402521841 165198173138217312301891381)
          ·
            refine ⟨15487328731707873028302317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165198173138217312301891381 15487328731707873028302317)
            ·
              refine ⟨5807748274390452385613369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15487328731707873028302317 5807748274390452385613369)
              ·
                refine ⟨4355811205792839289210027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5807748274390452385613369 4355811205792839289210027)
                ·
                  refine ⟨6533716808689258933815041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355811205792839289210027 6533716808689258933815041)
                  ·
                    refine ⟨4900287606516944200361281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6533716808689258933815041 4900287606516944200361281)
                    ·
                      refine ⟨3675215704887708150270961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900287606516944200361281 3675215704887708150270961)
                      ·
                        rfl

theorem cell23_7157457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 1, 2, 2].length) (baseStart_7157457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157457 prefixEnd_7157457 := by exact prefixLift 7157457
  have htrace : WordTrace (prefixWord ++ tailWord_7157457) baseStart_7157457 baseEnd_7157457 := by
    simpa [prefixWord, tailWord_7157457, baseEnd_7157457] using wordTrace_append hprefix tailTrace_7157457
  have hstable : (prefixWord ++ tailWord_7157457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157457).length < 2 ^ (prefixWord ++ tailWord_7157457).sum := by decide
  have hdescent : baseEnd_7157457 < baseStart_7157457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157483 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 1, 3, 2]
def baseStart_7157483 : Nat := 118140960795 + 7157483 * 2 ^ 59
def prefixEnd_7157483 : Nat := 4983230072969 + 3 ^ 40 * 7157483 * 2
def baseEnd_7157483 : Nat := 3675229055384725048545841

theorem tailTrace_7157483 : CollatzResearch.WordTrace tailWord_7157483 prefixEnd_7157483 3675229055384725048545841 := by
  unfold tailWord_7157483
  simp only [CollatzResearch.WordTrace]
  refine ⟨261054851528668966621213103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174036567685779311080808735 261054851528668966621213103)
  ·
    refine ⟨391582277293003449931819655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261054851528668966621213103 391582277293003449931819655)
    ·
      refine ⟨587373415939505174897729483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391582277293003449931819655 587373415939505174897729483)
      ·
        refine ⟨881060123909257762346594225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587373415939505174897729483 881060123909257762346594225)
        ·
          refine ⟨660795092931943321759945669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 881060123909257762346594225 660795092931943321759945669)
          ·
            refine ⟨123899079924739372829989813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 660795092931943321759945669 123899079924739372829989813)
            ·
              refine ⟨11615538742944316202811545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123899079924739372829989813 11615538742944316202811545)
              ·
                refine ⟨8711654057208237152108659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11615538742944316202811545 8711654057208237152108659)
                ·
                  refine ⟨13067481085812355728162989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711654057208237152108659 13067481085812355728162989)
                  ·
                    refine ⟨4900305407179633398061121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13067481085812355728162989 4900305407179633398061121)
                    ·
                      refine ⟨3675229055384725048545841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900305407179633398061121 3675229055384725048545841)
                      ·
                        rfl

theorem cell23_7157483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 3, 2].length) (baseStart_7157483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157483 prefixEnd_7157483 := by exact prefixLift 7157483
  have htrace : WordTrace (prefixWord ++ tailWord_7157483) baseStart_7157483 baseEnd_7157483 := by
    simpa [prefixWord, tailWord_7157483, baseEnd_7157483] using wordTrace_append hprefix tailTrace_7157483
  have hstable : (prefixWord ++ tailWord_7157483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157483).length < 2 ^ (prefixWord ++ tailWord_7157483).sum := by decide
  have hdescent : baseEnd_7157483 < baseStart_7157483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157500 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 1, 3, 2]
def baseStart_7157500 : Nat := 118140960795 + 7157500 * 2 ^ 59
def prefixEnd_7157500 : Nat := 4983230072969 + 3 ^ 40 * 7157500 * 2
def baseEnd_7157500 : Nat := 3675237784555851482033263

theorem tailTrace_7157500 : CollatzResearch.WordTrace tailWord_7157500 prefixEnd_7157500 3675237784555851482033263 := by
  unfold tailWord_7157500
  simp only [CollatzResearch.WordTrace]
  refine ⟨130527735784803689262290977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174036981046404919016387969 130527735784803689262290977)
  ·
    refine ⟨97895801838602766946718233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130527735784803689262290977 97895801838602766946718233)
    ·
      refine ⟨73421851378952075210038675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97895801838602766946718233 73421851378952075210038675)
      ·
        refine ⟨110132777068428112815058013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73421851378952075210038675 110132777068428112815058013)
        ·
          refine ⟨41299791400660542305646755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110132777068428112815058013 41299791400660542305646755)
          ·
            refine ⟨61949687100990813458470133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41299791400660542305646755 61949687100990813458470133)
            ·
              refine ⟨5807783165717888761731575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61949687100990813458470133 5807783165717888761731575)
              ·
                refine ⟨8711674748576833142597363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807783165717888761731575 8711674748576833142597363)
                ·
                  refine ⟨13067512122865249713896045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711674748576833142597363 13067512122865249713896045)
                  ·
                    refine ⟨4900317046074468642711017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13067512122865249713896045 4900317046074468642711017)
                    ·
                      refine ⟨3675237784555851482033263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900317046074468642711017 3675237784555851482033263)
                      ·
                        rfl

theorem cell23_7157500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_7157500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157500 prefixEnd_7157500 := by exact prefixLift 7157500
  have htrace : WordTrace (prefixWord ++ tailWord_7157500) baseStart_7157500 baseEnd_7157500 := by
    simpa [prefixWord, tailWord_7157500, baseEnd_7157500] using wordTrace_append hprefix tailTrace_7157500
  have hstable : (prefixWord ++ tailWord_7157500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157500).length < 2 ^ (prefixWord ++ tailWord_7157500).sum := by decide
  have hdescent : baseEnd_7157500 < baseStart_7157500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157506 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7157506 : Nat := 118140960795 + 7157506 * 2 ^ 59
def prefixEnd_7157506 : Nat := 4983230072969 + 3 ^ 40 * 7157506 * 2
def baseEnd_7157506 : Nat := 1225080288479926152852745

theorem tailTrace_7157506 : CollatzResearch.WordTrace tailWord_7157506 prefixEnd_7157506 1225080288479926152852745 := by
  unfold tailWord_7157506
  simp only [CollatzResearch.WordTrace]
  refine ⟨65263922601896410387325093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174037126938390427699533581 65263922601896410387325093)
  ·
    refine ⟨12236985487855576947623455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65263922601896410387325093 12236985487855576947623455)
    ·
      refine ⟨18355478231783365421435183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12236985487855576947623455 18355478231783365421435183)
      ·
        refine ⟨27533217347675048132152775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18355478231783365421435183 27533217347675048132152775)
        ·
          refine ⟨41299826021512572198229163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27533217347675048132152775 41299826021512572198229163)
          ·
            refine ⟨61949739032268858297343745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41299826021512572198229163 61949739032268858297343745)
            ·
              refine ⟨46462304274201643723007809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61949739032268858297343745 46462304274201643723007809)
              ·
                refine ⟨34846728205651232792255857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46462304274201643723007809 34846728205651232792255857)
                ·
                  refine ⟨26135046154238424594191893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34846728205651232792255857 26135046154238424594191893)
                  ·
                    refine ⟨1225080288479926152852745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26135046154238424594191893 1225080288479926152852745)
                    ·
                      rfl

theorem cell23_7157506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7157506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157506 prefixEnd_7157506 := by exact prefixLift 7157506
  have htrace : WordTrace (prefixWord ++ tailWord_7157506) baseStart_7157506 baseEnd_7157506 := by
    simpa [prefixWord, tailWord_7157506, baseEnd_7157506] using wordTrace_append hprefix tailTrace_7157506
  have hstable : (prefixWord ++ tailWord_7157506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157506).length < 2 ^ (prefixWord ++ tailWord_7157506).sum := by decide
  have hdescent : baseEnd_7157506 < baseStart_7157506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157530 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2]
def baseStart_7157530 : Nat := 118140960795 + 7157530 * 2 ^ 59
def prefixEnd_7157530 : Nat := 4983230072969 + 3 ^ 40 * 7157530 * 2
def baseEnd_7157530 : Nat := 3675253188975486364658125

theorem tailTrace_7157530 : CollatzResearch.WordTrace tailWord_7157530 prefixEnd_7157530 3675253188975486364658125 := by
  unfold tailWord_7157530
  simp only [CollatzResearch.WordTrace]
  refine ⟨65264141439874673412043511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174037710506332462432116029 65264141439874673412043511)
  ·
    refine ⟨97896212159812010118065267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65264141439874673412043511 97896212159812010118065267)
    ·
      refine ⟨146844318239718015177097901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97896212159812010118065267 146844318239718015177097901)
      ·
        refine ⟨55066619339894255691411713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146844318239718015177097901 55066619339894255691411713)
        ·
          refine ⟨41299964504920691768558785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55066619339894255691411713 41299964504920691768558785)
          ·
            refine ⟨30974973378690518826419089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41299964504920691768558785 30974973378690518826419089)
            ·
              refine ⟨23231230034017889119814317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30974973378690518826419089 23231230034017889119814317)
              ·
                refine ⟨8711711262756708419930369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23231230034017889119814317 8711711262756708419930369)
                ·
                  refine ⟨6533783447067531314947777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8711711262756708419930369 6533783447067531314947777)
                  ·
                    refine ⟨4900337585300648486210833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6533783447067531314947777 4900337585300648486210833)
                    ·
                      refine ⟨3675253188975486364658125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900337585300648486210833 3675253188975486364658125)
                      ·
                        rfl

theorem cell23_7157530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_7157530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157530 prefixEnd_7157530 := by exact prefixLift 7157530
  have htrace : WordTrace (prefixWord ++ tailWord_7157530) baseStart_7157530 baseEnd_7157530 := by
    simpa [prefixWord, tailWord_7157530, baseEnd_7157530] using wordTrace_append hprefix tailTrace_7157530
  have hstable : (prefixWord ++ tailWord_7157530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157530).length < 2 ^ (prefixWord ++ tailWord_7157530).sum := by decide
  have hdescent : baseEnd_7157530 < baseStart_7157530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157553 : List Nat := [1, 2, 2, 3, 2, 3, 2, 3, 5]
def baseStart_7157553 : Nat := 118140960795 + 7157553 * 2 ^ 59
def prefixEnd_7157553 : Nat := 4983230072969 + 3 ^ 40 * 7157553 * 2
def baseEnd_7157553 : Nat := 408362777670059974963391

theorem tailTrace_7157553 : CollatzResearch.WordTrace tailWord_7157553 prefixEnd_7157553 408362777670059974963391 := by
  unfold tailWord_7157553
  simp only [CollatzResearch.WordTrace]
  refine ⟨261057404638415368576261313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174038269758943579050840875 261057404638415368576261313)
  ·
    refine ⟨195793053478811526432195985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261057404638415368576261313 195793053478811526432195985)
    ·
      refine ⟨146844790109108644824146989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195793053478811526432195985 146844790109108644824146989)
      ·
        refine ⟨55066796290915741809055121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146844790109108644824146989 55066796290915741809055121)
        ·
          refine ⟨41300097218186806356791341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55066796290915741809055121 41300097218186806356791341)
          ·
            refine ⟨15487536456820052383796753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41300097218186806356791341 15487536456820052383796753)
            ·
              refine ⟨11615652342615039287847565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15487536456820052383796753 11615652342615039287847565)
              ·
                refine ⟨4355869628480639732942837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11615652342615039287847565 4355869628480639732942837)
                ·
                  refine ⟨408362777670059974963391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4355869628480639732942837 408362777670059974963391)
                  ·
                    rfl

theorem cell23_7157553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 5].length) (baseStart_7157553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157553 prefixEnd_7157553 := by exact prefixLift 7157553
  have htrace : WordTrace (prefixWord ++ tailWord_7157553) baseStart_7157553 baseEnd_7157553 := by
    simpa [prefixWord, tailWord_7157553, baseEnd_7157553] using wordTrace_append hprefix tailTrace_7157553
  have hstable : (prefixWord ++ tailWord_7157553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157553).length < 2 ^ (prefixWord ++ tailWord_7157553).sum := by decide
  have hdescent : baseEnd_7157553 < baseStart_7157553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157559 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_7157559 : Nat := 118140960795 + 7157559 * 2 ^ 59
def prefixEnd_7157559 : Nat := 4983230072969 + 3 ^ 40 * 7157559 * 2
def baseEnd_7157559 : Nat := 3675268079914466751195491

theorem tailTrace_7157559 : CollatzResearch.WordTrace tailWord_7157559 prefixEnd_7157559 3675268079914466751195491 := by
  unfold tailWord_7157559
  simp only [CollatzResearch.WordTrace]
  refine ⟨261057623476393631600979731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174038415650929087733986487 261057623476393631600979731)
  ·
    refine ⟨391586435214590447401469597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261057623476393631600979731 391586435214590447401469597)
    ·
      refine ⟨146844913205471417775551099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391586435214590447401469597 146844913205471417775551099)
      ·
        refine ⟨220267369808207126663326649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146844913205471417775551099 220267369808207126663326649)
        ·
          refine ⟨165200527356155344997494987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220267369808207126663326649 165200527356155344997494987)
          ·
            refine ⟨247800791034233017496242481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165200527356155344997494987 247800791034233017496242481)
            ·
              refine ⟨185850593275674763122181861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247800791034233017496242481 185850593275674763122181861)
              ·
                refine ⟨34846986239189018085409099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185850593275674763122181861 34846986239189018085409099)
                ·
                  refine ⟨52270479358783527128113649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34846986239189018085409099 52270479358783527128113649)
                  ·
                    refine ⟨39202859519087645346085237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52270479358783527128113649 39202859519087645346085237)
                    ·
                      refine ⟨3675268079914466751195491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39202859519087645346085237 3675268079914466751195491)
                      ·
                        rfl

theorem cell23_7157559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_7157559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157559 prefixEnd_7157559 := by exact prefixLift 7157559
  have htrace : WordTrace (prefixWord ++ tailWord_7157559) baseStart_7157559 baseEnd_7157559 := by
    simpa [prefixWord, tailWord_7157559, baseEnd_7157559] using wordTrace_append hprefix tailTrace_7157559
  have hstable : (prefixWord ++ tailWord_7157559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157559).length < 2 ^ (prefixWord ++ tailWord_7157559).sum := by decide
  have hdescent : baseEnd_7157559 < baseStart_7157559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157586 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_7157586 : Nat := 118140960795 + 7157586 * 2 ^ 59
def prefixEnd_7157586 : Nat := 4983230072969 + 3 ^ 40 * 7157586 * 2
def baseEnd_7157586 : Nat := 3675281943892138145557867

theorem tailTrace_7157586 : CollatzResearch.WordTrace tailWord_7157586 prefixEnd_7157586 3675281943892138145557867 := by
  unfold tailWord_7157586
  simp only [CollatzResearch.WordTrace]
  refine ⟨65264652061823953803053153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174039072164863876808141741 65264652061823953803053153)
  ·
    refine ⟨48948489046367965352289865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65264652061823953803053153 48948489046367965352289865)
    ·
      refine ⟨36711366784775974014217399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48948489046367965352289865 36711366784775974014217399)
      ·
        refine ⟨55067050177163961021326099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36711366784775974014217399 55067050177163961021326099)
        ·
          refine ⟨82600575265745941531989149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55067050177163961021326099 82600575265745941531989149)
          ·
            refine ⟨30975215724654728074495931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82600575265745941531989149 30975215724654728074495931)
            ·
              refine ⟨46462823586982092111743897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30975215724654728074495931 46462823586982092111743897)
              ·
                refine ⟨34847117690236569083807923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46462823586982092111743897 34847117690236569083807923)
                ·
                  refine ⟨52270676535354853625711885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34847117690236569083807923 52270676535354853625711885)
                  ·
                    refine ⟨19601503700758070109641957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52270676535354853625711885 19601503700758070109641957)
                    ·
                      refine ⟨3675281943892138145557867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19601503700758070109641957 3675281943892138145557867)
                      ·
                        rfl

theorem cell23_7157586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_7157586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157586 prefixEnd_7157586 := by exact prefixLift 7157586
  have htrace : WordTrace (prefixWord ++ tailWord_7157586) baseStart_7157586 baseEnd_7157586 := by
    simpa [prefixWord, tailWord_7157586, baseEnd_7157586] using wordTrace_append hprefix tailTrace_7157586
  have hstable : (prefixWord ++ tailWord_7157586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157586).length < 2 ^ (prefixWord ++ tailWord_7157586).sum := by decide
  have hdescent : baseEnd_7157586 < baseStart_7157586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157653 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_7157653 : Nat := 118140960795 + 7157653 * 2 ^ 59
def prefixEnd_7157653 : Nat := 4983230072969 + 3 ^ 40 * 7157653 * 2
def baseEnd_7157653 : Nat := 3675316347095989383420059

theorem tailTrace_7157653 : CollatzResearch.WordTrace tailWord_7157653 prefixEnd_7157653 3675316347095989383420059 := by
  unfold tailWord_7157653
  simp only [CollatzResearch.WordTrace]
  refine ⟨261061051938053085654901613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174040701292035390436601075 261061051938053085654901613)
  ·
    refine ⟨97897894476769907120588105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261061051938053085654901613 97897894476769907120588105)
    ·
      refine ⟨73423420857577430340441079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97897894476769907120588105 73423420857577430340441079)
      ·
        refine ⟨110135131286366145510661619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73423420857577430340441079 110135131286366145510661619)
        ·
          refine ⟨165202696929549218265992429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110135131286366145510661619 165202696929549218265992429)
          ·
            refine ⟨61951011348580956849747161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165202696929549218265992429 61951011348580956849747161)
            ·
              refine ⟨46463258511435717637310371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61951011348580956849747161 46463258511435717637310371)
              ·
                refine ⟨69694887767153576455965557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46463258511435717637310371 69694887767153576455965557)
                ·
                  refine ⟨6533895728170647792746771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69694887767153576455965557 6533895728170647792746771)
                  ·
                    refine ⟨9800843592255971689120157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6533895728170647792746771 9800843592255971689120157)
                    ·
                      refine ⟨3675316347095989383420059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9800843592255971689120157 3675316347095989383420059)
                      ·
                        rfl

theorem cell23_7157653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_7157653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157653 prefixEnd_7157653 := by exact prefixLift 7157653
  have htrace : WordTrace (prefixWord ++ tailWord_7157653) baseStart_7157653 baseEnd_7157653 := by
    simpa [prefixWord, tailWord_7157653, baseEnd_7157653] using wordTrace_append hprefix tailTrace_7157653
  have hstable : (prefixWord ++ tailWord_7157653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157653).length < 2 ^ (prefixWord ++ tailWord_7157653).sum := by decide
  have hdescent : baseEnd_7157653 < baseStart_7157653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157654 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7157654 : Nat := 118140960795 + 7157654 * 2 ^ 59
def prefixEnd_7157654 : Nat := 4983230072969 + 3 ^ 40 * 7157654 * 2
def baseEnd_7157654 : Nat := 3675316860576643879507555

theorem tailTrace_7157654 : CollatzResearch.WordTrace tailWord_7157654 prefixEnd_7157654 3675316860576643879507555 := by
  unfold tailWord_7157654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16316318025690591426605501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174040725607366308550458677 16316318025690591426605501)
  ·
    refine ⟨6118619259633971784977063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16316318025690591426605501 6118619259633971784977063)
    ·
      refine ⟨9177928889450957677465595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6118619259633971784977063 9177928889450957677465595)
      ·
        refine ⟨13766893334176436516198393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9177928889450957677465595 13766893334176436516198393)
        ·
          refine ⟨10325170000632327387148795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13766893334176436516198393 10325170000632327387148795)
          ·
            refine ⟨15487755000948491080723193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325170000632327387148795 15487755000948491080723193)
            ·
              refine ⟨11615816250711368310542395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15487755000948491080723193 11615816250711368310542395)
              ·
                refine ⟨17423724376067052465813593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11615816250711368310542395 17423724376067052465813593)
                ·
                  refine ⟨13067793282050289349360195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17423724376067052465813593 13067793282050289349360195)
                  ·
                    refine ⟨19601689923075434024040293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13067793282050289349360195 19601689923075434024040293)
                    ·
                      refine ⟨3675316860576643879507555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19601689923075434024040293 3675316860576643879507555)
                      ·
                        rfl

theorem cell23_7157654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7157654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157654 prefixEnd_7157654 := by exact prefixLift 7157654
  have htrace : WordTrace (prefixWord ++ tailWord_7157654) baseStart_7157654 baseEnd_7157654 := by
    simpa [prefixWord, tailWord_7157654, baseEnd_7157654] using wordTrace_append hprefix tailTrace_7157654
  have hstable : (prefixWord ++ tailWord_7157654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157654).length < 2 ^ (prefixWord ++ tailWord_7157654).sum := by decide
  have hdescent : baseEnd_7157654 < baseStart_7157654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157676 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_7157676 : Nat := 118140960795 + 7157676 * 2 ^ 59
def prefixEnd_7157676 : Nat := 4983230072969 + 3 ^ 40 * 7157676 * 2
def baseEnd_7157676 : Nat := 3675328157151042793432453

theorem tailTrace_7157676 : CollatzResearch.WordTrace tailWord_7157676 prefixEnd_7157676 3675328157151042793432453 := by
  unfold tailWord_7157676
  simp only [CollatzResearch.WordTrace]
  refine ⟨130530945408484880291494441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174041260544646507055325921 130530945408484880291494441)
  ·
    refine ⟨97898209056363660218620831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130530945408484880291494441 97898209056363660218620831)
    ·
      refine ⟨146847313584545490327931247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97898209056363660218620831 146847313584545490327931247)
      ·
        refine ⟨220270970376818235491896871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146847313584545490327931247 220270970376818235491896871)
        ·
          refine ⟨330406455565227353237845307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220270970376818235491896871 330406455565227353237845307)
          ·
            refine ⟨495609683347841029856767961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330406455565227353237845307 495609683347841029856767961)
            ·
              refine ⟨371707262510880772392575971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495609683347841029856767961 371707262510880772392575971)
              ·
                refine ⟨557560893766321158588863957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371707262510880772392575971 557560893766321158588863957)
                ·
                  refine ⟨13067833447648152154426499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 557560893766321158588863957 13067833447648152154426499)
                  ·
                    refine ⟨19601750171472228231639749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13067833447648152154426499 19601750171472228231639749)
                    ·
                      refine ⟨3675328157151042793432453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19601750171472228231639749 3675328157151042793432453)
                      ·
                        rfl

theorem cell23_7157676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_7157676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157676 prefixEnd_7157676 := by exact prefixLift 7157676
  have htrace : WordTrace (prefixWord ++ tailWord_7157676) baseStart_7157676 baseEnd_7157676 := by
    simpa [prefixWord, tailWord_7157676, baseEnd_7157676] using wordTrace_append hprefix tailTrace_7157676
  have hstable : (prefixWord ++ tailWord_7157676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157676).length < 2 ^ (prefixWord ++ tailWord_7157676).sum := by decide
  have hdescent : baseEnd_7157676 < baseStart_7157676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157693 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_7157693 : Nat := 118140960795 + 7157693 * 2 ^ 59
def prefixEnd_7157693 : Nat := 4983230072969 + 3 ^ 40 * 7157693 * 2
def baseEnd_7157693 : Nat := 3675336886322169226919875

theorem tailTrace_7157693 : CollatzResearch.WordTrace tailWord_7157693 prefixEnd_7157693 3675336886322169226919875 := by
  unfold tailWord_7157693
  simp only [CollatzResearch.WordTrace]
  refine ⟨261062510857908172486357733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174041673905272114990905155 261062510857908172486357733)
  ·
    refine ⟨48949220785857782341192075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261062510857908172486357733 48949220785857782341192075)
    ·
      refine ⟨73423831178786673511788113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48949220785857782341192075 73423831178786673511788113)
      ·
        refine ⟨55067873384090005133841085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73423831178786673511788113 55067873384090005133841085)
        ·
          refine ⟨20650452519033751925190407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55067873384090005133841085 20650452519033751925190407)
          ·
            refine ⟨30975678778550627887785611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20650452519033751925190407 30975678778550627887785611)
            ·
              refine ⟨46463518167825941831678417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30975678778550627887785611 46463518167825941831678417)
              ·
                refine ⟨34847638625869456373758813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46463518167825941831678417 34847638625869456373758813)
                ·
                  refine ⟨13067864484701046140159555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34847638625869456373758813 13067864484701046140159555)
                  ·
                    refine ⟨19601796727051569210239333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13067864484701046140159555 19601796727051569210239333)
                    ·
                      refine ⟨3675336886322169226919875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19601796727051569210239333 3675336886322169226919875)
                      ·
                        rfl

theorem cell23_7157693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_7157693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157693 prefixEnd_7157693 := by exact prefixLift 7157693
  have htrace : WordTrace (prefixWord ++ tailWord_7157693) baseStart_7157693 baseEnd_7157693 := by
    simpa [prefixWord, tailWord_7157693, baseEnd_7157693] using wordTrace_append hprefix tailTrace_7157693
  have hstable : (prefixWord ++ tailWord_7157693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157693).length < 2 ^ (prefixWord ++ tailWord_7157693).sum := by decide
  have hdescent : baseEnd_7157693 < baseStart_7157693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157696 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_7157696 : Nat := 118140960795 + 7157696 * 2 ^ 59
def prefixEnd_7157696 : Nat := 4983230072969 + 3 ^ 40 * 7157696 * 2
def baseEnd_7157696 : Nat := 3675338426764132715182361

theorem tailTrace_7157696 : CollatzResearch.WordTrace tailWord_7157696 prefixEnd_7157696 3675338426764132715182361 := by
  unfold tailWord_7157696
  simp only [CollatzResearch.WordTrace]
  refine ⟨130531310138448651999358471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174041746851264869332477961 130531310138448651999358471)
  ·
    refine ⟨195796965207672977999037707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130531310138448651999358471 195796965207672977999037707)
    ·
      refine ⟨293695447811509466998556561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195796965207672977999037707 293695447811509466998556561)
      ·
        refine ⟨220271585858632100248917421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293695447811509466998556561 220271585858632100248917421)
        ·
          refine ⟨82601844696987037593344033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220271585858632100248917421 82601844696987037593344033)
          ·
            refine ⟨61951383522740278195008025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82601844696987037593344033 61951383522740278195008025)
            ·
              refine ⟨46463537642055208646256019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61951383522740278195008025 46463537642055208646256019)
              ·
                refine ⟨69695306463082812969384029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46463537642055208646256019 69695306463082812969384029)
                ·
                  refine ⟨26135739923656054863519011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69695306463082812969384029 26135739923656054863519011)
                  ·
                    refine ⟨39203609885484082295278517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26135739923656054863519011 39203609885484082295278517)
                    ·
                      refine ⟨3675338426764132715182361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39203609885484082295278517 3675338426764132715182361)
                      ·
                        rfl

theorem cell23_7157696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_7157696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157696 prefixEnd_7157696 := by exact prefixLift 7157696
  have htrace : WordTrace (prefixWord ++ tailWord_7157696) baseStart_7157696 baseEnd_7157696 := by
    simpa [prefixWord, tailWord_7157696, baseEnd_7157696] using wordTrace_append hprefix tailTrace_7157696
  have hstable : (prefixWord ++ tailWord_7157696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157696).length < 2 ^ (prefixWord ++ tailWord_7157696).sum := by decide
  have hdescent : baseEnd_7157696 < baseStart_7157696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157706 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_7157706 : Nat := 118140960795 + 7157706 * 2 ^ 59
def prefixEnd_7157706 : Nat := 4983230072969 + 3 ^ 40 * 7157706 * 2
def baseEnd_7157706 : Nat := 3675343561570677676057315

theorem tailTrace_7157706 : CollatzResearch.WordTrace tailWord_7157706 prefixEnd_7157706 3675343561570677676057315 := by
  unfold tailWord_7157706
  simp only [CollatzResearch.WordTrace]
  refine ⟨65265746251715268926645243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174041990004574050471053981 65265746251715268926645243)
  ·
    refine ⟨97898619377572903389967865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65265746251715268926645243 97898619377572903389967865)
    ·
      refine ⟨73423964533179677542475899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97898619377572903389967865 73423964533179677542475899)
      ·
        refine ⟨110135946799769516313713849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73423964533179677542475899 110135946799769516313713849)
        ·
          refine ⟨82601960099827137235285387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110135946799769516313713849 82601960099827137235285387)
          ·
            refine ⟨123902940149740705852928081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82601960099827137235285387 123902940149740705852928081)
            ·
              refine ⟨92927205112305529389696061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123902940149740705852928081 92927205112305529389696061)
              ·
                refine ⟨34847701917114573521136023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92927205112305529389696061 34847701917114573521136023)
                ·
                  refine ⟨52271552875671860281704035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34847701917114573521136023 52271552875671860281704035)
                  ·
                    refine ⟨78407329313507790422556053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52271552875671860281704035 78407329313507790422556053)
                    ·
                      refine ⟨3675343561570677676057315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78407329313507790422556053 3675343561570677676057315)
                      ·
                        rfl

theorem cell23_7157706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_7157706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157706 prefixEnd_7157706 := by exact prefixLift 7157706
  have htrace : WordTrace (prefixWord ++ tailWord_7157706) baseStart_7157706 baseEnd_7157706 := by
    simpa [prefixWord, tailWord_7157706, baseEnd_7157706] using wordTrace_append hprefix tailTrace_7157706
  have hstable : (prefixWord ++ tailWord_7157706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157706).length < 2 ^ (prefixWord ++ tailWord_7157706).sum := by decide
  have hdescent : baseEnd_7157706 < baseStart_7157706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157714 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_7157714 : Nat := 118140960795 + 7157714 * 2 ^ 59
def prefixEnd_7157714 : Nat := 4983230072969 + 3 ^ 40 * 7157714 * 2
def baseEnd_7157714 : Nat := 3675347669415913644757279

theorem tailTrace_7157714 : CollatzResearch.WordTrace tailWord_7157714 prefixEnd_7157714 3675347669415913644757279 := by
  unfold tailWord_7157714
  simp only [CollatzResearch.WordTrace]
  refine ⟨65265819197708023268218049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174042184527221395381914797 65265819197708023268218049)
  ·
    refine ⟨48949364398281017451163537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65265819197708023268218049 48949364398281017451163537)
    ·
      refine ⟨36712023298710763088372653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48949364398281017451163537 36712023298710763088372653)
      ·
        refine ⟨13767008737016536158139745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36712023298710763088372653 13767008737016536158139745)
        ·
          refine ⟨10325256552762402118604809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13767008737016536158139745 10325256552762402118604809)
          ·
            refine ⟨7743942414571801588953607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10325256552762402118604809 7743942414571801588953607)
            ·
              refine ⟨11615913621857702383430411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743942414571801588953607 11615913621857702383430411)
              ·
                refine ⟨17423870432786553575145617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11615913621857702383430411 17423870432786553575145617)
                ·
                  refine ⟨13067902824589915181359213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17423870432786553575145617 13067902824589915181359213)
                  ·
                    refine ⟨4900463559221218193009705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13067902824589915181359213 4900463559221218193009705)
                    ·
                      refine ⟨3675347669415913644757279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900463559221218193009705 3675347669415913644757279)
                      ·
                        rfl

theorem cell23_7157714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_7157714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157714 prefixEnd_7157714 := by exact prefixLift 7157714
  have htrace : WordTrace (prefixWord ++ tailWord_7157714) baseStart_7157714 baseEnd_7157714 := by
    simpa [prefixWord, tailWord_7157714, baseEnd_7157714] using wordTrace_append hprefix tailTrace_7157714
  have hstable : (prefixWord ++ tailWord_7157714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157714).length < 2 ^ (prefixWord ++ tailWord_7157714).sum := by decide
  have hdescent : baseEnd_7157714 < baseStart_7157714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157724 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7157724 : Nat := 118140960795 + 7157724 * 2 ^ 59
def prefixEnd_7157724 : Nat := 4983230072969 + 3 ^ 40 * 7157724 * 2
def baseEnd_7157724 : Nat := 1225117601407486201877411

theorem tailTrace_7157724 : CollatzResearch.WordTrace tailWord_7157724 prefixEnd_7157724 1225117601407486201877411 := by
  unfold tailWord_7157724
  simp only [CollatzResearch.WordTrace]
  refine ⟨130531820760397932390368113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174042427680530576520490817 130531820760397932390368113)
  ·
    refine ⟨97898865570298449292776085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130531820760397932390368113 97898865570298449292776085)
    ·
      refine ⟨4589009323607739810598879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97898865570298449292776085 4589009323607739810598879)
      ·
        refine ⟨6883513985411609715898319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4589009323607739810598879 6883513985411609715898319)
        ·
          refine ⟨10325270978117414573847479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883513985411609715898319 10325270978117414573847479)
          ·
            refine ⟨15487906467176121860771219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325270978117414573847479 15487906467176121860771219)
            ·
              refine ⟨23231859700764182791156829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15487906467176121860771219 23231859700764182791156829)
              ·
                refine ⟨8711947387786568546683811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23231859700764182791156829 8711947387786568546683811)
                ·
                  refine ⟨13067921081679852820025717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711947387786568546683811 13067921081679852820025717)
                  ·
                    refine ⟨1225117601407486201877411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13067921081679852820025717 1225117601407486201877411)
                    ·
                      rfl

theorem cell23_7157724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7157724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157724 prefixEnd_7157724 := by exact prefixLift 7157724
  have htrace : WordTrace (prefixWord ++ tailWord_7157724) baseStart_7157724 baseEnd_7157724 := by
    simpa [prefixWord, tailWord_7157724, baseEnd_7157724] using wordTrace_append hprefix tailTrace_7157724
  have hstable : (prefixWord ++ tailWord_7157724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157724).length < 2 ^ (prefixWord ++ tailWord_7157724).sum := by decide
  have hdescent : baseEnd_7157724 < baseStart_7157724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157727 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 1, 1, 4]
def baseStart_7157727 : Nat := 118140960795 + 7157727 * 2 ^ 59
def prefixEnd_7157727 : Nat := 4983230072969 + 3 ^ 40 * 7157727 * 2
def baseEnd_7157727 : Nat := 3675354344664422093894719

theorem tailTrace_7157727 : CollatzResearch.WordTrace tailWord_7157727 prefixEnd_7157727 3675354344664422093894719 := by
  unfold tailWord_7157727
  simp only [CollatzResearch.WordTrace]
  refine ⟨261063750939784996293095435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174042500626523330862063623 261063750939784996293095435)
  ·
    refine ⟨391595626409677494439643153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261063750939784996293095435 391595626409677494439643153)
    ·
      refine ⟨293696719807258120829732365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391595626409677494439643153 293696719807258120829732365)
      ·
        refine ⟨110136269927721795311149637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293696719807258120829732365 110136269927721795311149637)
        ·
          refine ⟨20650550611447836620840557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110136269927721795311149637 20650550611447836620840557)
          ·
            refine ⟨7743956479292938732815209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20650550611447836620840557 7743956479292938732815209)
            ·
              refine ⟨5807967359469704049611407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7743956479292938732815209 5807967359469704049611407)
              ·
                refine ⟨8711951039204556074417111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807967359469704049611407 8711951039204556074417111)
                ·
                  refine ⟨13067926558806834111625667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711951039204556074417111 13067926558806834111625667)
                  ·
                    refine ⟨19601889838210251167438501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13067926558806834111625667 19601889838210251167438501)
                    ·
                      refine ⟨3675354344664422093894719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19601889838210251167438501 3675354344664422093894719)
                      ·
                        rfl

theorem cell23_7157727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_7157727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157727 prefixEnd_7157727 := by exact prefixLift 7157727
  have htrace : WordTrace (prefixWord ++ tailWord_7157727) baseStart_7157727 baseEnd_7157727 := by
    simpa [prefixWord, tailWord_7157727, baseEnd_7157727] using wordTrace_append hprefix tailTrace_7157727
  have hstable : (prefixWord ++ tailWord_7157727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157727).length < 2 ^ (prefixWord ++ tailWord_7157727).sum := by decide
  have hdescent : baseEnd_7157727 < baseStart_7157727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157736 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7157736 : Nat := 118140960795 + 7157736 * 2 ^ 59
def prefixEnd_7157736 : Nat := 4983230072969 + 3 ^ 40 * 7157736 * 2
def baseEnd_7157736 : Nat := 3675358965990312558682177

theorem tailTrace_7157736 : CollatzResearch.WordTrace tailWord_7157736 prefixEnd_7157736 3675358965990312558682177 := by
  unfold tailWord_7157736
  simp only [CollatzResearch.WordTrace]
  refine ⟨130532039598376195415086531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174042719464501593886782041 130532039598376195415086531)
  ·
    refine ⟨195798059397564293122629797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130532039598376195415086531 195798059397564293122629797)
    ·
      refine ⟨36712136137043304960493087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195798059397564293122629797 36712136137043304960493087)
      ·
        refine ⟨55068204205564957440739631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36712136137043304960493087 55068204205564957440739631)
        ·
          refine ⟨82602306308347436161109447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55068204205564957440739631 82602306308347436161109447)
          ·
            refine ⟨123903459462521154241664171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82602306308347436161109447 123903459462521154241664171)
            ·
              refine ⟨185855189193781731362496257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123903459462521154241664171 185855189193781731362496257)
              ·
                refine ⟨139391391895336298521872193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185855189193781731362496257 139391391895336298521872193)
                ·
                  refine ⟨104543543921502223891404145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139391391895336298521872193 104543543921502223891404145)
                  ·
                    refine ⟨78407657941126667918553109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104543543921502223891404145 78407657941126667918553109)
                    ·
                      refine ⟨3675358965990312558682177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78407657941126667918553109 3675358965990312558682177)
                      ·
                        rfl

theorem cell23_7157736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7157736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157736 prefixEnd_7157736 := by exact prefixLift 7157736
  have htrace : WordTrace (prefixWord ++ tailWord_7157736) baseStart_7157736 baseEnd_7157736 := by
    simpa [prefixWord, tailWord_7157736, baseEnd_7157736] using wordTrace_append hprefix tailTrace_7157736
  have hstable : (prefixWord ++ tailWord_7157736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157736).length < 2 ^ (prefixWord ++ tailWord_7157736).sum := by decide
  have hdescent : baseEnd_7157736 < baseStart_7157736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157764 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7157764 : Nat := 118140960795 + 7157764 * 2 ^ 59
def prefixEnd_7157764 : Nat := 4983230072969 + 3 ^ 40 * 7157764 * 2
def baseEnd_7157764 : Nat := 3675373343448638449132049

theorem tailTrace_7157764 : CollatzResearch.WordTrace tailWord_7157764 prefixEnd_7157764 3675373343448638449132049 := by
  unfold tailWord_7157764
  simp only [CollatzResearch.WordTrace]
  refine ⟨130532550220325475806096173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174043400293767301074794897 130532550220325475806096173)
  ·
    refine ⟨48949706332622053427286065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130532550220325475806096173 48949706332622053427286065)
    ·
      refine ⟨36712279749466540070464549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48949706332622053427286065 36712279749466540070464549)
      ·
        refine ⟨6883552453024976263212103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36712279749466540070464549 6883552453024976263212103)
        ·
          refine ⟨10325328679537464394818155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883552453024976263212103 10325328679537464394818155)
          ·
            refine ⟨15487993019306196592227233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325328679537464394818155 15487993019306196592227233)
            ·
              refine ⟨11615994764479647444170425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15487993019306196592227233 11615994764479647444170425)
              ·
                refine ⟨8711996073359735583127819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11615994764479647444170425 8711996073359735583127819)
                ·
                  refine ⟨13067994110039603374691729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711996073359735583127819 13067994110039603374691729)
                  ·
                    refine ⟨9800995582529702531018797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13067994110039603374691729 9800995582529702531018797)
                    ·
                      refine ⟨3675373343448638449132049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9800995582529702531018797 3675373343448638449132049)
                      ·
                        rfl

theorem cell23_7157764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7157764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157764 prefixEnd_7157764 := by exact prefixLift 7157764
  have htrace : WordTrace (prefixWord ++ tailWord_7157764) baseStart_7157764 baseEnd_7157764 := by
    simpa [prefixWord, tailWord_7157764, baseEnd_7157764] using wordTrace_append hprefix tailTrace_7157764
  have hstable : (prefixWord ++ tailWord_7157764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157764).length < 2 ^ (prefixWord ++ tailWord_7157764).sum := by decide
  have hdescent : baseEnd_7157764 < baseStart_7157764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157813 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_7157813 : Nat := 118140960795 + 7157813 * 2 ^ 59
def prefixEnd_7157813 : Nat := 4983230072969 + 3 ^ 40 * 7157813 * 2
def baseEnd_7157813 : Nat := 3675398504000708757419323

theorem tailTrace_7157813 : CollatzResearch.WordTrace tailWord_7157813 prefixEnd_7157813 3675398504000708757419323 := by
  unfold tailWord_7157813
  simp only [CollatzResearch.WordTrace]
  refine ⟨261066887617473432980726093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174044591744982288653817395 261066887617473432980726093)
  ·
    refine ⟨97900082856552537367772285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261066887617473432980726093 97900082856552537367772285)
    ·
      refine ⟨36712531071207201512914607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97900082856552537367772285 36712531071207201512914607)
      ·
        refine ⟨55068796606810802269371911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36712531071207201512914607 55068796606810802269371911)
        ·
          refine ⟨82603194910216203404057867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55068796606810802269371911 82603194910216203404057867)
          ·
            refine ⟨123904792365324305106086801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82603194910216203404057867 123904792365324305106086801)
            ·
              refine ⟨92928594273993228829565101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123904792365324305106086801 92928594273993228829565101)
              ·
                refine ⟨34848222852747460811086913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92928594273993228829565101 34848222852747460811086913)
                ·
                  refine ⟨26136167139560595608315185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34848222852747460811086913 26136167139560595608315185)
                  ·
                    refine ⟨19602125354670446706236389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26136167139560595608315185 19602125354670446706236389)
                    ·
                      refine ⟨3675398504000708757419323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19602125354670446706236389 3675398504000708757419323)
                      ·
                        rfl

theorem cell23_7157813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_7157813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157813 prefixEnd_7157813 := by exact prefixLift 7157813
  have htrace : WordTrace (prefixWord ++ tailWord_7157813) baseStart_7157813 baseEnd_7157813 := by
    simpa [prefixWord, tailWord_7157813, baseEnd_7157813] using wordTrace_append hprefix tailTrace_7157813
  have hstable : (prefixWord ++ tailWord_7157813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157813).length < 2 ^ (prefixWord ++ tailWord_7157813).sum := by decide
  have hdescent : baseEnd_7157813 < baseStart_7157813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157860 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 2, 5, 2]
def baseStart_7157860 : Nat := 118140960795 + 7157860 * 2 ^ 59
def prefixEnd_7157860 : Nat := 4983230072969 + 3 ^ 40 * 7157860 * 2
def baseEnd_7157860 : Nat := 3675422637591470073531607

theorem tailTrace_7157860 : CollatzResearch.WordTrace tailWord_7157860 prefixEnd_7157860 3675422637591470073531607 := by
  unfold tailWord_7157860
  simp only [CollatzResearch.WordTrace]
  refine ⟨130534300924151580003843517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174045734565535440005124689 130534300924151580003843517)
  ·
    refine ⟨48950362846556842501441319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130534300924151580003843517 48950362846556842501441319)
    ·
      refine ⟨73425544269835263752161979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48950362846556842501441319 73425544269835263752161979)
      ·
        refine ⟨110138316404752895628242969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73425544269835263752161979 110138316404752895628242969)
        ·
          refine ⟨82603737303564671721182227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110138316404752895628242969 82603737303564671721182227)
          ·
            refine ⟨123905605955347007581773341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82603737303564671721182227 123905605955347007581773341)
            ·
              refine ⟨46464602233255127843165003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123905605955347007581773341 46464602233255127843165003)
              ·
                refine ⟨69696903349882691764747505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46464602233255127843165003 69696903349882691764747505)
                ·
                  refine ⟨52272677512412018823560629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69696903349882691764747505 52272677512412018823560629)
                  ·
                    refine ⟨4900563516788626764708809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52272677512412018823560629 4900563516788626764708809)
                    ·
                      refine ⟨3675422637591470073531607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900563516788626764708809 3675422637591470073531607)
                      ·
                        rfl

theorem cell23_7157860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_7157860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157860 prefixEnd_7157860 := by exact prefixLift 7157860
  have htrace : WordTrace (prefixWord ++ tailWord_7157860) baseStart_7157860 baseEnd_7157860 := by
    simpa [prefixWord, tailWord_7157860, baseEnd_7157860] using wordTrace_append hprefix tailTrace_7157860
  have hstable : (prefixWord ++ tailWord_7157860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157860).length < 2 ^ (prefixWord ++ tailWord_7157860).sum := by decide
  have hdescent : baseEnd_7157860 < baseStart_7157860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157863 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_7157863 : Nat := 118140960795 + 7157863 * 2 ^ 59
def prefixEnd_7157863 : Nat := 4983230072969 + 3 ^ 40 * 7157863 * 2
def baseEnd_7157863 : Nat := 3675424178033433561794093

theorem tailTrace_7157863 : CollatzResearch.WordTrace tailWord_7157863 prefixEnd_7157863 3675424178033433561794093 := by
  unfold tailWord_7157863
  simp only [CollatzResearch.WordTrace]
  refine ⟨261068711267292291520046243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174045807511528194346697495 261068711267292291520046243)
  ·
    refine ⟨391603066900938437280069365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261068711267292291520046243 391603066900938437280069365)
    ·
      refine ⟨36712787521962978495006503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391603066900938437280069365 36712787521962978495006503)
      ·
        refine ⟨55069181282944467742509755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36712787521962978495006503 55069181282944467742509755)
        ·
          refine ⟨82603771924416701613764633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55069181282944467742509755 82603771924416701613764633)
          ·
            refine ⟨61952828943312526210323475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82603771924416701613764633 61952828943312526210323475)
            ·
              refine ⟨92929243414968789315485213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61952828943312526210323475 92929243414968789315485213)
              ·
                refine ⟨34848466280613295993306955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92929243414968789315485213 34848466280613295993306955)
                ·
                  refine ⟨52272699420919943989960433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34848466280613295993306955 52272699420919943989960433)
                  ·
                    refine ⟨39204524565689957992470325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52272699420919943989960433 39204524565689957992470325)
                    ·
                      refine ⟨3675424178033433561794093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39204524565689957992470325 3675424178033433561794093)
                      ·
                        rfl

theorem cell23_7157863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_7157863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157863 prefixEnd_7157863 := by exact prefixLift 7157863
  have htrace : WordTrace (prefixWord ++ tailWord_7157863) baseStart_7157863 baseEnd_7157863 := by
    simpa [prefixWord, tailWord_7157863, baseEnd_7157863] using wordTrace_append hprefix tailTrace_7157863
  have hstable : (prefixWord ++ tailWord_7157863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157863).length < 2 ^ (prefixWord ++ tailWord_7157863).sum := by decide
  have hdescent : baseEnd_7157863 < baseStart_7157863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157873 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_7157873 : Nat := 118140960795 + 7157873 * 2 ^ 59
def prefixEnd_7157873 : Nat := 4983230072969 + 3 ^ 40 * 7157873 * 2
def baseEnd_7157873 : Nat := 3675429312839978522669047

theorem tailTrace_7157873 : CollatzResearch.WordTrace tailWord_7157873 prefixEnd_7157873 3675429312839978522669047 := by
  unfold tailWord_7157873
  simp only [CollatzResearch.WordTrace]
  refine ⟨261069075997256063227910273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174046050664837375485273515 261069075997256063227910273)
  ·
    refine ⟨195801806997942047420932705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261069075997256063227910273 195801806997942047420932705)
    ·
      refine ⟨146851355248456535565699529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195801806997942047420932705 146851355248456535565699529)
      ·
        refine ⟨110138516436342401674274647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146851355248456535565699529 110138516436342401674274647)
        ·
          refine ⟨165207774654513602511411971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110138516436342401674274647 165207774654513602511411971)
          ·
            refine ⟨247811661981770403767117957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165207774654513602511411971 247811661981770403767117957)
            ·
              refine ⟨46464686621581950706334617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247811661981770403767117957 46464686621581950706334617)
              ·
                refine ⟨34848514966186463029750963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46464686621581950706334617 34848514966186463029750963)
                ·
                  refine ⟨52272772449279694544626445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34848514966186463029750963 52272772449279694544626445)
                  ·
                    refine ⟨19602289668479885454234917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52272772449279694544626445 19602289668479885454234917)
                    ·
                      refine ⟨3675429312839978522669047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19602289668479885454234917 3675429312839978522669047)
                      ·
                        rfl

theorem cell23_7157873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_7157873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157873 prefixEnd_7157873 := by exact prefixLift 7157873
  have htrace : WordTrace (prefixWord ++ tailWord_7157873) baseStart_7157873 baseEnd_7157873 := by
    simpa [prefixWord, tailWord_7157873, baseEnd_7157873] using wordTrace_append hprefix tailTrace_7157873
  have hstable : (prefixWord ++ tailWord_7157873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157873).length < 2 ^ (prefixWord ++ tailWord_7157873).sum := by decide
  have hdescent : baseEnd_7157873 < baseStart_7157873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157917 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_7157917 : Nat := 118140960795 + 7157917 * 2 ^ 59
def prefixEnd_7157917 : Nat := 4983230072969 + 3 ^ 40 * 7157917 * 2
def baseEnd_7157917 : Nat := 1225150635329592116839615

theorem tailTrace_7157917 : CollatzResearch.WordTrace tailWord_7157917 prefixEnd_7157917 1225150635329592116839615 := by
  unfold tailWord_7157917
  simp only [CollatzResearch.WordTrace]
  refine ⟨261070680809096658742512005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174047120539397772495008003 261070680809096658742512005)
  ·
    refine ⟨48950752651705623514221001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261070680809096658742512005 48950752651705623514221001)
    ·
      refine ⟨36713064488779217635665751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48950752651705623514221001 36713064488779217635665751)
      ·
        refine ⟨55069596733168826453498627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36713064488779217635665751 55069596733168826453498627)
        ·
          refine ⟨82604395099753239680247941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55069596733168826453498627 82604395099753239680247941)
          ·
            refine ⟨15488324081203732440046489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82604395099753239680247941 15488324081203732440046489)
            ·
              refine ⟨11616243060902799330034867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15488324081203732440046489 11616243060902799330034867)
              ·
                refine ⟨17424364591354198995052301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11616243060902799330034867 17424364591354198995052301)
                ·
                  refine ⟨6534136721757824623144613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17424364591354198995052301 6534136721757824623144613)
                  ·
                    refine ⟨1225150635329592116839615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6534136721757824623144613 1225150635329592116839615)
                    ·
                      rfl

theorem cell23_7157917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_7157917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157917 prefixEnd_7157917 := by exact prefixLift 7157917
  have htrace : WordTrace (prefixWord ++ tailWord_7157917) baseStart_7157917 baseEnd_7157917 := by
    simpa [prefixWord, tailWord_7157917, baseEnd_7157917] using wordTrace_append hprefix tailTrace_7157917
  have hstable : (prefixWord ++ tailWord_7157917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157917).length < 2 ^ (prefixWord ++ tailWord_7157917).sum := by decide
  have hdescent : baseEnd_7157917 < baseStart_7157917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7157967 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 2, 3, 2]
def baseStart_7157967 : Nat := 118140960795 + 7157967 * 2 ^ 59
def prefixEnd_7157967 : Nat := 4983230072969 + 3 ^ 40 * 7157967 * 2
def baseEnd_7157967 : Nat := 3675477580021501154893615

theorem tailTrace_7157967 : CollatzResearch.WordTrace tailWord_7157967 prefixEnd_7157967 3675477580021501154893615 := by
  unfold tailWord_7157967
  simp only [CollatzResearch.WordTrace]
  refine ⟨261072504458915517281832155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174048336305943678187888103 261072504458915517281832155)
  ·
    refine ⟨391608756688373275922748233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261072504458915517281832155 391608756688373275922748233)
    ·
      refine ⟨293706567516279956942061175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391608756688373275922748233 293706567516279956942061175)
      ·
        refine ⟨440559851274419935413091763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293706567516279956942061175 440559851274419935413091763)
        ·
          refine ⟨660839776911629903119637645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440559851274419935413091763 660839776911629903119637645)
          ·
            refine ⟨247814916341861213669864117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 660839776911629903119637645 247814916341861213669864117)
            ·
              refine ⟨23232648407049488781549761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247814916341861213669864117 23232648407049488781549761)
              ·
                refine ⟨17424486305287116586162321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23232648407049488781549761 17424486305287116586162321)
                ·
                  refine ⟨13068364728965337439621741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17424486305287116586162321 13068364728965337439621741)
                  ·
                    refine ⟨4900636773362001539858153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13068364728965337439621741 4900636773362001539858153)
                    ·
                      refine ⟨3675477580021501154893615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900636773362001539858153 3675477580021501154893615)
                      ·
                        rfl

theorem cell23_7157967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 3, 2].length) (baseStart_7157967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7157967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7157967 prefixEnd_7157967 := by exact prefixLift 7157967
  have htrace : WordTrace (prefixWord ++ tailWord_7157967) baseStart_7157967 baseEnd_7157967 := by
    simpa [prefixWord, tailWord_7157967, baseEnd_7157967] using wordTrace_append hprefix tailTrace_7157967
  have hstable : (prefixWord ++ tailWord_7157967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7157967).length < 2 ^ (prefixWord ++ tailWord_7157967).sum := by decide
  have hdescent : baseEnd_7157967 < baseStart_7157967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7157967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158003 : List Nat := [1, 1, 1, 2, 2, 4, 1, 11]
def baseStart_7158003 : Nat := 118140960795 + 7158003 * 2 ^ 59
def prefixEnd_7158003 : Nat := 4983230072969 + 3 ^ 40 * 7158003 * 2
def baseEnd_7158003 : Nat := 136129483900928259779387

theorem tailTrace_7158003 : CollatzResearch.WordTrace tailWord_7158003 prefixEnd_7158003 136129483900928259779387 := by
  unfold tailWord_7158003
  simp only [CollatzResearch.WordTrace]
  refine ⟨261073817486785095430142663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174049211657856730286761775 261073817486785095430142663)
  ·
    refine ⟨391610726230177643145213995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261073817486785095430142663 391610726230177643145213995)
    ·
      refine ⟨587416089345266464717820993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391610726230177643145213995 587416089345266464717820993)
      ·
        refine ⟨440562067008949848538365745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587416089345266464717820993 440562067008949848538365745)
        ·
          refine ⟨330421550256712386403774309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440562067008949848538365745 330421550256712386403774309)
          ·
            refine ⟨61954040673133572450707683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330421550256712386403774309 61954040673133572450707683)
            ·
              refine ⟨92931061009700358676061525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61954040673133572450707683 92931061009700358676061525)
              ·
                refine ⟨136129483900928259779387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 92931061009700358676061525 136129483900928259779387)
                ·
                  rfl

theorem cell23_7158003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 11].length) (baseStart_7158003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158003 prefixEnd_7158003 := by exact prefixLift 7158003
  have htrace : WordTrace (prefixWord ++ tailWord_7158003) baseStart_7158003 baseEnd_7158003 := by
    simpa [prefixWord, tailWord_7158003, baseEnd_7158003] using wordTrace_append hprefix tailTrace_7158003
  have hstable : (prefixWord ++ tailWord_7158003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158003).length < 2 ^ (prefixWord ++ tailWord_7158003).sum := by decide
  have hdescent : baseEnd_7158003 < baseStart_7158003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158010 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_7158010 : Nat := 118140960795 + 7158010 * 2 ^ 59
def prefixEnd_7158010 : Nat := 4983230072969 + 3 ^ 40 * 7158010 * 2
def baseEnd_7158010 : Nat := 3675499659689644486655917

theorem tailTrace_7158010 : CollatzResearch.WordTrace tailWord_7158010 prefixEnd_7158010 3675499659689644486655917 := by
  unfold tailWord_7158010
  simp only [CollatzResearch.WordTrace]
  refine ⟨65268518199439933906411871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174049381865173157083764989 65268518199439933906411871)
  ·
    refine ⟨97902777299159900859617807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65268518199439933906411871 97902777299159900859617807)
    ·
      refine ⟨146854165948739851289426711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97902777299159900859617807 146854165948739851289426711)
      ·
        refine ⟨220281248923109776934140067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146854165948739851289426711 220281248923109776934140067)
        ·
          refine ⟨330421873384664665401210101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220281248923109776934140067 330421873384664665401210101)
          ·
            refine ⟨30977050629812312381363447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 330421873384664665401210101 30977050629812312381363447)
            ·
              refine ⟨46465575944718468572045171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30977050629812312381363447 46465575944718468572045171)
              ·
                refine ⟨69698363917077702858067757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46465575944718468572045171 69698363917077702858067757)
                ·
                  refine ⟨26136886468904138571775409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69698363917077702858067757 26136886468904138571775409)
                  ·
                    refine ⟨19602664851678103928831557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26136886468904138571775409 19602664851678103928831557)
                    ·
                      refine ⟨3675499659689644486655917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19602664851678103928831557 3675499659689644486655917)
                      ·
                        rfl

theorem cell23_7158010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_7158010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158010 prefixEnd_7158010 := by exact prefixLift 7158010
  have htrace : WordTrace (prefixWord ++ tailWord_7158010) baseStart_7158010 baseEnd_7158010 := by
    simpa [prefixWord, tailWord_7158010, baseEnd_7158010] using wordTrace_append hprefix tailTrace_7158010
  have hstable : (prefixWord ++ tailWord_7158010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158010).length < 2 ^ (prefixWord ++ tailWord_7158010).sum := by decide
  have hdescent : baseEnd_7158010 < baseStart_7158010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158020 : List Nat := [2, 3, 2, 2, 3, 11]
def baseStart_7158020 : Nat := 118140960795 + 7158020 * 2 ^ 59
def prefixEnd_7158020 : Nat := 4983230072969 + 3 ^ 40 * 7158020 * 2
def baseEnd_7158020 : Nat := 15125534133729174681197

theorem tailTrace_7158020 : CollatzResearch.WordTrace tailWord_7158020 prefixEnd_7158020 15125534133729174681197 := by
  unfold tailWord_7158020
  simp only [CollatzResearch.WordTrace]
  refine ⟨130537218763861753666755757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174049625018482338222341009 130537218763861753666755757)
  ·
    refine ⟨48951457036448157625033409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130537218763861753666755757 48951457036448157625033409)
    ·
      refine ⟨36713592777336118218775057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48951457036448157625033409 36713592777336118218775057)
      ·
        refine ⟨27535194583002088664081293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36713592777336118218775057 27535194583002088664081293)
        ·
          refine ⟨10325697968625783249030485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27535194583002088664081293 10325697968625783249030485)
          ·
            refine ⟨15125534133729174681197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10325697968625783249030485 15125534133729174681197)
            ·
              rfl

theorem cell23_7158020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 11].length) (baseStart_7158020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158020 prefixEnd_7158020 := by exact prefixLift 7158020
  have htrace : WordTrace (prefixWord ++ tailWord_7158020) baseStart_7158020 baseEnd_7158020 := by
    simpa [prefixWord, tailWord_7158020, baseEnd_7158020] using wordTrace_append hprefix tailTrace_7158020
  have hstable : (prefixWord ++ tailWord_7158020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158020).length < 2 ^ (prefixWord ++ tailWord_7158020).sum := by decide
  have hdescent : baseEnd_7158020 < baseStart_7158020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158024 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 2, 4]
def baseStart_7158024 : Nat := 118140960795 + 7158024 * 2 ^ 59
def prefixEnd_7158024 : Nat := 4983230072969 + 3 ^ 40 * 7158024 * 2
def baseEnd_7158024 : Nat := 1225168949472935810626951

theorem tailTrace_7158024 : CollatzResearch.WordTrace tailWord_7158024 prefixEnd_7158024 1225168949472935810626951 := by
  unfold tailWord_7158024
  simp only [CollatzResearch.WordTrace]
  refine ⟨130537291709854508008328563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174049722279806010677771417 130537291709854508008328563)
  ·
    refine ⟨195805937564781762012492845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130537291709854508008328563 195805937564781762012492845)
    ·
      refine ⟨73427226586793160754684817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195805937564781762012492845 73427226586793160754684817)
      ·
        refine ⟨55070419940094870566013613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73427226586793160754684817 55070419940094870566013613)
        ·
          refine ⟨20651407477535576462255105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55070419940094870566013613 20651407477535576462255105)
          ·
            refine ⟨15488555608151682346691329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20651407477535576462255105 15488555608151682346691329)
            ·
              refine ⟨11616416706113761760018497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15488555608151682346691329 11616416706113761760018497)
              ·
                refine ⟨8712312529585321320013873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11616416706113761760018497 8712312529585321320013873)
                ·
                  refine ⟨6534234397188990990010405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8712312529585321320013873 6534234397188990990010405)
                  ·
                    refine ⟨1225168949472935810626951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6534234397188990990010405 1225168949472935810626951)
                    ·
                      rfl

theorem cell23_7158024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_7158024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158024 prefixEnd_7158024 := by exact prefixLift 7158024
  have htrace : WordTrace (prefixWord ++ tailWord_7158024) baseStart_7158024 baseEnd_7158024 := by
    simpa [prefixWord, tailWord_7158024, baseEnd_7158024] using wordTrace_append hprefix tailTrace_7158024
  have hstable : (prefixWord ++ tailWord_7158024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158024).length < 2 ^ (prefixWord ++ tailWord_7158024).sum := by decide
  have hdescent : baseEnd_7158024 < baseStart_7158024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158047 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 3]
def baseStart_7158047 : Nat := 118140960795 + 7158047 * 2 ^ 59
def prefixEnd_7158047 : Nat := 4983230072969 + 3 ^ 40 * 7158047 * 2
def baseEnd_7158047 : Nat := 3675518658473860841893247

theorem tailTrace_7158047 : CollatzResearch.WordTrace tailWord_7158047 prefixEnd_7158047 3675518658473860841893247 := by
  unfold tailWord_7158047
  simp only [CollatzResearch.WordTrace]
  refine ⟨261075422298625690944744395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174050281532417127296496263 261075422298625690944744395)
  ·
    refine ⟨391613133447938536417116593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261075422298625690944744395 391613133447938536417116593)
    ·
      refine ⟨293709850085953902312837445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391613133447938536417116593 293709850085953902312837445)
      ·
        refine ⟨55070596891116356683657021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293709850085953902312837445 55070596891116356683657021)
        ·
          refine ⟨20651473834168633756371383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55070596891116356683657021 20651473834168633756371383)
          ·
            refine ⟨30977210751252950634557075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20651473834168633756371383 30977210751252950634557075)
            ·
              refine ⟨46465816126879425951835613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30977210751252950634557075 46465816126879425951835613)
              ·
                refine ⟨17424681047579784731938355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46465816126879425951835613 17424681047579784731938355)
                ·
                  refine ⟨26137021571369677097907533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17424681047579784731938355 26137021571369677097907533)
                  ·
                    refine ⟨9801383089263628911715325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26137021571369677097907533 9801383089263628911715325)
                    ·
                      refine ⟨3675518658473860841893247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9801383089263628911715325 3675518658473860841893247)
                      ·
                        rfl

theorem cell23_7158047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_7158047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158047 prefixEnd_7158047 := by exact prefixLift 7158047
  have htrace : WordTrace (prefixWord ++ tailWord_7158047) baseStart_7158047 baseEnd_7158047 := by
    simpa [prefixWord, tailWord_7158047, baseEnd_7158047] using wordTrace_append hprefix tailTrace_7158047
  have hstable : (prefixWord ++ tailWord_7158047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158047).length < 2 ^ (prefixWord ++ tailWord_7158047).sum := by decide
  have hdescent : baseEnd_7158047 < baseStart_7158047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158068 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_7158068 : Nat := 118140960795 + 7158068 * 2 ^ 59
def prefixEnd_7158068 : Nat := 4983230072969 + 3 ^ 40 * 7158068 * 2
def baseEnd_7158068 : Nat := 3675529441567605259730651

theorem tailTrace_7158068 : CollatzResearch.WordTrace tailWord_7158068 prefixEnd_7158068 3675529441567605259730651 := by
  unfold tailWord_7158068
  simp only [CollatzResearch.WordTrace]
  refine ⟨130538094115774805765629429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174050792154366407687505905 130538094115774805765629429)
  ·
    refine ⟨12237946323353888040527759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130538094115774805765629429 12237946323353888040527759)
    ·
      refine ⟨18356919485030832060791639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12237946323353888040527759 18356919485030832060791639)
      ·
        refine ⟨27535379227546248091187459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18356919485030832060791639 27535379227546248091187459)
        ·
          refine ⟨41303068841319372136781189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27535379227546248091187459 41303068841319372136781189)
          ·
            refine ⟨7744325407747382275646473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41303068841319372136781189 7744325407747382275646473)
            ·
              refine ⟨5808244055810536706734855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7744325407747382275646473 5808244055810536706734855)
              ·
                refine ⟨8712366083715805060102283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5808244055810536706734855 8712366083715805060102283)
                ·
                  refine ⟨13068549125573707590153425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8712366083715805060102283 13068549125573707590153425)
                  ·
                    refine ⟨9801411844180280692615069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13068549125573707590153425 9801411844180280692615069)
                    ·
                      refine ⟨3675529441567605259730651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9801411844180280692615069 3675529441567605259730651)
                      ·
                        rfl

theorem cell23_7158068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_7158068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158068 prefixEnd_7158068 := by exact prefixLift 7158068
  have htrace : WordTrace (prefixWord ++ tailWord_7158068) baseStart_7158068 baseEnd_7158068 := by
    simpa [prefixWord, tailWord_7158068, baseEnd_7158068] using wordTrace_append hprefix tailTrace_7158068
  have hstable : (prefixWord ++ tailWord_7158068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158068).length < 2 ^ (prefixWord ++ tailWord_7158068).sum := by decide
  have hdescent : baseEnd_7158068 < baseStart_7158068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158081 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7158081 : Nat := 118140960795 + 7158081 * 2 ^ 59
def prefixEnd_7158081 : Nat := 4983230072969 + 3 ^ 40 * 7158081 * 2
def baseEnd_7158081 : Nat := 3675536116816113708868091

theorem tailTrace_7158081 : CollatzResearch.WordTrace tailWord_7158081 prefixEnd_7158081 3675536116816113708868091 := by
  unfold tailWord_7158081
  simp only [CollatzResearch.WordTrace]
  refine ⟨261076662380502514751482097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174051108253668343167654731 261076662380502514751482097)
  ·
    refine ⟨195807496785376886063611573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261076662380502514751482097 195807496785376886063611573)
    ·
      refine ⟨18356952823629083068463585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195807496785376886063611573 18356952823629083068463585)
      ·
        refine ⟨13767714617721812301347689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18356952823629083068463585 13767714617721812301347689)
        ·
          refine ⟨10325785963291359226010767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13767714617721812301347689 10325785963291359226010767)
          ·
            refine ⟨15488678944937038839016151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325785963291359226010767 15488678944937038839016151)
            ·
              refine ⟨23233018417405558258524227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15488678944937038839016151 23233018417405558258524227)
              ·
                refine ⟨34849527626108337387786341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23233018417405558258524227 34849527626108337387786341)
                ·
                  refine ⟨6534286429895313260209939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34849527626108337387786341 6534286429895313260209939)
                  ·
                    refine ⟨9801429644842969890314909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6534286429895313260209939 9801429644842969890314909)
                    ·
                      refine ⟨3675536116816113708868091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9801429644842969890314909 3675536116816113708868091)
                      ·
                        rfl

theorem cell23_7158081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7158081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158081 prefixEnd_7158081 := by exact prefixLift 7158081
  have htrace : WordTrace (prefixWord ++ tailWord_7158081) baseStart_7158081 baseEnd_7158081 := by
    simpa [prefixWord, tailWord_7158081, baseEnd_7158081] using wordTrace_append hprefix tailTrace_7158081
  have hstable : (prefixWord ++ tailWord_7158081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158081).length < 2 ^ (prefixWord ++ tailWord_7158081).sum := by decide
  have hdescent : baseEnd_7158081 < baseStart_7158081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158090 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_7158090 : Nat := 118140960795 + 7158090 * 2 ^ 59
def prefixEnd_7158090 : Nat := 4983230072969 + 3 ^ 40 * 7158090 * 2
def baseEnd_7158090 : Nat := 3675540738142004173655549

theorem tailTrace_7158090 : CollatzResearch.WordTrace tailWord_7158090 prefixEnd_7158090 3675540738142004173655549 := by
  unfold tailWord_7158090
  simp only [CollatzResearch.WordTrace]
  refine ⟨65269247659367477322139931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174051327091646606192373149 65269247659367477322139931)
  ·
    refine ⟨97903871489051215983209897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65269247659367477322139931 97903871489051215983209897)
    ·
      refine ⟨73427903616788411987407423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97903871489051215983209897 73427903616788411987407423)
      ·
        refine ⟨110141855425182617981111135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73427903616788411987407423 110141855425182617981111135)
        ·
          refine ⟨165212783137773926971666703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110141855425182617981111135 165212783137773926971666703)
          ·
            refine ⟨247819174706660890457500055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165212783137773926971666703 247819174706660890457500055)
            ·
              refine ⟨371728762059991335686250083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247819174706660890457500055 371728762059991335686250083)
              ·
                refine ⟨557593143089987003529375125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371728762059991335686250083 557593143089987003529375125)
                ·
                  refine ⟨26137178582343140790439459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 557593143089987003529375125 26137178582343140790439459)
                  ·
                    refine ⟨39205767873514711185659189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26137178582343140790439459 39205767873514711185659189)
                    ·
                      refine ⟨3675540738142004173655549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39205767873514711185659189 3675540738142004173655549)
                      ·
                        rfl

theorem cell23_7158090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_7158090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158090 prefixEnd_7158090 := by exact prefixLift 7158090
  have htrace : WordTrace (prefixWord ++ tailWord_7158090) baseStart_7158090 baseEnd_7158090 := by
    simpa [prefixWord, tailWord_7158090, baseEnd_7158090] using wordTrace_append hprefix tailTrace_7158090
  have hstable : (prefixWord ++ tailWord_7158090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158090).length < 2 ^ (prefixWord ++ tailWord_7158090).sum := by decide
  have hdescent : baseEnd_7158090 < baseStart_7158090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158127 : List Nat := [1, 1, 2, 1, 3, 1, 2, 7, 5]
def baseStart_7158127 : Nat := 118140960795 + 7158127 * 2 ^ 59
def prefixEnd_7158127 : Nat := 4983230072969 + 3 ^ 40 * 7158127 * 2
def baseEnd_7158127 : Nat := 408395526325135614321431

theorem tailTrace_7158127 : CollatzResearch.WordTrace tailWord_7158127 prefixEnd_7158127 408395526325135614321431 := by
  unfold tailWord_7158127
  simp only [CollatzResearch.WordTrace]
  refine ⟨261078340138335864607656635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174052226758890576405104423 261078340138335864607656635)
  ·
    refine ⟨391617510207503796911484953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261078340138335864607656635 391617510207503796911484953)
    ·
      refine ⟨293713132655627847683613715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391617510207503796911484953 293713132655627847683613715)
      ·
        refine ⟨440569698983441771525420573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293713132655627847683613715 440569698983441771525420573)
        ·
          refine ⟨165213637118790664322032715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440569698983441771525420573 165213637118790664322032715)
          ·
            refine ⟨247820455678185996483049073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165213637118790664322032715 247820455678185996483049073)
            ·
              refine ⟨185865341758639497362286805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247820455678185996483049073 185865341758639497362286805)
              ·
                refine ⟨4356218947468113219428597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 185865341758639497362286805 4356218947468113219428597)
                ·
                  refine ⟨408395526325135614321431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4356218947468113219428597 408395526325135614321431)
                  ·
                    rfl

theorem cell23_7158127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 5].length) (baseStart_7158127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158127 prefixEnd_7158127 := by exact prefixLift 7158127
  have htrace : WordTrace (prefixWord ++ tailWord_7158127) baseStart_7158127 baseEnd_7158127 := by
    simpa [prefixWord, tailWord_7158127, baseEnd_7158127] using wordTrace_append hprefix tailTrace_7158127
  have hstable : (prefixWord ++ tailWord_7158127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158127).length < 2 ^ (prefixWord ++ tailWord_7158127).sum := by decide
  have hdescent : baseEnd_7158127 < baseStart_7158127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158140 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_7158140 : Nat := 118140960795 + 7158140 * 2 ^ 59
def prefixEnd_7158140 : Nat := 4983230072969 + 3 ^ 40 * 7158140 * 2
def baseEnd_7158140 : Nat := 1225188804058242992676773

theorem tailTrace_7158140 : CollatzResearch.WordTrace tailWord_7158140 prefixEnd_7158140 1225188804058242992676773 := by
  unfold tailWord_7158140
  simp only [CollatzResearch.WordTrace]
  refine ⟨130539407143644383913939937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174052542858192511885253249 130539407143644383913939937)
  ·
    refine ⟨97904555357733287935454953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130539407143644383913939937 97904555357733287935454953)
    ·
      refine ⟨73428416518299965951591215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97904555357733287935454953 73428416518299965951591215)
      ·
        refine ⟨110142624777449948927386823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73428416518299965951591215 110142624777449948927386823)
        ·
          refine ⟨165213937166174923391080235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110142624777449948927386823 165213937166174923391080235)
          ·
            refine ⟨247820905749262385086620353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165213937166174923391080235 247820905749262385086620353)
            ·
              refine ⟨185865679311946788814965265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247820905749262385086620353 185865679311946788814965265)
              ·
                refine ⟨139399259483960091611223949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185865679311946788814965265 139399259483960091611223949)
                ·
                  refine ⟨52274722306485034354208981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139399259483960091611223949 52274722306485034354208981)
                  ·
                    refine ⟨1225188804058242992676773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52274722306485034354208981 1225188804058242992676773)
                    ·
                      rfl

theorem cell23_7158140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_7158140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158140 prefixEnd_7158140 := by exact prefixLift 7158140
  have htrace : WordTrace (prefixWord ++ tailWord_7158140) baseStart_7158140 baseEnd_7158140 := by
    simpa [prefixWord, tailWord_7158140, baseEnd_7158140] using wordTrace_append hprefix tailTrace_7158140
  have hstable : (prefixWord ++ tailWord_7158140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158140).length < 2 ^ (prefixWord ++ tailWord_7158140).sum := by decide
  have hdescent : baseEnd_7158140 < baseStart_7158140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158184 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7158184 : Nat := 118140960795 + 7158184 * 2 ^ 59
def prefixEnd_7158184 : Nat := 4983230072969 + 3 ^ 40 * 7158184 * 2
def baseEnd_7158184 : Nat := 3675589005323526805880117

theorem tailTrace_7158184 : CollatzResearch.WordTrace tailWord_7158184 prefixEnd_7158184 3675589005323526805880117 := by
  unfold tailWord_7158184
  simp only [CollatzResearch.WordTrace]
  refine ⟨130540209549564681671240803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174053612732752908894987737 130540209549564681671240803)
  ·
    refine ⟨195810314324347022506861205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130540209549564681671240803 195810314324347022506861205)
    ·
      refine ⟨9178608483953766680009119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 195810314324347022506861205 9178608483953766680009119)
      ·
        refine ⟨13767912725930650020013679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9178608483953766680009119 13767912725930650020013679)
        ·
          refine ⟨20651869088895975030020519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13767912725930650020013679 20651869088895975030020519)
          ·
            refine ⟨30977803633343962545030779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20651869088895975030020519 30977803633343962545030779)
            ·
              refine ⟨46466705450015943817546169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30977803633343962545030779 46466705450015943817546169)
              ·
                refine ⟨34850029087511957863159627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46466705450015943817546169 34850029087511957863159627)
                ·
                  refine ⟨52275043631267936794739441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34850029087511957863159627 52275043631267936794739441)
                  ·
                    refine ⟨39206282723450952596054581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52275043631267936794739441 39206282723450952596054581)
                    ·
                      refine ⟨3675589005323526805880117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39206282723450952596054581 3675589005323526805880117)
                      ·
                        rfl

theorem cell23_7158184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7158184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158184 prefixEnd_7158184 := by exact prefixLift 7158184
  have htrace : WordTrace (prefixWord ++ tailWord_7158184) baseStart_7158184 baseEnd_7158184 := by
    simpa [prefixWord, tailWord_7158184, baseEnd_7158184] using wordTrace_append hprefix tailTrace_7158184
  have hstable : (prefixWord ++ tailWord_7158184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158184).length < 2 ^ (prefixWord ++ tailWord_7158184).sum := by decide
  have hdescent : baseEnd_7158184 < baseStart_7158184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158194 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2]
def baseStart_7158194 : Nat := 118140960795 + 7158194 * 2 ^ 59
def prefixEnd_7158194 : Nat := 4983230072969 + 3 ^ 40 * 7158194 * 2
def baseEnd_7158194 : Nat := 3675594140130071766755071

theorem tailTrace_7158194 : CollatzResearch.WordTrace tailWord_7158194 prefixEnd_7158194 3675594140130071766755071 := by
  unfold tailWord_7158194
  simp only [CollatzResearch.WordTrace]
  refine ⟨65270195957273283762586409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174053855886062090033563757 65270195957273283762586409)
  ·
    refine ⟨48952646967954962821939807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65270195957273283762586409 48952646967954962821939807)
    ·
      refine ⟨73428970451932444232909711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48952646967954962821939807 73428970451932444232909711)
      ·
        refine ⟨110143455677898666349364567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73428970451932444232909711 110143455677898666349364567)
        ·
          refine ⟨165215183516847999524046851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110143455677898666349364567 165215183516847999524046851)
          ·
            refine ⟨247822775275271999286070277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165215183516847999524046851 247822775275271999286070277)
            ·
              refine ⟨46466770364113499866138177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247822775275271999286070277 46466770364113499866138177)
              ·
                refine ⟨34850077773085124899603633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46466770364113499866138177 34850077773085124899603633)
                ·
                  refine ⟨26137558329813843674702725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34850077773085124899603633 26137558329813843674702725)
                  ·
                    refine ⟨4900792186840095689006761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26137558329813843674702725 4900792186840095689006761)
                    ·
                      refine ⟨3675594140130071766755071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900792186840095689006761 3675594140130071766755071)
                      ·
                        rfl

theorem cell23_7158194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_7158194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158194 prefixEnd_7158194 := by exact prefixLift 7158194
  have htrace : WordTrace (prefixWord ++ tailWord_7158194) baseStart_7158194 baseEnd_7158194 := by
    simpa [prefixWord, tailWord_7158194, baseEnd_7158194] using wordTrace_append hprefix tailTrace_7158194
  have hstable : (prefixWord ++ tailWord_7158194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158194).length < 2 ^ (prefixWord ++ tailWord_7158194).sum := by decide
  have hdescent : baseEnd_7158194 < baseStart_7158194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158217 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 6]
def baseStart_7158217 : Nat := 118140960795 + 7158217 * 2 ^ 59
def prefixEnd_7158217 : Nat := 4983230072969 + 3 ^ 40 * 7158217 * 2
def baseEnd_7158217 : Nat := 408400661131680575196385

theorem tailTrace_7158217 : CollatzResearch.WordTrace tailWord_7158217 prefixEnd_7158217 408400661131680575196385 := by
  unfold tailWord_7158217
  simp only [CollatzResearch.WordTrace]
  refine ⟨261081622708009809978432905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174054415138673206652288603 261081622708009809978432905)
  ·
    refine ⟨195811217031007357483824679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261081622708009809978432905 195811217031007357483824679)
    ·
      refine ⟨293716825546511036225737019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195811217031007357483824679 293716825546511036225737019)
      ·
        refine ⟨440575238319766554338605529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293716825546511036225737019 440575238319766554338605529)
        ·
          refine ⟨330431428739824915753954147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440575238319766554338605529 330431428739824915753954147)
          ·
            refine ⟨495647143109737373630931221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330431428739824915753954147 495647143109737373630931221)
            ·
              refine ⟨23233459833268939388949901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 495647143109737373630931221 23233459833268939388949901)
              ·
                refine ⟨8712547437475852270856213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23233459833268939388949901 8712547437475852270856213)
                ·
                  refine ⟨408400661131680575196385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8712547437475852270856213 408400661131680575196385)
                  ·
                    rfl

theorem cell23_7158217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 6].length) (baseStart_7158217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158217 prefixEnd_7158217 := by exact prefixLift 7158217
  have htrace : WordTrace (prefixWord ++ tailWord_7158217) baseStart_7158217 baseEnd_7158217 := by
    simpa [prefixWord, tailWord_7158217, baseEnd_7158217] using wordTrace_append hprefix tailTrace_7158217
  have hstable : (prefixWord ++ tailWord_7158217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158217).length < 2 ^ (prefixWord ++ tailWord_7158217).sum := by decide
  have hdescent : baseEnd_7158217 < baseStart_7158217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158301 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_7158301 : Nat := 118140960795 + 7158301 * 2 ^ 59
def prefixEnd_7158301 : Nat := 4983230072969 + 3 ^ 40 * 7158301 * 2
def baseEnd_7158301 : Nat := 3675649082560102848117079

theorem tailTrace_7158301 : CollatzResearch.WordTrace tailWord_7158301 prefixEnd_7158301 3675649082560102848117079 := by
  unfold tailWord_7158301
  simp only [CollatzResearch.WordTrace]
  refine ⟨261084686439705492324490757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174056457626470328216327171 261084686439705492324490757)
  ·
    refine ⟨48953378707444779810842017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261084686439705492324490757 48953378707444779810842017)
    ·
      refine ⟨36715034030583584858131513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48953378707444779810842017 36715034030583584858131513)
      ·
        refine ⟨27536275522937688643598635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36715034030583584858131513 27536275522937688643598635)
        ·
          refine ⟨41304413284406532965397953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27536275522937688643598635 41304413284406532965397953)
          ·
            refine ⟨30978309963304899724048465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41304413284406532965397953 30978309963304899724048465)
            ·
              refine ⟨23233732472478674793036349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30978309963304899724048465 23233732472478674793036349)
              ·
                refine ⟨8712649677179503047388631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23233732472478674793036349 8712649677179503047388631)
                ·
                  refine ⟨13068974515769254571082947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8712649677179503047388631 13068974515769254571082947)
                  ·
                    refine ⟨19603461773653881856624421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13068974515769254571082947 19603461773653881856624421)
                    ·
                      refine ⟨3675649082560102848117079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19603461773653881856624421 3675649082560102848117079)
                      ·
                        rfl

theorem cell23_7158301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_7158301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158301 prefixEnd_7158301 := by exact prefixLift 7158301
  have htrace : WordTrace (prefixWord ++ tailWord_7158301) baseStart_7158301 baseEnd_7158301 := by
    simpa [prefixWord, tailWord_7158301, baseEnd_7158301] using wordTrace_append hprefix tailTrace_7158301
  have hstable : (prefixWord ++ tailWord_7158301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158301).length < 2 ^ (prefixWord ++ tailWord_7158301).sum := by decide
  have hdescent : baseEnd_7158301 < baseStart_7158301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158307 : List Nat := [1, 1, 1, 4, 4, 1, 11]
def baseStart_7158307 : Nat := 118140960795 + 7158307 * 2 ^ 59
def prefixEnd_7158307 : Nat := 4983230072969 + 3 ^ 40 * 7158307 * 2
def baseEnd_7158307 : Nat := 45378421770913948452371

theorem tailTrace_7158307 : CollatzResearch.WordTrace tailWord_7158307 prefixEnd_7158307 45378421770913948452371 := by
  unfold tailWord_7158307
  simp only [CollatzResearch.WordTrace]
  refine ⟨261084905277683755349209175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174056603518455836899472783 261084905277683755349209175)
  ·
    refine ⟨391627357916525633023813763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261084905277683755349209175 391627357916525633023813763)
    ·
      refine ⟨587441036874788449535720645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391627357916525633023813763 587441036874788449535720645)
      ·
        refine ⟨110145194414022834287947621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 587441036874788449535720645 110145194414022834287947621)
        ·
          refine ⟨20652223952629281428990179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110145194414022834287947621 20652223952629281428990179)
          ·
            refine ⟨30978335928943922143485269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20652223952629281428990179 30978335928943922143485269)
            ·
              refine ⟨45378421770913948452371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30978335928943922143485269 45378421770913948452371)
              ·
                rfl

theorem cell23_7158307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 11].length) (baseStart_7158307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158307 prefixEnd_7158307 := by exact prefixLift 7158307
  have htrace : WordTrace (prefixWord ++ tailWord_7158307) baseStart_7158307 baseEnd_7158307 := by
    simpa [prefixWord, tailWord_7158307, baseEnd_7158307] using wordTrace_append hprefix tailTrace_7158307
  have hstable : (prefixWord ++ tailWord_7158307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158307).length < 2 ^ (prefixWord ++ tailWord_7158307).sum := by decide
  have hdescent : baseEnd_7158307 < baseStart_7158307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158312 : List Nat := [2, 1, 5, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_7158312 : Nat := 118140960795 + 7158312 * 2 ^ 59
def prefixEnd_7158312 : Nat := 4983230072969 + 3 ^ 40 * 7158312 * 2
def baseEnd_7158312 : Nat := 3675654730847302305079529

theorem tailTrace_7158312 : CollatzResearch.WordTrace tailWord_7158312 prefixEnd_7158312 3675654730847302305079529 := by
  unfold tailWord_7158312
  simp only [CollatzResearch.WordTrace]
  refine ⟨130542543821332820601570595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174056725095110427468760793 130542543821332820601570595)
  ·
    refine ⟨195813815731999230902355893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130542543821332820601570595 195813815731999230902355893)
    ·
      refine ⟨18357545224874927897095865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195813815731999230902355893 18357545224874927897095865)
      ·
        refine ⟨13768158918656195922821899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18357545224874927897095865 13768158918656195922821899)
        ·
          refine ⟨20652238377984293884232849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13768158918656195922821899 20652238377984293884232849)
          ·
            refine ⟨15489178783488220413174637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20652238377984293884232849 15489178783488220413174637)
            ·
              refine ⟨5808442043808082654940489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15489178783488220413174637 5808442043808082654940489)
              ·
                refine ⟨4356331532856061991205367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5808442043808082654940489 4356331532856061991205367)
                ·
                  refine ⟨6534497299284092986808051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356331532856061991205367 6534497299284092986808051)
                  ·
                    refine ⟨9801745948926139480212077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6534497299284092986808051 9801745948926139480212077)
                    ·
                      refine ⟨3675654730847302305079529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9801745948926139480212077 3675654730847302305079529)
                      ·
                        rfl

theorem cell23_7158312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_7158312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158312 prefixEnd_7158312 := by exact prefixLift 7158312
  have htrace : WordTrace (prefixWord ++ tailWord_7158312) baseStart_7158312 baseEnd_7158312 := by
    simpa [prefixWord, tailWord_7158312, baseEnd_7158312] using wordTrace_append hprefix tailTrace_7158312
  have hstable : (prefixWord ++ tailWord_7158312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158312).length < 2 ^ (prefixWord ++ tailWord_7158312).sum := by decide
  have hdescent : baseEnd_7158312 < baseStart_7158312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158314 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_7158314 : Nat := 118140960795 + 7158314 * 2 ^ 59
def prefixEnd_7158314 : Nat := 4983230072969 + 3 ^ 40 * 7158314 * 2
def baseEnd_7158314 : Nat := 3675655757808611297254519

theorem tailTrace_7158314 : CollatzResearch.WordTrace tailWord_7158314 prefixEnd_7158314 3675655757808611297254519 := by
  unfold tailWord_7158314
  simp only [CollatzResearch.WordTrace]
  refine ⟨65271290147164598886178499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174056773725772263696475997 65271290147164598886178499)
  ·
    refine ⟨97906935220746898329267749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65271290147164598886178499 97906935220746898329267749)
    ·
      refine ⟨18357550353890043436737703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97906935220746898329267749 18357550353890043436737703)
      ·
        refine ⟨27536325530835065155106555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18357550353890043436737703 27536325530835065155106555)
        ·
          refine ⟨41304488296252597732659833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27536325530835065155106555 41304488296252597732659833)
          ·
            refine ⟨30978366222189448299494875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41304488296252597732659833 30978366222189448299494875)
            ·
              refine ⟨46467549333284172449242313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30978366222189448299494875 46467549333284172449242313)
              ·
                refine ⟨34850661999963129336931735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46467549333284172449242313 34850661999963129336931735)
                ·
                  refine ⟨52275992999944694005397603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34850661999963129336931735 52275992999944694005397603)
                  ·
                    refine ⟨78413989499917041008096405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52275992999944694005397603 78413989499917041008096405)
                    ·
                      refine ⟨3675655757808611297254519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78413989499917041008096405 3675655757808611297254519)
                      ·
                        rfl

theorem cell23_7158314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_7158314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158314 prefixEnd_7158314 := by exact prefixLift 7158314
  have htrace : WordTrace (prefixWord ++ tailWord_7158314) baseStart_7158314 baseEnd_7158314 := by
    simpa [prefixWord, tailWord_7158314, baseEnd_7158314] using wordTrace_append hprefix tailTrace_7158314
  have hstable : (prefixWord ++ tailWord_7158314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158314).length < 2 ^ (prefixWord ++ tailWord_7158314).sum := by decide
  have hdescent : baseEnd_7158314 < baseStart_7158314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158327 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_7158327 : Nat := 118140960795 + 7158327 * 2 ^ 59
def prefixEnd_7158327 : Nat := 4983230072969 + 3 ^ 40 * 7158327 * 2
def baseEnd_7158327 : Nat := 3675662433057119746391959

theorem tailTrace_7158327 : CollatzResearch.WordTrace tailWord_7158327 prefixEnd_7158327 3675662433057119746391959 := by
  unfold tailWord_7158327
  simp only [CollatzResearch.WordTrace]
  refine ⟨261085634737611298764937235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174057089825074199176624823 261085634737611298764937235)
  ·
    refine ⟨391628452106416948147405853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261085634737611298764937235 391628452106416948147405853)
    ·
      refine ⟨146860669539906355555277195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391628452106416948147405853 146860669539906355555277195)
      ·
        refine ⟨220291004309859533332915793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146860669539906355555277195 220291004309859533332915793)
        ·
          refine ⟨165218253232394649999686845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220291004309859533332915793 165218253232394649999686845)
          ·
            refine ⟨61956844962147993749882567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165218253232394649999686845 61956844962147993749882567)
            ·
              refine ⟨92935267443221990624823851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61956844962147993749882567 92935267443221990624823851)
              ·
                refine ⟨139402901164832985937235777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92935267443221990624823851 139402901164832985937235777)
                ·
                  refine ⟨104552175873624739452926833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139402901164832985937235777 104552175873624739452926833)
                  ·
                    refine ⟨78414131905218554589695125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104552175873624739452926833 78414131905218554589695125)
                    ·
                      refine ⟨3675662433057119746391959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78414131905218554589695125 3675662433057119746391959)
                      ·
                        rfl

theorem cell23_7158327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_7158327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158327 prefixEnd_7158327 := by exact prefixLift 7158327
  have htrace : WordTrace (prefixWord ++ tailWord_7158327) baseStart_7158327 baseEnd_7158327 := by
    simpa [prefixWord, tailWord_7158327, baseEnd_7158327] using wordTrace_append hprefix tailTrace_7158327
  have hstable : (prefixWord ++ tailWord_7158327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158327).length < 2 ^ (prefixWord ++ tailWord_7158327).sum := by decide
  have hdescent : baseEnd_7158327 < baseStart_7158327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158347 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 5]
def baseStart_7158347 : Nat := 118140960795 + 7158347 * 2 ^ 59
def prefixEnd_7158347 : Nat := 4983230072969 + 3 ^ 40 * 7158347 * 2
def baseEnd_7158347 : Nat := 3675672702670209668141867

theorem tailTrace_7158347 : CollatzResearch.WordTrace tailWord_7158347 prefixEnd_7158347 3675672702670209668141867 := by
  unfold tailWord_7158347
  simp only [CollatzResearch.WordTrace]
  refine ⟨261086364197538842180665295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174057576131692561453776863 261086364197538842180665295)
  ·
    refine ⟨391629546296308263270997943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261086364197538842180665295 391629546296308263270997943)
    ·
      refine ⟨587444319444462394906496915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391629546296308263270997943 587444319444462394906496915)
      ·
        refine ⟨881166479166693592359745373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587444319444462394906496915 881166479166693592359745373)
        ·
          refine ⟨330437429687510097134904515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 881166479166693592359745373 330437429687510097134904515)
          ·
            refine ⟨495656144531265145702356773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330437429687510097134904515 495656144531265145702356773)
            ·
              refine ⟨92935527099612214819191895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 495656144531265145702356773 92935527099612214819191895)
              ·
                refine ⟨139403290649418322228787843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92935527099612214819191895 139403290649418322228787843)
                ·
                  refine ⟨209104935974127483343181765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139403290649418322228787843 209104935974127483343181765)
                  ·
                    refine ⟨39207175495148903126846581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209104935974127483343181765 39207175495148903126846581)
                    ·
                      refine ⟨3675672702670209668141867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39207175495148903126846581 3675672702670209668141867)
                      ·
                        rfl

theorem cell23_7158347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_7158347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158347 prefixEnd_7158347 := by exact prefixLift 7158347
  have htrace : WordTrace (prefixWord ++ tailWord_7158347) baseStart_7158347 baseEnd_7158347 := by
    simpa [prefixWord, tailWord_7158347, baseEnd_7158347] using wordTrace_append hprefix tailTrace_7158347
  have hstable : (prefixWord ++ tailWord_7158347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158347).length < 2 ^ (prefixWord ++ tailWord_7158347).sum := by decide
  have hdescent : baseEnd_7158347 < baseStart_7158347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158367 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 3, 8]
def baseStart_7158367 : Nat := 118140960795 + 7158367 * 2 ^ 59
def prefixEnd_7158367 : Nat := 4983230072969 + 3 ^ 40 * 7158367 * 2
def baseEnd_7158367 : Nat := 1225227657427766529963925

theorem tailTrace_7158367 : CollatzResearch.WordTrace tailWord_7158367 prefixEnd_7158367 1225227657427766529963925 := by
  unfold tailWord_7158367
  simp only [CollatzResearch.WordTrace]
  refine ⟨261087093657466385596393355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174058062438310923730928903 261087093657466385596393355)
  ·
    refine ⟨391630640486199578394590033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261087093657466385596393355 391630640486199578394590033)
    ·
      refine ⟨293722980364649683795942525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391630640486199578394590033 293722980364649683795942525)
      ·
        refine ⟨110146117636743631423478447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293722980364649683795942525 110146117636743631423478447)
        ·
          refine ⟨165219176455115447135217671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110146117636743631423478447 165219176455115447135217671)
          ·
            refine ⟨247828764682673170702826507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165219176455115447135217671 247828764682673170702826507)
            ·
              refine ⟨371743147024009756054239761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247828764682673170702826507 371743147024009756054239761)
              ·
                refine ⟨278807360268007317040679821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371743147024009756054239761 278807360268007317040679821)
                ·
                  refine ⟨104552760100502743890254933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278807360268007317040679821 104552760100502743890254933)
                  ·
                    refine ⟨1225227657427766529963925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104552760100502743890254933 1225227657427766529963925)
                    ·
                      rfl

theorem cell23_7158367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_7158367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158367 prefixEnd_7158367 := by exact prefixLift 7158367
  have htrace : WordTrace (prefixWord ++ tailWord_7158367) baseStart_7158367 baseEnd_7158367 := by
    simpa [prefixWord, tailWord_7158367, baseEnd_7158367] using wordTrace_append hprefix tailTrace_7158367
  have hstable : (prefixWord ++ tailWord_7158367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158367).length < 2 ^ (prefixWord ++ tailWord_7158367).sum := by decide
  have hdescent : baseEnd_7158367 < baseStart_7158367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158391 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 1, 4, 2]
def baseStart_7158391 : Nat := 118140960795 + 7158391 * 2 ^ 59
def prefixEnd_7158391 : Nat := 4983230072969 + 3 ^ 40 * 7158391 * 2
def baseEnd_7158391 : Nat := 3675695295819007495991665

theorem tailTrace_7158391 : CollatzResearch.WordTrace tailWord_7158391 prefixEnd_7158391 3675695295819007495991665 := by
  unfold tailWord_7158391
  simp only [CollatzResearch.WordTrace]
  refine ⟨261087969009379437695267027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174058646006252958463511351 261087969009379437695267027)
  ·
    refine ⟨391631953514069156542900541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261087969009379437695267027 391631953514069156542900541)
    ·
      refine ⟨146861982567775933703587703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391631953514069156542900541 146861982567775933703587703)
      ·
        refine ⟨220292973851663900555381555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146861982567775933703587703 220292973851663900555381555)
        ·
          refine ⟨330439460777495850833072333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220292973851663900555381555 330439460777495850833072333)
          ·
            refine ⟨123914797791560944062402125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330439460777495850833072333 123914797791560944062402125)
            ·
              refine ⟨46468049171835354023400797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123914797791560944062402125 46468049171835354023400797)
              ·
                refine ⟨17425518439438257758775299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46468049171835354023400797 17425518439438257758775299)
                ·
                  refine ⟨26138277659157386638162949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17425518439438257758775299 26138277659157386638162949)
                  ·
                    refine ⟨4900927061092009994655553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26138277659157386638162949 4900927061092009994655553)
                    ·
                      refine ⟨3675695295819007495991665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4900927061092009994655553 3675695295819007495991665)
                      ·
                        rfl

theorem cell23_7158391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_7158391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158391 prefixEnd_7158391 := by exact prefixLift 7158391
  have htrace : WordTrace (prefixWord ++ tailWord_7158391) baseStart_7158391 baseEnd_7158391 := by
    simpa [prefixWord, tailWord_7158391, baseEnd_7158391] using wordTrace_append hprefix tailTrace_7158391
  have hstable : (prefixWord ++ tailWord_7158391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158391).length < 2 ^ (prefixWord ++ tailWord_7158391).sum := by decide
  have hdescent : baseEnd_7158391 < baseStart_7158391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158414 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_7158414 : Nat := 118140960795 + 7158414 * 2 ^ 59
def prefixEnd_7158414 : Nat := 4983230072969 + 3 ^ 40 * 7158414 * 2
def baseEnd_7158414 : Nat := 408411900652673434000451

theorem tailTrace_7158414 : CollatzResearch.WordTrace tailWord_7158414 prefixEnd_7158414 408411900652673434000451 := by
  unfold tailWord_7158414
  simp only [CollatzResearch.WordTrace]
  refine ⟨32636100986037014077919287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174059205258864075082236197 32636100986037014077919287)
  ·
    refine ⟨48954151479055521116878931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32636100986037014077919287 48954151479055521116878931)
    ·
      refine ⟨73431227218583281675318397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48954151479055521116878931 73431227218583281675318397)
      ·
        refine ⟨27536710206968730628244399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73431227218583281675318397 27536710206968730628244399)
        ·
          refine ⟨41305065310453095942366599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27536710206968730628244399 41305065310453095942366599)
          ·
            refine ⟨61957597965679643913549899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41305065310453095942366599 61957597965679643913549899)
            ·
              refine ⟨92936396948519465870324849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61957597965679643913549899 92936396948519465870324849)
              ·
                refine ⟨69702297711389599402743637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92936396948519465870324849 69702297711389599402743637)
                ·
                  refine ⟨408411900652673434000451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69702297711389599402743637 408411900652673434000451)
                  ·
                    rfl

theorem cell23_7158414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_7158414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158414 prefixEnd_7158414 := by exact prefixLift 7158414
  have htrace : WordTrace (prefixWord ++ tailWord_7158414) baseStart_7158414 baseEnd_7158414 := by
    simpa [prefixWord, tailWord_7158414, baseEnd_7158414] using wordTrace_append hprefix tailTrace_7158414
  have hstable : (prefixWord ++ tailWord_7158414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158414).length < 2 ^ (prefixWord ++ tailWord_7158414).sum := by decide
  have hdescent : baseEnd_7158414 < baseStart_7158414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158481 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_7158481 : Nat := 118140960795 + 7158481 * 2 ^ 59
def prefixEnd_7158481 : Nat := 4983230072969 + 3 ^ 40 * 7158481 * 2
def baseEnd_7158481 : Nat := 3675741509077912143866251

theorem tailTrace_7158481 : CollatzResearch.WordTrace tailWord_7158481 prefixEnd_7158481 3675741509077912143866251 := by
  unfold tailWord_7158481
  simp only [CollatzResearch.WordTrace]
  refine ⟨261091251579053383066043297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174060834386035588710695531 261091251579053383066043297)
  ·
    refine ⟨195818438684290037299532473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261091251579053383066043297 195818438684290037299532473)
    ·
      refine ⟨146863829013217527974649355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195818438684290037299532473 146863829013217527974649355)
      ·
        refine ⟨220295743519826291961974033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146863829013217527974649355 220295743519826291961974033)
        ·
          refine ⟨165221807639869718971480525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220295743519826291961974033 165221807639869718971480525)
          ·
            refine ⟨61958177864951144614305197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165221807639869718971480525 61958177864951144614305197)
            ·
              refine ⟨23234316699356679230364449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61958177864951144614305197 23234316699356679230364449)
              ·
                refine ⟨17425737524517509422773337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23234316699356679230364449 17425737524517509422773337)
                ·
                  refine ⟨13069303143388132067080003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17425737524517509422773337 13069303143388132067080003)
                  ·
                    refine ⟨19603954715082198100620005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13069303143388132067080003 19603954715082198100620005)
                    ·
                      refine ⟨3675741509077912143866251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19603954715082198100620005 3675741509077912143866251)
                      ·
                        rfl

theorem cell23_7158481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_7158481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158481 prefixEnd_7158481 := by exact prefixLift 7158481
  have htrace : WordTrace (prefixWord ++ tailWord_7158481) baseStart_7158481 baseEnd_7158481 := by
    simpa [prefixWord, tailWord_7158481, baseEnd_7158481] using wordTrace_append hprefix tailTrace_7158481
  have hstable : (prefixWord ++ tailWord_7158481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158481).length < 2 ^ (prefixWord ++ tailWord_7158481).sum := by decide
  have hdescent : baseEnd_7158481 < baseStart_7158481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158568 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 1, 5]
def baseStart_7158568 : Nat := 118140960795 + 7158568 * 2 ^ 59
def prefixEnd_7158568 : Nat := 4983230072969 + 3 ^ 40 * 7158568 * 2
def baseEnd_7158568 : Nat := 1225262060631617767826117

theorem tailTrace_7158568 : CollatzResearch.WordTrace tailWord_7158568 prefixEnd_7158568 1225262060631617767826117 := by
  unfold tailWord_7158568
  simp only [CollatzResearch.WordTrace]
  refine ⟨130547212364869098462230179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174062949819825464616306905 130547212364869098462230179)
  ·
    refine ⟨195820818547303647693345269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130547212364869098462230179 195820818547303647693345269)
    ·
      refine ⟨18358201738809716971251119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195820818547303647693345269 18358201738809716971251119)
      ·
        refine ⟨27537302608214575456876679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18358201738809716971251119 27537302608214575456876679)
        ·
          refine ⟨41305953912321863185315019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27537302608214575456876679 41305953912321863185315019)
          ·
            refine ⟨61958930868482794777972529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41305953912321863185315019 61958930868482794777972529)
            ·
              refine ⟨46469198151362096083479397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61958930868482794777972529 46469198151362096083479397)
              ·
                refine ⟨8712974653380393015652387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46469198151362096083479397 8712974653380393015652387)
                ·
                  refine ⟨13069461980070589523478581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8712974653380393015652387 13069461980070589523478581)
                  ·
                    refine ⟨1225262060631617767826117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13069461980070589523478581 1225262060631617767826117)
                    ·
                      rfl

theorem cell23_7158568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_7158568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158568 prefixEnd_7158568 := by exact prefixLift 7158568
  have htrace : WordTrace (prefixWord ++ tailWord_7158568) baseStart_7158568 baseEnd_7158568 := by
    simpa [prefixWord, tailWord_7158568, baseEnd_7158568] using wordTrace_append hprefix tailTrace_7158568
  have hstable : (prefixWord ++ tailWord_7158568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158568).length < 2 ^ (prefixWord ++ tailWord_7158568).sum := by decide
  have hdescent : baseEnd_7158568 < baseStart_7158568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158618 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4]
def baseStart_7158618 : Nat := 118140960795 + 7158618 * 2 ^ 59
def prefixEnd_7158618 : Nat := 4983230072969 + 3 ^ 40 * 7158618 * 2
def baseEnd_7158618 : Nat := 3675811855927578107853121

theorem tailTrace_7158618 : CollatzResearch.WordTrace tailWord_7158618 prefixEnd_7158618 3675811855927578107853121 := by
  unfold tailWord_7158618
  simp only [CollatzResearch.WordTrace]
  refine ⟨65274062094889263865945127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174064165586371370309187005 65274062094889263865945127)
  ·
    refine ⟨97911093142333895798917691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65274062094889263865945127 97911093142333895798917691)
    ·
      refine ⟨146866639713500843698376537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97911093142333895798917691 146866639713500843698376537)
      ·
        refine ⟨110149979785125632773782403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146866639713500843698376537 110149979785125632773782403)
        ·
          refine ⟨165224969677688449160673605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110149979785125632773782403 165224969677688449160673605)
          ·
            refine ⟨30979681814566584217626301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165224969677688449160673605 30979681814566584217626301)
            ·
              refine ⟨11617380680462469081609863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30979681814566584217626301 11617380680462469081609863)
              ·
                refine ⟨17426071020693703622414795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11617380680462469081609863 17426071020693703622414795)
                ·
                  refine ⟨26139106531040555433622193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17426071020693703622414795 26139106531040555433622193)
                  ·
                    refine ⟨19604329898280416575216645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26139106531040555433622193 19604329898280416575216645)
                    ·
                      refine ⟨3675811855927578107853121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19604329898280416575216645 3675811855927578107853121)
                      ·
                        rfl

theorem cell23_7158618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_7158618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158618 prefixEnd_7158618 := by exact prefixLift 7158618
  have htrace : WordTrace (prefixWord ++ tailWord_7158618) baseStart_7158618 baseEnd_7158618 := by
    simpa [prefixWord, tailWord_7158618, baseEnd_7158618] using wordTrace_append hprefix tailTrace_7158618
  have hstable : (prefixWord ++ tailWord_7158618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158618).length < 2 ^ (prefixWord ++ tailWord_7158618).sum := by decide
  have hdescent : baseEnd_7158618 < baseStart_7158618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158628 : List Nat := [2, 3, 1, 1, 4, 1, 4, 7]
def baseStart_7158628 : Nat := 118140960795 + 7158628 * 2 ^ 59
def prefixEnd_7158628 : Nat := 4983230072969 + 3 ^ 40 * 7158628 * 2
def baseEnd_7158628 : Nat := 136141370027189743286225

theorem tailTrace_7158628 : CollatzResearch.WordTrace tailWord_7158628 prefixEnd_7158628 136141370027189743286225 := by
  unfold tailWord_7158628
  simp only [CollatzResearch.WordTrace]
  refine ⟨130548306554760413585822269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174064408739680551447763025 130548306554760413585822269)
  ·
    refine ⟨48955614958035155094683351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130548306554760413585822269 48955614958035155094683351)
    ·
      refine ⟨73433422437052732642025027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48955614958035155094683351 73433422437052732642025027)
      ·
        refine ⟨110150133655579098963037541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73433422437052732642025027 110150133655579098963037541)
        ·
          refine ⟨20653150060421081055569539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110150133655579098963037541 20653150060421081055569539)
          ·
            refine ⟨30979725090631621583354309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20653150060421081055569539 30979725090631621583354309)
            ·
              refine ⟨5808698454493429046878933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30979725090631621583354309 5808698454493429046878933)
              ·
                refine ⟨136141370027189743286225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5808698454493429046878933 136141370027189743286225)
                ·
                  rfl

theorem cell23_7158628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 7].length) (baseStart_7158628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158628 prefixEnd_7158628 := by exact prefixLift 7158628
  have htrace : WordTrace (prefixWord ++ tailWord_7158628) baseStart_7158628 baseEnd_7158628 := by
    simpa [prefixWord, tailWord_7158628, baseEnd_7158628] using wordTrace_append hprefix tailTrace_7158628
  have hstable : (prefixWord ++ tailWord_7158628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158628).length < 2 ^ (prefixWord ++ tailWord_7158628).sum := by decide
  have hdescent : baseEnd_7158628 < baseStart_7158628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158682 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2]
def baseStart_7158682 : Nat := 118140960795 + 7158682 * 2 ^ 59
def prefixEnd_7158682 : Nat := 4983230072969 + 3 ^ 40 * 7158682 * 2
def baseEnd_7158682 : Nat := 3675844718689465857452827

theorem tailTrace_7158682 : CollatzResearch.WordTrace tailWord_7158682 prefixEnd_7158682 3675844718689465857452827 := by
  unfold tailWord_7158682
  simp only [CollatzResearch.WordTrace]
  refine ⟨65274645662831298598527575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174065721767550129596073533 65274645662831298598527575)
  ·
    refine ⟨97911968494246947897791363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65274645662831298598527575 97911968494246947897791363)
    ·
      refine ⟨146867952741370421846687045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97911968494246947897791363 146867952741370421846687045)
      ·
        refine ⟨27537741139006954096253821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146867952741370421846687045 27537741139006954096253821)
        ·
          refine ⟨10326652927127607786095183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27537741139006954096253821 10326652927127607786095183)
          ·
            refine ⟨15489979390691411679142775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10326652927127607786095183 15489979390691411679142775)
            ·
              refine ⟨23234969086037117518714163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15489979390691411679142775 23234969086037117518714163)
              ·
                refine ⟨34852453629055676278071245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23234969086037117518714163 34852453629055676278071245)
                ·
                  refine ⟨13069670110895878604276717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34852453629055676278071245 13069670110895878604276717)
                  ·
                    refine ⟨4901126291585954476603769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13069670110895878604276717 4901126291585954476603769)
                    ·
                      refine ⟨3675844718689465857452827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901126291585954476603769 3675844718689465857452827)
                      ·
                        rfl

theorem cell23_7158682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_7158682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158682 prefixEnd_7158682 := by exact prefixLift 7158682
  have htrace : WordTrace (prefixWord ++ tailWord_7158682) baseStart_7158682 baseEnd_7158682 := by
    simpa [prefixWord, tailWord_7158682, baseEnd_7158682] using wordTrace_append hprefix tailTrace_7158682
  have hstable : (prefixWord ++ tailWord_7158682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158682).length < 2 ^ (prefixWord ++ tailWord_7158682).sum := by decide
  have hdescent : baseEnd_7158682 < baseStart_7158682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158711 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_7158711 : Nat := 118140960795 + 7158711 * 2 ^ 59
def prefixEnd_7158711 : Nat := 4983230072969 + 3 ^ 40 * 7158711 * 2
def baseEnd_7158711 : Nat := 3675859609628446243990193

theorem tailTrace_7158711 : CollatzResearch.WordTrace tailWord_7158711 prefixEnd_7158711 3675859609628446243990193 := by
  unfold tailWord_7158711
  simp only [CollatzResearch.WordTrace]
  refine ⟨261099640368220132346915987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174066426912146754897943991 261099640368220132346915987)
  ·
    refine ⟨391649460552330198520373981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261099640368220132346915987 391649460552330198520373981)
    ·
      refine ⟨146868547707123824445140243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391649460552330198520373981 146868547707123824445140243)
      ·
        refine ⟨220302821560685736667710365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146868547707123824445140243 220302821560685736667710365)
        ·
          refine ⟨82613558085257151250391387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220302821560685736667710365 82613558085257151250391387)
          ·
            refine ⟨123920337127885726875587081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82613558085257151250391387 123920337127885726875587081)
            ·
              refine ⟨92940252845914295156690311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123920337127885726875587081 92940252845914295156690311)
              ·
                refine ⟨139410379268871442735035467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92940252845914295156690311 139410379268871442735035467)
                ·
                  refine ⟨209115568903307164102553201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139410379268871442735035467 209115568903307164102553201)
                  ·
                    refine ⟨156836676677480373076914901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 209115568903307164102553201 156836676677480373076914901)
                    ·
                      refine ⟨3675859609628446243990193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156836676677480373076914901 3675859609628446243990193)
                      ·
                        rfl

theorem cell23_7158711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_7158711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158711 prefixEnd_7158711 := by exact prefixLift 7158711
  have htrace : WordTrace (prefixWord ++ tailWord_7158711) baseStart_7158711 baseEnd_7158711 := by
    simpa [prefixWord, tailWord_7158711, baseEnd_7158711] using wordTrace_append hprefix tailTrace_7158711
  have hstable : (prefixWord ++ tailWord_7158711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158711).length < 2 ^ (prefixWord ++ tailWord_7158711).sum := by decide
  have hdescent : baseEnd_7158711 < baseStart_7158711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158712 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 2, 2, 2]
def baseStart_7158712 : Nat := 118140960795 + 7158712 * 2 ^ 59
def prefixEnd_7158712 : Nat := 4983230072969 + 3 ^ 40 * 7158712 * 2
def baseEnd_7158712 : Nat := 3675860123109100740077689

theorem tailTrace_7158712 : CollatzResearch.WordTrace tailWord_7158712 prefixEnd_7158712 3675860123109100740077689 := by
  unfold tailWord_7158712
  simp only [CollatzResearch.WordTrace]
  refine ⟨130549838420608254758851195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174066451227477673011801593 130549838420608254758851195)
  ·
    refine ⟨195824757630912382138276793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130549838420608254758851195 195824757630912382138276793)
    ·
      refine ⟨146868568223184286603707595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195824757630912382138276793 146868568223184286603707595)
      ·
        refine ⟨220302852334776429905561393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146868568223184286603707595 220302852334776429905561393)
        ·
          refine ⟨165227139251082322429171045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220302852334776429905561393 165227139251082322429171045)
          ·
            refine ⟨30980088609577935455469571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165227139251082322429171045 30980088609577935455469571)
            ·
              refine ⟨46470132914366903183204357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30980088609577935455469571 46470132914366903183204357)
              ·
                refine ⟨8713149921443794346850817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46470132914366903183204357 8713149921443794346850817)
                ·
                  refine ⟨6534862441082845760138113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8713149921443794346850817 6534862441082845760138113)
                  ·
                    refine ⟨4901146830812134320103585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6534862441082845760138113 4901146830812134320103585)
                    ·
                      refine ⟨3675860123109100740077689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901146830812134320103585 3675860123109100740077689)
                      ·
                        rfl

theorem cell23_7158712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_7158712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158712 prefixEnd_7158712 := by exact prefixLift 7158712
  have htrace : WordTrace (prefixWord ++ tailWord_7158712) baseStart_7158712 baseEnd_7158712 := by
    simpa [prefixWord, tailWord_7158712, baseEnd_7158712] using wordTrace_append hprefix tailTrace_7158712
  have hstable : (prefixWord ++ tailWord_7158712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158712).length < 2 ^ (prefixWord ++ tailWord_7158712).sum := by decide
  have hdescent : baseEnd_7158712 < baseStart_7158712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158718 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_7158718 : Nat := 118140960795 + 7158718 * 2 ^ 59
def prefixEnd_7158718 : Nat := 4983230072969 + 3 ^ 40 * 7158718 * 2
def baseEnd_7158718 : Nat := 408429244888114190733629

theorem tailTrace_7158718 : CollatzResearch.WordTrace tailWord_7158718 prefixEnd_7158718 408429244888114190733629 := by
  unfold tailWord_7158718
  simp only [CollatzResearch.WordTrace]
  refine ⟨32637486959899346567802601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174066597119463181694947205 32637486959899346567802601)
  ·
    refine ⟨24478115219924509925851951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32637486959899346567802601 24478115219924509925851951)
    ·
      refine ⟨36717172829886764888777927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24478115219924509925851951 36717172829886764888777927)
      ·
        refine ⟨55075759244830147333166891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36717172829886764888777927 55075759244830147333166891)
        ·
          refine ⟨82613638867245220999750337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55075759244830147333166891 82613638867245220999750337)
          ·
            refine ⟨61960229150433915749812753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82613638867245220999750337 61960229150433915749812753)
            ·
              refine ⟨46470171862825436812359565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61960229150433915749812753 46470171862825436812359565)
              ·
                refine ⟨17426314448559538804634837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46470171862825436812359565 17426314448559538804634837)
                ·
                  refine ⟨408429244888114190733629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17426314448559538804634837 408429244888114190733629)
                  ·
                    rfl

theorem cell23_7158718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_7158718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158718 prefixEnd_7158718 := by exact prefixLift 7158718
  have htrace : WordTrace (prefixWord ++ tailWord_7158718) baseStart_7158718 baseEnd_7158718 := by
    simpa [prefixWord, tailWord_7158718, baseEnd_7158718] using wordTrace_append hprefix tailTrace_7158718
  have hstable : (prefixWord ++ tailWord_7158718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158718).length < 2 ^ (prefixWord ++ tailWord_7158718).sum := by decide
  have hdescent : baseEnd_7158718 < baseStart_7158718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158761 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 3, 10]
def baseStart_7158761 : Nat := 118140960795 + 7158761 * 2 ^ 59
def prefixEnd_7158761 : Nat := 4983230072969 + 3 ^ 40 * 7158761 * 2
def baseEnd_7158761 : Nat := 1225295094553723682788321

theorem tailTrace_7158761 : CollatzResearch.WordTrace tailWord_7158761 prefixEnd_7158761 1225295094553723682788321 := by
  unfold tailWord_7158761
  simp only [CollatzResearch.WordTrace]
  refine ⟨261101464018038990886236137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174067642678692660590824091 261101464018038990886236137)
  ·
    refine ⟨195826098013529243164677103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261101464018038990886236137 195826098013529243164677103)
    ·
      refine ⟨293739147020293864747015655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195826098013529243164677103 293739147020293864747015655)
      ·
        refine ⟨440608720530440797120523483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293739147020293864747015655 440608720530440797120523483)
        ·
          refine ⟨660913080795661195680785225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440608720530440797120523483 660913080795661195680785225)
          ·
            refine ⟨495684810596745896760588919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660913080795661195680785225 495684810596745896760588919)
            ·
              refine ⟨743527215895118845140883379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495684810596745896760588919 743527215895118845140883379)
              ·
                refine ⟨1115290823842678267711325069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743527215895118845140883379 1115290823842678267711325069)
                ·
                  refine ⟨418234058941004350391746901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115290823842678267711325069 418234058941004350391746901)
                  ·
                    refine ⟨1225295094553723682788321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 418234058941004350391746901 1225295094553723682788321)
                    ·
                      rfl

theorem cell23_7158761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_7158761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158761 prefixEnd_7158761 := by exact prefixLift 7158761
  have htrace : WordTrace (prefixWord ++ tailWord_7158761) baseStart_7158761 baseEnd_7158761 := by
    simpa [prefixWord, tailWord_7158761, baseEnd_7158761] using wordTrace_append hprefix tailTrace_7158761
  have hstable : (prefixWord ++ tailWord_7158761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158761).length < 2 ^ (prefixWord ++ tailWord_7158761).sum := by decide
  have hdescent : baseEnd_7158761 < baseStart_7158761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158768 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 4]
def baseStart_7158768 : Nat := 118140960795 + 7158768 * 2 ^ 59
def prefixEnd_7158768 : Nat := 4983230072969 + 3 ^ 40 * 7158768 * 2
def baseEnd_7158768 : Nat := 3675888878025752520977431

theorem tailTrace_7158768 : CollatzResearch.WordTrace tailWord_7158768 prefixEnd_7158768 3675888878025752520977431 := by
  unfold tailWord_7158768
  simp only [CollatzResearch.WordTrace]
  refine ⟨130550859664506815540870479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174067812886009087387827305 130550859664506815540870479)
  ·
    refine ⟨195826289496760223311305719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130550859664506815540870479 195826289496760223311305719)
    ·
      refine ⟨293739434245140334966958579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195826289496760223311305719 293739434245140334966958579)
      ·
        refine ⟨440609151367710502450437869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293739434245140334966958579 440609151367710502450437869)
        ·
          refine ⟨165228431762891438418914201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440609151367710502450437869 165228431762891438418914201)
          ·
            refine ⟨123921323822168578814185651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165228431762891438418914201 123921323822168578814185651)
            ·
              refine ⟨185881985733252868221278477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123921323822168578814185651 185881985733252868221278477)
              ·
                refine ⟨69705744649969825582979429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185881985733252868221278477 69705744649969825582979429)
                ·
                  refine ⟨13069827121869342296808643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69705744649969825582979429 13069827121869342296808643)
                  ·
                    refine ⟨19604740682804013445212965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13069827121869342296808643 19604740682804013445212965)
                    ·
                      refine ⟨3675888878025752520977431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19604740682804013445212965 3675888878025752520977431)
                      ·
                        rfl

theorem cell23_7158768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_7158768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158768 prefixEnd_7158768 := by exact prefixLift 7158768
  have htrace : WordTrace (prefixWord ++ tailWord_7158768) baseStart_7158768 baseEnd_7158768 := by
    simpa [prefixWord, tailWord_7158768, baseEnd_7158768] using wordTrace_append hprefix tailTrace_7158768
  have hstable : (prefixWord ++ tailWord_7158768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158768).length < 2 ^ (prefixWord ++ tailWord_7158768).sum := by decide
  have hdescent : baseEnd_7158768 < baseStart_7158768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158795 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 3, 4]
def baseStart_7158795 : Nat := 118140960795 + 7158795 * 2 ^ 59
def prefixEnd_7158795 : Nat := 4983230072969 + 3 ^ 40 * 7158795 * 2
def baseEnd_7158795 : Nat := 1225300914001141305113269

theorem tailTrace_7158795 : CollatzResearch.WordTrace tailWord_7158795 prefixEnd_7158795 1225300914001141305113269 := by
  unfold tailWord_7158795
  simp only [CollatzResearch.WordTrace]
  refine ⟨261102704099915814692973839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174068469399943876461982559 261102704099915814692973839)
  ·
    refine ⟨391654056149873722039460759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261102704099915814692973839 391654056149873722039460759)
    ·
      refine ⟨587481084224810583059191139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391654056149873722039460759 587481084224810583059191139)
      ·
        refine ⟨881221626337215874588786709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587481084224810583059191139 881221626337215874588786709)
        ·
          refine ⟨41307263734556994121349377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 881221626337215874588786709 41307263734556994121349377)
          ·
            refine ⟨30980447800917745591012033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41307263734556994121349377 30980447800917745591012033)
            ·
              refine ⟨23235335850688309193259025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30980447800917745591012033 23235335850688309193259025)
              ·
                refine ⟨17426501888016231894944269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23235335850688309193259025 17426501888016231894944269)
                ·
                  refine ⟨6534938208006086960604101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17426501888016231894944269 6534938208006086960604101)
                  ·
                    refine ⟨1225300914001141305113269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6534938208006086960604101 1225300914001141305113269)
                    ·
                      rfl

theorem cell23_7158795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 4].length) (baseStart_7158795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158795 prefixEnd_7158795 := by exact prefixLift 7158795
  have htrace : WordTrace (prefixWord ++ tailWord_7158795) baseStart_7158795 baseEnd_7158795 := by
    simpa [prefixWord, tailWord_7158795, baseEnd_7158795] using wordTrace_append hprefix tailTrace_7158795
  have hstable : (prefixWord ++ tailWord_7158795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158795).length < 2 ^ (prefixWord ++ tailWord_7158795).sum := by decide
  have hdescent : baseEnd_7158795 < baseStart_7158795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158805 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_7158805 : Nat := 118140960795 + 7158805 * 2 ^ 59
def prefixEnd_7158805 : Nat := 4983230072969 + 3 ^ 40 * 7158805 * 2
def baseEnd_7158805 : Nat := 3675907876809968876214761

theorem tailTrace_7158805 : CollatzResearch.WordTrace tailWord_7158805 prefixEnd_7158805 3675907876809968876214761 := by
  unfold tailWord_7158805
  simp only [CollatzResearch.WordTrace]
  refine ⟨261103068829879586400837869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174068712553253057600558579 261103068829879586400837869)
  ·
    refine ⟨97913650811204844900314201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261103068829879586400837869 97913650811204844900314201)
    ·
      refine ⟨73435238108403633675235651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97913650811204844900314201 73435238108403633675235651)
      ·
        refine ⟨110152857162605450512853477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73435238108403633675235651 110152857162605450512853477)
        ·
          refine ⟨20653660717988521971160027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110152857162605450512853477 20653660717988521971160027)
          ·
            refine ⟨30980491076982782956740041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20653660717988521971160027 30980491076982782956740041)
            ·
              refine ⟨23235368307737087217555031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30980491076982782956740041 23235368307737087217555031)
              ·
                refine ⟨34853052461605630826332547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23235368307737087217555031 34853052461605630826332547)
                ·
                  refine ⟨52279578692408446239498821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34853052461605630826332547 52279578692408446239498821)
                  ·
                    refine ⟨9802421004826583669906029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52279578692408446239498821 9802421004826583669906029)
                    ·
                      refine ⟨3675907876809968876214761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9802421004826583669906029 3675907876809968876214761)
                      ·
                        rfl

theorem cell23_7158805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_7158805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158805 prefixEnd_7158805 := by exact prefixLift 7158805
  have htrace : WordTrace (prefixWord ++ tailWord_7158805) baseStart_7158805 baseEnd_7158805 := by
    simpa [prefixWord, tailWord_7158805, baseEnd_7158805] using wordTrace_append hprefix tailTrace_7158805
  have hstable : (prefixWord ++ tailWord_7158805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158805).length < 2 ^ (prefixWord ++ tailWord_7158805).sum := by decide
  have hdescent : baseEnd_7158805 < baseStart_7158805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158808 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 8]
def baseStart_7158808 : Nat := 118140960795 + 7158808 * 2 ^ 59
def prefixEnd_7158808 : Nat := 4983230072969 + 3 ^ 40 * 7158808 * 2
def baseEnd_7158808 : Nat := 408434379694659151608583

theorem tailTrace_7158808 : CollatzResearch.WordTrace tailWord_7158808 prefixEnd_7158808 408434379694659151608583 := by
  unfold tailWord_7158808
  simp only [CollatzResearch.WordTrace]
  refine ⟨130551589124434358956598539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174068785499245811942131385 130551589124434358956598539)
  ·
    refine ⟨195827383686651538434897809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130551589124434358956598539 195827383686651538434897809)
    ·
      refine ⟨146870537764988653826173357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195827383686651538434897809 146870537764988653826173357)
      ·
        refine ⟨55076451661870745184815009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146870537764988653826173357 55076451661870745184815009)
        ·
          refine ⟨41307338746403058888611257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55076451661870745184815009 41307338746403058888611257)
          ·
            refine ⟨30980504059802294166458443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41307338746403058888611257 30980504059802294166458443)
            ·
              refine ⟨46470756089703441249687665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30980504059802294166458443 46470756089703441249687665)
              ·
                refine ⟨34853067067277580937265749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46470756089703441249687665 34853067067277580937265749)
                ·
                  refine ⟨408434379694659151608583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34853067067277580937265749 408434379694659151608583)
                  ·
                    rfl

theorem cell23_7158808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 8].length) (baseStart_7158808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158808 prefixEnd_7158808 := by exact prefixLift 7158808
  have htrace : WordTrace (prefixWord ++ tailWord_7158808) baseStart_7158808 baseEnd_7158808 := by
    simpa [prefixWord, tailWord_7158808, baseEnd_7158808] using wordTrace_append hprefix tailTrace_7158808
  have hstable : (prefixWord ++ tailWord_7158808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158808).length < 2 ^ (prefixWord ++ tailWord_7158808).sum := by decide
  have hdescent : baseEnd_7158808 < baseStart_7158808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158855 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 3, 5]
def baseStart_7158855 : Nat := 118140960795 + 7158855 * 2 ^ 59
def prefixEnd_7158855 : Nat := 4983230072969 + 3 ^ 40 * 7158855 * 2
def baseEnd_7158855 : Nat := 1225311183614231226863177

theorem tailTrace_7158855 : CollatzResearch.WordTrace tailWord_7158855 prefixEnd_7158855 1225311183614231226863177 := by
  unfold tailWord_7158855
  simp only [CollatzResearch.WordTrace]
  refine ⟨261104892479698444940158019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174069928319798963293438679 261104892479698444940158019)
  ·
    refine ⟨391657338719547667410237029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261104892479698444940158019 391657338719547667410237029)
    ·
      refine ⟨73435751009915187639419443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391657338719547667410237029 73435751009915187639419443)
      ·
        refine ⟨110153626514872781459129165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73435751009915187639419443 110153626514872781459129165)
        ·
          refine ⟨41307609943077293047173437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110153626514872781459129165 41307609943077293047173437)
          ·
            refine ⟨15490353728653984892690039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41307609943077293047173437 15490353728653984892690039)
            ·
              refine ⟨23235530592980977339035059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15490353728653984892690039 23235530592980977339035059)
              ·
                refine ⟨34853295889471466008552589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23235530592980977339035059 34853295889471466008552589)
                ·
                  refine ⟨13069985958551799753207221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34853295889471466008552589 13069985958551799753207221)
                  ·
                    refine ⟨1225311183614231226863177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13069985958551799753207221 1225311183614231226863177)
                    ·
                      rfl

theorem cell23_7158855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_7158855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158855 prefixEnd_7158855 := by exact prefixLift 7158855
  have htrace : WordTrace (prefixWord ++ tailWord_7158855) baseStart_7158855 baseEnd_7158855 := by
    simpa [prefixWord, tailWord_7158855, baseEnd_7158855] using wordTrace_append hprefix tailTrace_7158855
  have hstable : (prefixWord ++ tailWord_7158855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158855).length < 2 ^ (prefixWord ++ tailWord_7158855).sum := by decide
  have hdescent : baseEnd_7158855 < baseStart_7158855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158869 : List Nat := [1, 3, 2, 2, 1, 2, 2, 5, 1, 1, 3]
def baseStart_7158869 : Nat := 118140960795 + 7158869 * 2 ^ 59
def prefixEnd_7158869 : Nat := 4983230072969 + 3 ^ 40 * 7158869 * 2
def baseEnd_7158869 : Nat := 3675940739571856625814467

theorem tailTrace_7158869 : CollatzResearch.WordTrace tailWord_7158869 prefixEnd_7158869 3675940739571856625814467 := by
  unfold tailWord_7158869
  simp only [CollatzResearch.WordTrace]
  refine ⟨261105403101647725331167661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174070268734431816887445107 261105403101647725331167661)
  ·
    refine ⟨97914526163117896999187873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261105403101647725331167661 97914526163117896999187873)
    ·
      refine ⟨73435894622338422749390905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97914526163117896999187873 73435894622338422749390905)
      ·
        refine ⟨55076920966753817062043179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73435894622338422749390905 55076920966753817062043179)
        ·
          refine ⟨82615381450130725593064769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55076920966753817062043179 82615381450130725593064769)
          ·
            refine ⟨61961536087598044194798577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82615381450130725593064769 61961536087598044194798577)
            ·
              refine ⟨46471152065698533146098933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61961536087598044194798577 46471152065698533146098933)
              ·
                refine ⟨4356670506159237482446775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46471152065698533146098933 4356670506159237482446775)
                ·
                  refine ⟨6535005759238856223670163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356670506159237482446775 6535005759238856223670163)
                  ·
                    refine ⟨9802508638858284335505245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6535005759238856223670163 9802508638858284335505245)
                    ·
                      refine ⟨3675940739571856625814467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9802508638858284335505245 3675940739571856625814467)
                      ·
                        rfl

theorem cell23_7158869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_7158869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158869 prefixEnd_7158869 := by exact prefixLift 7158869
  have htrace : WordTrace (prefixWord ++ tailWord_7158869) baseStart_7158869 baseEnd_7158869 := by
    simpa [prefixWord, tailWord_7158869, baseEnd_7158869] using wordTrace_append hprefix tailTrace_7158869
  have hstable : (prefixWord ++ tailWord_7158869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158869).length < 2 ^ (prefixWord ++ tailWord_7158869).sum := by decide
  have hdescent : baseEnd_7158869 < baseStart_7158869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158872 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 1, 5]
def baseStart_7158872 : Nat := 118140960795 + 7158872 * 2 ^ 59
def prefixEnd_7158872 : Nat := 4983230072969 + 3 ^ 40 * 7158872 * 2
def baseEnd_7158872 : Nat := 1225314093337940038025651

theorem tailTrace_7158872 : CollatzResearch.WordTrace tailWord_7158872 prefixEnd_7158872 1225314093337940038025651 := by
  unfold tailWord_7158872
  simp only [CollatzResearch.WordTrace]
  refine ⟨130552756260318428421763435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174070341680424571229017913 130552756260318428421763435)
  ·
    refine ⟨195829134390477642632645153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130552756260318428421763435 195829134390477642632645153)
    ·
      refine ⟨146871850792858231974483865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195829134390477642632645153 146871850792858231974483865)
      ·
        refine ⟨110153888094643673980862899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146871850792858231974483865 110153888094643673980862899)
        ·
          refine ⟨165230832141965510971294349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110153888094643673980862899 165230832141965510971294349)
          ·
            refine ⟨61961562053237066614235381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165230832141965510971294349 61961562053237066614235381)
            ·
              refine ⟨5808896442490974995084567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61961562053237066614235381 5808896442490974995084567)
              ·
                refine ⟨8713344663736462492626851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5808896442490974995084567 8713344663736462492626851)
                ·
                  refine ⟨13070016995604693738940277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8713344663736462492626851 13070016995604693738940277)
                  ·
                    refine ⟨1225314093337940038025651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13070016995604693738940277 1225314093337940038025651)
                    ·
                      rfl

theorem cell23_7158872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_7158872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158872 prefixEnd_7158872 := by exact prefixLift 7158872
  have htrace : WordTrace (prefixWord ++ tailWord_7158872) baseStart_7158872 baseEnd_7158872 := by
    simpa [prefixWord, tailWord_7158872, baseEnd_7158872] using wordTrace_append hprefix tailTrace_7158872
  have hstable : (prefixWord ++ tailWord_7158872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158872).length < 2 ^ (prefixWord ++ tailWord_7158872).sum := by decide
  have hdescent : baseEnd_7158872 < baseStart_7158872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158895 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 3]
def baseStart_7158895 : Nat := 118140960795 + 7158895 * 2 ^ 59
def prefixEnd_7158895 : Nat := 4983230072969 + 3 ^ 40 * 7158895 * 2
def baseEnd_7158895 : Nat := 3675954090068873524089347

theorem tailTrace_7158895 : CollatzResearch.WordTrace tailWord_7158895 prefixEnd_7158895 3675954090068873524089347 := by
  unfold tailWord_7158895
  simp only [CollatzResearch.WordTrace]
  refine ⟨261106351399553531771614139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174070900933035687847742759 261106351399553531771614139)
  ·
    refine ⟨391659527099330297657421209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261106351399553531771614139 391659527099330297657421209)
    ·
      refine ⟨293744645324497723243065907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391659527099330297657421209 293744645324497723243065907)
      ·
        refine ⟨440616967986746584864598861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293744645324497723243065907 440616967986746584864598861)
        ·
          refine ⟨165231362995029969324224573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440616967986746584864598861 165231362995029969324224573)
          ·
            refine ⟨61961761123136238496584215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165231362995029969324224573 61961761123136238496584215)
            ·
              refine ⟨92942641684704357744876323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61961761123136238496584215 92942641684704357744876323)
              ·
                refine ⟨139413962527056536617314485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92942641684704357744876323 139413962527056536617314485)
                ·
                  refine ⟨13070058986911550307873233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139413962527056536617314485 13070058986911550307873233)
                  ·
                    refine ⟨9802544240183662730904925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13070058986911550307873233 9802544240183662730904925)
                    ·
                      refine ⟨3675954090068873524089347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9802544240183662730904925 3675954090068873524089347)
                      ·
                        rfl

theorem cell23_7158895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 3].length) (baseStart_7158895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158895 prefixEnd_7158895 := by exact prefixLift 7158895
  have htrace : WordTrace (prefixWord ++ tailWord_7158895) baseStart_7158895 baseEnd_7158895 := by
    simpa [prefixWord, tailWord_7158895, baseEnd_7158895] using wordTrace_append hprefix tailTrace_7158895
  have hstable : (prefixWord ++ tailWord_7158895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158895).length < 2 ^ (prefixWord ++ tailWord_7158895).sum := by decide
  have hdescent : baseEnd_7158895 < baseStart_7158895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158902 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_7158902 : Nat := 118140960795 + 7158902 * 2 ^ 59
def prefixEnd_7158902 : Nat := 4983230072969 + 3 ^ 40 * 7158902 * 2
def baseEnd_7158902 : Nat := 1225319228144484998900605

theorem tailTrace_7158902 : CollatzResearch.WordTrace tailWord_7158902 prefixEnd_7158902 1225319228144484998900605 := by
  unfold tailWord_7158902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16319162919408010747944935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174071071140352114644745973 16319162919408010747944935)
  ·
    refine ⟨24478744379112016121917403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16319162919408010747944935 24478744379112016121917403)
    ·
      refine ⟨36718116568668024182876105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24478744379112016121917403 36718116568668024182876105)
      ·
        refine ⟨27538587426501018137157079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36718116568668024182876105 27538587426501018137157079)
        ·
          refine ⟨41307881139751527205735619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27538587426501018137157079 41307881139751527205735619)
          ·
            refine ⟨61961821709627290808603429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41307881139751527205735619 61961821709627290808603429)
            ·
              refine ⟨11617841570555117026613143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61961821709627290808603429 11617841570555117026613143)
              ·
                refine ⟨17426762355832675539919715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11617841570555117026613143 17426762355832675539919715)
                ·
                  refine ⟨26140143533749013309879573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17426762355832675539919715 26140143533749013309879573)
                  ·
                    refine ⟨1225319228144484998900605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26140143533749013309879573 1225319228144484998900605)
                    ·
                      rfl

theorem cell23_7158902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_7158902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158902 prefixEnd_7158902 := by exact prefixLift 7158902
  have htrace : WordTrace (prefixWord ++ tailWord_7158902) baseStart_7158902 baseEnd_7158902 := by
    simpa [prefixWord, tailWord_7158902, baseEnd_7158902] using wordTrace_append hprefix tailTrace_7158902
  have hstable : (prefixWord ++ tailWord_7158902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158902).length < 2 ^ (prefixWord ++ tailWord_7158902).sum := by decide
  have hdescent : baseEnd_7158902 < baseStart_7158902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158909 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 3, 2, 2]
def baseStart_7158909 : Nat := 118140960795 + 7158909 * 2 ^ 59
def prefixEnd_7158909 : Nat := 4983230072969 + 3 ^ 40 * 7158909 * 2
def baseEnd_7158909 : Nat := 3675961278798036469314283

theorem tailTrace_7158909 : CollatzResearch.WordTrace tailWord_7158909 prefixEnd_7158909 3675961278798036469314283 := by
  unfold tailWord_7158909
  simp only [CollatzResearch.WordTrace]
  refine ⟨261106862021502812162623781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174071241347668541441749187 261106862021502812162623781)
  ·
    refine ⟨48957536629031777280491959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261106862021502812162623781 48957536629031777280491959)
    ·
      refine ⟨73436304943547665920737939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48957536629031777280491959 73436304943547665920737939)
      ·
        refine ⟨110154457415321498881106909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73436304943547665920737939 110154457415321498881106909)
        ·
          refine ⟨41307921530745562080415091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110154457415321498881106909 41307921530745562080415091)
          ·
            refine ⟨61961882296118343120622637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41307921530745562080415091 61961882296118343120622637)
            ·
              refine ⟨23235705861044378670233489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61961882296118343120622637 23235705861044378670233489)
              ·
                refine ⟨17426779395783284002675117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23235705861044378670233489 17426779395783284002675117)
                ·
                  refine ⟨6535042273418731501003169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17426779395783284002675117 6535042273418731501003169)
                  ·
                    refine ⟨4901281705064048625752377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6535042273418731501003169 4901281705064048625752377)
                    ·
                      refine ⟨3675961278798036469314283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901281705064048625752377 3675961278798036469314283)
                      ·
                        rfl

theorem cell23_7158909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_7158909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158909 prefixEnd_7158909 := by exact prefixLift 7158909
  have htrace : WordTrace (prefixWord ++ tailWord_7158909) baseStart_7158909 baseEnd_7158909 := by
    simpa [prefixWord, tailWord_7158909, baseEnd_7158909] using wordTrace_append hprefix tailTrace_7158909
  have hstable : (prefixWord ++ tailWord_7158909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158909).length < 2 ^ (prefixWord ++ tailWord_7158909).sum := by decide
  have hdescent : baseEnd_7158909 < baseStart_7158909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158915 : List Nat := [1, 1, 1, 3, 3, 2, 5, 7]
def baseStart_7158915 : Nat := 118140960795 + 7158915 * 2 ^ 59
def prefixEnd_7158915 : Nat := 4983230072969 + 3 ^ 40 * 7158915 * 2
def baseEnd_7158915 : Nat := 136146828136369016512565

theorem tailTrace_7158915 : CollatzResearch.WordTrace tailWord_7158915 prefixEnd_7158915 136146828136369016512565 := by
  unfold tailWord_7158915
  simp only [CollatzResearch.WordTrace]
  refine ⟨261107080859481075187342199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174071387239654050124894799 261107080859481075187342199)
  ·
    refine ⟨391660621289221612781013299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261107080859481075187342199 391660621289221612781013299)
    ·
      refine ⟨587490931933832419171519949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391660621289221612781013299 587490931933832419171519949)
      ·
        refine ⟨220309099475187157189319981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587490931933832419171519949 220309099475187157189319981)
        ·
          refine ⟨82615912303195183945994993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220309099475187157189319981 82615912303195183945994993)
          ·
            refine ⟨61961934227396387959496245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82615912303195183945994993 61961934227396387959496245)
            ·
              refine ⟨5808931333818411371202773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61961934227396387959496245 5808931333818411371202773)
              ·
                refine ⟨136146828136369016512565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5808931333818411371202773 136146828136369016512565)
                ·
                  rfl

theorem cell23_7158915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 7].length) (baseStart_7158915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158915 prefixEnd_7158915 := by exact prefixLift 7158915
  have htrace : WordTrace (prefixWord ++ tailWord_7158915) baseStart_7158915 baseEnd_7158915 := by
    simpa [prefixWord, tailWord_7158915, baseEnd_7158915] using wordTrace_append hprefix tailTrace_7158915
  have hstable : (prefixWord ++ tailWord_7158915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158915).length < 2 ^ (prefixWord ++ tailWord_7158915).sum := by decide
  have hdescent : baseEnd_7158915 < baseStart_7158915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158926 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4]
def baseStart_7158926 : Nat := 118140960795 + 7158926 * 2 ^ 59
def prefixEnd_7158926 : Nat := 4983230072969 + 3 ^ 40 * 7158926 * 2
def baseEnd_7158926 : Nat := 3675970007969162902801705

theorem tailTrace_7158926 : CollatzResearch.WordTrace tailWord_7158926 prefixEnd_7158926 3675970007969162902801705 := by
  unfold tailWord_7158926
  simp only [CollatzResearch.WordTrace]
  refine ⟨32638435257805153008249079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174071654708294149377328421 32638435257805153008249079)
  ·
    refine ⟨48957652886707729512373619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32638435257805153008249079 48957652886707729512373619)
    ·
      refine ⟨73436479330061594268560429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48957652886707729512373619 73436479330061594268560429)
      ·
        refine ⟨27538679748773097850710161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73436479330061594268560429 27538679748773097850710161)
        ·
          refine ⟨20654009811579823388032621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27538679748773097850710161 20654009811579823388032621)
          ·
            refine ⟨7745253679342433770512233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20654009811579823388032621 7745253679342433770512233)
            ·
              refine ⟨5808940259506825327884175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7745253679342433770512233 5808940259506825327884175)
              ·
                refine ⟨8713410389260237991826263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5808940259506825327884175 8713410389260237991826263)
                ·
                  refine ⟨13070115583890356987739395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8713410389260237991826263 13070115583890356987739395)
                  ·
                    refine ⟨19605173375835535481609093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13070115583890356987739395 19605173375835535481609093)
                    ·
                      refine ⟨3675970007969162902801705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19605173375835535481609093 3675970007969162902801705)
                      ·
                        rfl

theorem cell23_7158926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_7158926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158926 prefixEnd_7158926 := by exact prefixLift 7158926
  have htrace : WordTrace (prefixWord ++ tailWord_7158926) baseStart_7158926 baseEnd_7158926 := by
    simpa [prefixWord, tailWord_7158926, baseEnd_7158926] using wordTrace_append hprefix tailTrace_7158926
  have hstable : (prefixWord ++ tailWord_7158926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158926).length < 2 ^ (prefixWord ++ tailWord_7158926).sum := by decide
  have hdescent : baseEnd_7158926 < baseStart_7158926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158928 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 1, 9]
def baseStart_7158928 : Nat := 118140960795 + 7158928 * 2 ^ 59
def prefixEnd_7158928 : Nat := 4983230072969 + 3 ^ 40 * 7158928 * 2
def baseEnd_7158928 : Nat := 1225323678310157298325565

theorem tailTrace_7158928 : CollatzResearch.WordTrace tailWord_7158928 prefixEnd_7158928 1225323678310157298325565 := by
  unfold tailWord_7158928
  simp only [CollatzResearch.WordTrace]
  refine ⟨130553777504216989203782719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174071703338955985605043625 130553777504216989203782719)
  ·
    refine ⟨195830666256325483805674079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130553777504216989203782719 195830666256325483805674079)
    ·
      refine ⟨293745999384488225708511119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195830666256325483805674079 293745999384488225708511119)
      ·
        refine ⟨440618999076732338562766679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293745999384488225708511119 440618999076732338562766679)
        ·
          refine ⟨660928498615098507844150019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440618999076732338562766679 660928498615098507844150019)
          ·
            refine ⟨991392747922647761766225029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660928498615098507844150019 991392747922647761766225029)
            ·
              refine ⟨185886140235496455331167193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 991392747922647761766225029 185886140235496455331167193)
              ·
                refine ⟨139414605176622341498375395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185886140235496455331167193 139414605176622341498375395)
                ·
                  refine ⟨209121907764933512247563093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139414605176622341498375395 209121907764933512247563093)
                  ·
                    refine ⟨1225323678310157298325565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 209121907764933512247563093 1225323678310157298325565)
                    ·
                      rfl

theorem cell23_7158928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_7158928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158928 prefixEnd_7158928 := by exact prefixLift 7158928
  have htrace : WordTrace (prefixWord ++ tailWord_7158928) baseStart_7158928 baseEnd_7158928 := by
    simpa [prefixWord, tailWord_7158928, baseEnd_7158928] using wordTrace_append hprefix tailTrace_7158928
  have hstable : (prefixWord ++ tailWord_7158928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158928).length < 2 ^ (prefixWord ++ tailWord_7158928).sum := by decide
  have hdescent : baseEnd_7158928 < baseStart_7158928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158969 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 1, 3, 2]
def baseStart_7158969 : Nat := 118140960795 + 7158969 * 2 ^ 59
def prefixEnd_7158969 : Nat := 4983230072969 + 3 ^ 40 * 7158969 * 2
def baseEnd_7158969 : Nat := 3675992087637306234564007

theorem tailTrace_7158969 : CollatzResearch.WordTrace tailWord_7158969 prefixEnd_7158969 3675992087637306234564007 := by
  unfold tailWord_7158969
  simp only [CollatzResearch.WordTrace]
  refine ⟨261109050401285442409807961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174072700267523628273205307 261109050401285442409807961)
  ·
    refine ⟨195831787800964081807355971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261109050401285442409807961 195831787800964081807355971)
    ·
      refine ⟨293747681701446122711033957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195831787800964081807355971 293747681701446122711033957)
      ·
        refine ⟨55077690319021148008318867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293747681701446122711033957 55077690319021148008318867)
        ·
          refine ⟨82616535478531722012478301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55077690319021148008318867 82616535478531722012478301)
          ·
            refine ⟨30981200804449395754679363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82616535478531722012478301 30981200804449395754679363)
            ·
              refine ⟨46471801206674093632019045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30981200804449395754679363 46471801206674093632019045)
              ·
                refine ⟨8713462726251392556003571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46471801206674093632019045 8713462726251392556003571)
                ·
                  refine ⟨13070194089377088834005357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8713462726251392556003571 13070194089377088834005357)
                  ·
                    refine ⟨4901322783516408312752009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13070194089377088834005357 4901322783516408312752009)
                    ·
                      refine ⟨3675992087637306234564007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901322783516408312752009 3675992087637306234564007)
                      ·
                        rfl

theorem cell23_7158969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_7158969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158969 prefixEnd_7158969 := by exact prefixLift 7158969
  have htrace : WordTrace (prefixWord ++ tailWord_7158969) baseStart_7158969 baseEnd_7158969 := by
    simpa [prefixWord, tailWord_7158969, baseEnd_7158969] using wordTrace_append hprefix tailTrace_7158969
  have hstable : (prefixWord ++ tailWord_7158969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158969).length < 2 ^ (prefixWord ++ tailWord_7158969).sum := by decide
  have hdescent : baseEnd_7158969 < baseStart_7158969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7158999 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 4, 2, 2]
def baseStart_7158999 : Nat := 118140960795 + 7158999 * 2 ^ 59
def prefixEnd_7158999 : Nat := 4983230072969 + 3 ^ 40 * 7158999 * 2
def baseEnd_7158999 : Nat := 3676007492056941117188869

theorem tailTrace_7158999 : CollatzResearch.WordTrace tailWord_7158999 prefixEnd_7158999 3676007492056941117188869 := by
  unfold tailWord_7158999
  simp only [CollatzResearch.WordTrace]
  refine ⟨261110144591176757533400051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174073429727451171688933367 261110144591176757533400051)
  ·
    refine ⟨391665216886765136300100077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261110144591176757533400051 391665216886765136300100077)
    ·
      refine ⟨146874456332536926112537529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391665216886765136300100077 146874456332536926112537529)
      ·
        refine ⟨110155842249402694584403147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146874456332536926112537529 110155842249402694584403147)
        ·
          refine ⟨165233763374104041876604721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110155842249402694584403147 165233763374104041876604721)
          ·
            refine ⟨123925322530578031407453541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165233763374104041876604721 123925322530578031407453541)
            ·
              refine ⟨23235997974483380888897539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123925322530578031407453541 23235997974483380888897539)
              ·
                refine ⟨34853996961725071333346309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23235997974483380888897539 34853996961725071333346309)
                ·
                  refine ⟨6535124430323450875002433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34853996961725071333346309 6535124430323450875002433)
                  ·
                    refine ⟨4901343322742588156251825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6535124430323450875002433 4901343322742588156251825)
                    ·
                      refine ⟨3676007492056941117188869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901343322742588156251825 3676007492056941117188869)
                      ·
                        rfl

theorem cell23_7158999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_7158999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7158999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7158999 prefixEnd_7158999 := by exact prefixLift 7158999
  have htrace : WordTrace (prefixWord ++ tailWord_7158999) baseStart_7158999 baseEnd_7158999 := by
    simpa [prefixWord, tailWord_7158999, baseEnd_7158999] using wordTrace_append hprefix tailTrace_7158999
  have hstable : (prefixWord ++ tailWord_7158999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7158999).length < 2 ^ (prefixWord ++ tailWord_7158999).sum := by decide
  have hdescent : baseEnd_7158999 < baseStart_7158999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7158999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159016 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_7159016 : Nat := 118140960795 + 7159016 * 2 ^ 59
def prefixEnd_7159016 : Nat := 4983230072969 + 3 ^ 40 * 7159016 * 2
def baseEnd_7159016 : Nat := 3676016221228067550676291

theorem tailTrace_7159016 : CollatzResearch.WordTrace tailWord_7159016 prefixEnd_7159016 3676016221228067550676291 := by
  unfold tailWord_7159016
  simp only [CollatzResearch.WordTrace]
  refine ⟨130555382316057584718384451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174073843088076779624512601 130555382316057584718384451)
  ·
    refine ⟨195833073474086377077576677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130555382316057584718384451 195833073474086377077576677)
    ·
      refine ⟨36718701276391195702045627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195833073474086377077576677 36718701276391195702045627)
      ·
        refine ⟨55078051914586793553068441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36718701276391195702045627 55078051914586793553068441)
        ·
          refine ⟨41308538935940095164801331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55078051914586793553068441 41308538935940095164801331)
          ·
            refine ⟨61962808403910142747201997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41308538935940095164801331 61962808403910142747201997)
            ·
              refine ⟨23236053151466303530200749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61962808403910142747201997 23236053151466303530200749)
              ·
                refine ⟨8713519931799863823825281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23236053151466303530200749 8713519931799863823825281)
                ·
                  refine ⟨6535139948849897867868961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8713519931799863823825281 6535139948849897867868961)
                  ·
                    refine ⟨4901354961637423400901721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6535139948849897867868961 4901354961637423400901721)
                    ·
                      refine ⟨3676016221228067550676291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901354961637423400901721 3676016221228067550676291)
                      ·
                        rfl

theorem cell23_7159016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_7159016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159016 prefixEnd_7159016 := by exact prefixLift 7159016
  have htrace : WordTrace (prefixWord ++ tailWord_7159016) baseStart_7159016 baseEnd_7159016 := by
    simpa [prefixWord, tailWord_7159016, baseEnd_7159016] using wordTrace_append hprefix tailTrace_7159016
  have hstable : (prefixWord ++ tailWord_7159016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159016).length < 2 ^ (prefixWord ++ tailWord_7159016).sum := by decide
  have hdescent : baseEnd_7159016 < baseStart_7159016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159045 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_7159045 : Nat := 118140960795 + 7159045 * 2 ^ 59
def prefixEnd_7159045 : Nat := 4983230072969 + 3 ^ 40 * 7159045 * 2
def baseEnd_7159045 : Nat := 3676031112167047937213657

theorem tailTrace_7159045 : CollatzResearch.WordTrace tailWord_7159045 prefixEnd_7159045 3676031112167047937213657 := by
  unfold tailWord_7159045
  simp only [CollatzResearch.WordTrace]
  refine ⟨261111822349010107389574589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174074548232673404926383059 261111822349010107389574589)
  ·
    refine ⟨97916933380878790271090471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261111822349010107389574589 97916933380878790271090471)
    ·
      refine ⟨146875400071318185406635707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97916933380878790271090471 146875400071318185406635707)
      ·
        refine ⟨220313100106977278109953561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146875400071318185406635707 220313100106977278109953561)
        ·
          refine ⟨165234825080232958582465171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220313100106977278109953561 165234825080232958582465171)
          ·
            refine ⟨247852237620349437873697757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165234825080232958582465171 247852237620349437873697757)
            ·
              refine ⟨92944589107631039202636659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247852237620349437873697757 92944589107631039202636659)
              ·
                refine ⟨139416883661446558803954989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92944589107631039202636659 139416883661446558803954989)
                ·
                  refine ⟨52281331373042459551483121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139416883661446558803954989 52281331373042459551483121)
                  ·
                    refine ⟨39210998529781844663612341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52281331373042459551483121 39210998529781844663612341)
                    ·
                      refine ⟨3676031112167047937213657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39210998529781844663612341 3676031112167047937213657)
                      ·
                        rfl

theorem cell23_7159045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_7159045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159045 prefixEnd_7159045 := by exact prefixLift 7159045
  have htrace : WordTrace (prefixWord ++ tailWord_7159045) baseStart_7159045 baseEnd_7159045 := by
    simpa [prefixWord, tailWord_7159045, baseEnd_7159045] using wordTrace_append hprefix tailTrace_7159045
  have hstable : (prefixWord ++ tailWord_7159045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159045).length < 2 ^ (prefixWord ++ tailWord_7159045).sum := by decide
  have hdescent : baseEnd_7159045 < baseStart_7159045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159052 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_7159052 : Nat := 118140960795 + 7159052 * 2 ^ 59
def prefixEnd_7159052 : Nat := 4983230072969 + 3 ^ 40 * 7159052 * 2
def baseEnd_7159052 : Nat := 1225344902177209803275375

theorem tailTrace_7159052 : CollatzResearch.WordTrace tailWord_7159052 prefixEnd_7159052 1225344902177209803275375 := by
  unfold tailWord_7159052
  simp only [CollatzResearch.WordTrace]
  refine ⟨130556038829992373792539705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174074718439989831723386273 130556038829992373792539705)
  ·
    refine ⟨97917029122494280344404779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130556038829992373792539705 97917029122494280344404779)
    ·
      refine ⟨146875543683741420516607169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97917029122494280344404779 146875543683741420516607169)
      ·
        refine ⟨110156657762806065387455377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146875543683741420516607169 110156657762806065387455377)
        ·
          refine ⟨82617493322104549040591533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110156657762806065387455377 82617493322104549040591533)
          ·
            refine ⟨30981559995789205890221825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82617493322104549040591533 30981559995789205890221825)
            ·
              refine ⟨23236169996841904417666369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30981559995789205890221825 23236169996841904417666369)
              ·
                refine ⟨17427127497631428313249777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23236169996841904417666369 17427127497631428313249777)
                ·
                  refine ⟨13070345623223571234937333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17427127497631428313249777 13070345623223571234937333)
                  ·
                    refine ⟨1225344902177209803275375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13070345623223571234937333 1225344902177209803275375)
                    ·
                      rfl

theorem cell23_7159052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_7159052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159052 prefixEnd_7159052 := by exact prefixLift 7159052
  have htrace : WordTrace (prefixWord ++ tailWord_7159052) baseStart_7159052 baseEnd_7159052 := by
    simpa [prefixWord, tailWord_7159052, baseEnd_7159052] using wordTrace_append hprefix tailTrace_7159052
  have hstable : (prefixWord ++ tailWord_7159052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159052).length < 2 ^ (prefixWord ++ tailWord_7159052).sum := by decide
  have hdescent : baseEnd_7159052 < baseStart_7159052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159055 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_7159055 : Nat := 118140960795 + 7159055 * 2 ^ 59
def prefixEnd_7159055 : Nat := 4983230072969 + 3 ^ 40 * 7159055 * 2
def baseEnd_7159055 : Nat := 3676036246973592898088611

theorem tailTrace_7159055 : CollatzResearch.WordTrace tailWord_7159055 prefixEnd_7159055 3676036246973592898088611 := by
  unfold tailWord_7159055
  simp only [CollatzResearch.WordTrace]
  refine ⟨261112187078973879097438619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174074791385982586064959079 261112187078973879097438619)
  ·
    refine ⟨391668280618460818646157929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261112187078973879097438619 391668280618460818646157929)
    ·
      refine ⟨293751210463845613984618447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391668280618460818646157929 293751210463845613984618447)
      ·
        refine ⟨440626815695768420976927671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293751210463845613984618447 440626815695768420976927671)
        ·
          refine ⟨660940223543652631465391507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440626815695768420976927671 660940223543652631465391507)
          ·
            refine ⟨991410335315478947198087261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660940223543652631465391507 991410335315478947198087261)
            ·
              refine ⟨371778875743304605199282723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 991410335315478947198087261 371778875743304605199282723)
              ·
                refine ⟨557668313614956907798924085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371778875743304605199282723 557668313614956907798924085)
                ·
                  refine ⟨52281404401402210106149133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 557668313614956907798924085 52281404401402210106149133)
                  ·
                    refine ⟨19605526650525828789805925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52281404401402210106149133 19605526650525828789805925)
                    ·
                      refine ⟨3676036246973592898088611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19605526650525828789805925 3676036246973592898088611)
                      ·
                        rfl

theorem cell23_7159055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_7159055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159055 prefixEnd_7159055 := by exact prefixLift 7159055
  have htrace : WordTrace (prefixWord ++ tailWord_7159055) baseStart_7159055 baseEnd_7159055 := by
    simpa [prefixWord, tailWord_7159055, baseEnd_7159055] using wordTrace_append hprefix tailTrace_7159055
  have hstable : (prefixWord ++ tailWord_7159055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159055).length < 2 ^ (prefixWord ++ tailWord_7159055).sum := by decide
  have hdescent : baseEnd_7159055 < baseStart_7159055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159089 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 4]
def baseStart_7159089 : Nat := 118140960795 + 7159089 * 2 ^ 59
def prefixEnd_7159089 : Nat := 4983230072969 + 3 ^ 40 * 7159089 * 2
def baseEnd_7159089 : Nat := 3676053705315845765063455

theorem tailTrace_7159089 : CollatzResearch.WordTrace tailWord_7159089 prefixEnd_7159089 3676053705315845765063455 := by
  unfold tailWord_7159089
  simp only [CollatzResearch.WordTrace]
  refine ⟨261113427160850702904176321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174075618107233801936117547 261113427160850702904176321)
  ·
    refine ⟨195835070370638027178132241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261113427160850702904176321 195835070370638027178132241)
    ·
      refine ⟨146876302777978520383599181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195835070370638027178132241 146876302777978520383599181)
      ·
        refine ⟨55078613541741945143849693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146876302777978520383599181 55078613541741945143849693)
        ·
          refine ⟨20654480078153229428943635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55078613541741945143849693 20654480078153229428943635)
          ·
            refine ⟨30981720117229844143415453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20654480078153229428943635 30981720117229844143415453)
            ·
              refine ⟨11618145043961191553780795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30981720117229844143415453 11618145043961191553780795)
              ·
                refine ⟨17427217565941787330671193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11618145043961191553780795 17427217565941787330671193)
                ·
                  refine ⟨13070413174456340498003395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17427217565941787330671193 13070413174456340498003395)
                  ·
                    refine ⟨19605619761684510747005093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13070413174456340498003395 19605619761684510747005093)
                    ·
                      refine ⟨3676053705315845765063455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19605619761684510747005093 3676053705315845765063455)
                      ·
                        rfl

theorem cell23_7159089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_7159089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159089 prefixEnd_7159089 := by exact prefixLift 7159089
  have htrace : WordTrace (prefixWord ++ tailWord_7159089) baseStart_7159089 baseEnd_7159089 := by
    simpa [prefixWord, tailWord_7159089, baseEnd_7159089] using wordTrace_append hprefix tailTrace_7159089
  have hstable : (prefixWord ++ tailWord_7159089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159089).length < 2 ^ (prefixWord ++ tailWord_7159089).sum := by decide
  have hdescent : baseEnd_7159089 < baseStart_7159089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159102 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_7159102 : Nat := 118140960795 + 7159102 * 2 ^ 59
def prefixEnd_7159102 : Nat := 4983230072969 + 3 ^ 40 * 7159102 * 2
def baseEnd_7159102 : Nat := 3676060380564354214200895

theorem tailTrace_7159102 : CollatzResearch.WordTrace tailWord_7159102 prefixEnd_7159102 3676060380564354214200895 := by
  unfold tailWord_7159102
  simp only [CollatzResearch.WordTrace]
  refine ⟨32639237663725450765549945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174075934206535737416266373 32639237663725450765549945)
  ·
    refine ⟨24479428247794088074162459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32639237663725450765549945 24479428247794088074162459)
    ·
      refine ⟨36719142371691132111243689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24479428247794088074162459 36719142371691132111243689)
      ·
        refine ⟨27539356778768349083432767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36719142371691132111243689 27539356778768349083432767)
        ·
          refine ⟨41309035168152523625149151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27539356778768349083432767 41309035168152523625149151)
          ·
            refine ⟨61963552752228785437723727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41309035168152523625149151 61963552752228785437723727)
            ·
              refine ⟨92945329128343178156585591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61963552752228785437723727 92945329128343178156585591)
              ·
                refine ⟨139417993692514767234878387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92945329128343178156585591 139417993692514767234878387)
                ·
                  refine ⟨209126990538772150852317581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139417993692514767234878387 209126990538772150852317581)
                  ·
                    refine ⟨78422621452039556569619093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209126990538772150852317581 78422621452039556569619093)
                    ·
                      refine ⟨3676060380564354214200895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78422621452039556569619093 3676060380564354214200895)
                      ·
                        rfl

theorem cell23_7159102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_7159102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159102 prefixEnd_7159102 := by exact prefixLift 7159102
  have htrace : WordTrace (prefixWord ++ tailWord_7159102) baseStart_7159102 baseEnd_7159102 := by
    simpa [prefixWord, tailWord_7159102, baseEnd_7159102] using wordTrace_append hprefix tailTrace_7159102
  have hstable : (prefixWord ++ tailWord_7159102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159102).length < 2 ^ (prefixWord ++ tailWord_7159102).sum := by decide
  have hdescent : baseEnd_7159102 < baseStart_7159102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159116 : List Nat := [2, 2, 1, 3, 2, 2, 2, 4, 1, 4]
def baseStart_7159116 : Nat := 118140960795 + 7159116 * 2 ^ 59
def prefixEnd_7159116 : Nat := 4983230072969 + 3 ^ 40 * 7159116 * 2
def baseEnd_7159116 : Nat := 1225355856431172386475277

theorem tailTrace_7159116 : CollatzResearch.WordTrace tailWord_7159116 prefixEnd_7159116 1225355856431172386475277 := by
  unfold tailWord_7159116
  simp only [CollatzResearch.WordTrace]
  refine ⟨130557205965876443257704601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174076274621168591010272801 130557205965876443257704601)
  ·
    refine ⟨97917904474407332443278451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130557205965876443257704601 97917904474407332443278451)
    ·
      refine ⟨146876856711610998664917677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97917904474407332443278451 146876856711610998664917677)
      ·
        refine ⟨55078821266854124499344129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146876856711610998664917677 55078821266854124499344129)
        ·
          refine ⟨41309115950140593374508097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55078821266854124499344129 41309115950140593374508097)
          ·
            refine ⟨30981836962605445030881073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41309115950140593374508097 30981836962605445030881073)
            ·
              refine ⟨23236377721954083773160805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30981836962605445030881073 23236377721954083773160805)
              ·
                refine ⟨4356820822866390707467651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23236377721954083773160805 4356820822866390707467651)
                ·
                  refine ⟨6535231234299586061201477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356820822866390707467651 6535231234299586061201477)
                  ·
                    refine ⟨1225355856431172386475277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6535231234299586061201477 1225355856431172386475277)
                    ·
                      rfl

theorem cell23_7159116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_7159116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159116 prefixEnd_7159116 := by exact prefixLift 7159116
  have htrace : WordTrace (prefixWord ++ tailWord_7159116) baseStart_7159116 baseEnd_7159116 := by
    simpa [prefixWord, tailWord_7159116, baseEnd_7159116] using wordTrace_append hprefix tailTrace_7159116
  have hstable : (prefixWord ++ tailWord_7159116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159116).length < 2 ^ (prefixWord ++ tailWord_7159116).sum := by decide
  have hdescent : baseEnd_7159116 < baseStart_7159116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159229 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_7159229 : Nat := 118140960795 + 7159229 * 2 ^ 59
def prefixEnd_7159229 : Nat := 4983230072969 + 3 ^ 40 * 7159229 * 2
def baseEnd_7159229 : Nat := 3676125592607475217312811

theorem tailTrace_7159229 : CollatzResearch.WordTrace tailWord_7159229 prefixEnd_7159229 3676125592607475217312811 := by
  unfold tailWord_7159229
  simp only [CollatzResearch.WordTrace]
  refine ⟨261118533380343506814272741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174079022253562337876181827 261118533380343506814272741)
  ·
    refine ⟨48959725008814407527676139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261118533380343506814272741 48959725008814407527676139)
    ·
      refine ⟨73439587513221611291514209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48959725008814407527676139 73439587513221611291514209)
      ·
        refine ⟨55079690634916208468635657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73439587513221611291514209 55079690634916208468635657)
        ·
          refine ⟨41309767976187156351476743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55079690634916208468635657 41309767976187156351476743)
          ·
            refine ⟨61964651964280734527215115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41309767976187156351476743 61964651964280734527215115)
            ·
              refine ⟨92946977946421101790822673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61964651964280734527215115 92946977946421101790822673)
              ·
                refine ⟨69710233459815826343117005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92946977946421101790822673 69710233459815826343117005)
                ·
                  refine ⟨26141337547430934878668877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69710233459815826343117005 26141337547430934878668877)
                  ·
                    refine ⟨9803001580286600579500829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26141337547430934878668877 9803001580286600579500829)
                    ·
                      refine ⟨3676125592607475217312811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9803001580286600579500829 3676125592607475217312811)
                      ·
                        rfl

theorem cell23_7159229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_7159229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159229 prefixEnd_7159229 := by exact prefixLift 7159229
  have htrace : WordTrace (prefixWord ++ tailWord_7159229) baseStart_7159229 baseEnd_7159229 := by
    simpa [prefixWord, tailWord_7159229, baseEnd_7159229] using wordTrace_append hprefix tailTrace_7159229
  have hstable : (prefixWord ++ tailWord_7159229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159229).length < 2 ^ (prefixWord ++ tailWord_7159229).sum := by decide
  have hdescent : baseEnd_7159229 < baseStart_7159229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159232 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 2, 7]
def baseStart_7159232 : Nat := 118140960795 + 7159232 * 2 ^ 59
def prefixEnd_7159232 : Nat := 4983230072969 + 3 ^ 40 * 7159232 * 2
def baseEnd_7159232 : Nat := 1225375711016479568525099

theorem tailTrace_7159232 : CollatzResearch.WordTrace tailWord_7159232 prefixEnd_7159232 1225375711016479568525099 := by
  unfold tailWord_7159232
  simp only [CollatzResearch.WordTrace]
  refine ⟨130559321399666319163315975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174079095199555092217754633 130559321399666319163315975)
  ·
    refine ⟨195838982099499478744973963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130559321399666319163315975 195838982099499478744973963)
    ·
      refine ⟨293758473149249218117460945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195838982099499478744973963 293758473149249218117460945)
      ·
        refine ⟨220318854861936913588095709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293758473149249218117460945 220318854861936913588095709)
        ·
          refine ⟨82619570573226342595535891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220318854861936913588095709 82619570573226342595535891)
          ·
            refine ⟨123929355859839513893303837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82619570573226342595535891 123929355859839513893303837)
            ·
              refine ⟨46473508447439817709988939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123929355859839513893303837 46473508447439817709988939)
              ·
                refine ⟨69710262671159726564983409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46473508447439817709988939 69710262671159726564983409)
                ·
                  refine ⟨52282697003369794923737557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69710262671159726564983409 52282697003369794923737557)
                  ·
                    refine ⟨1225375711016479568525099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52282697003369794923737557 1225375711016479568525099)
                    ·
                      rfl

theorem cell23_7159232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_7159232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159232 prefixEnd_7159232 := by exact prefixLift 7159232
  have htrace : WordTrace (prefixWord ++ tailWord_7159232) baseStart_7159232 baseEnd_7159232 := by
    simpa [prefixWord, tailWord_7159232, baseEnd_7159232] using wordTrace_append hprefix tailTrace_7159232
  have hstable : (prefixWord ++ tailWord_7159232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159232).length < 2 ^ (prefixWord ++ tailWord_7159232).sum := by decide
  have hdescent : baseEnd_7159232 < baseStart_7159232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159236 : List Nat := [2, 3, 3, 2, 1, 3, 1, 8]
def baseStart_7159236 : Nat := 118140960795 + 7159236 * 2 ^ 59
def prefixEnd_7159236 : Nat := 4983230072969 + 3 ^ 40 * 7159236 * 2
def baseEnd_7159236 : Nat := 136152932850816914441677

theorem tailTrace_7159236 : CollatzResearch.WordTrace tailWord_7159236 prefixEnd_7159236 136152932850816914441677 := by
  unfold tailWord_7159236
  simp only [CollatzResearch.WordTrace]
  refine ⟨130559394345659073504888781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174079192460878764673185041 130559394345659073504888781)
  ·
    refine ⟨48959772879622152564333293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130559394345659073504888781 48959772879622152564333293)
    ·
      refine ⟨18359914829858307211624985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48959772879622152564333293 18359914829858307211624985)
      ·
        refine ⟨13769936122393730408718739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18359914829858307211624985 13769936122393730408718739)
        ·
          refine ⟨20654904183590595613078109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13769936122393730408718739 20654904183590595613078109)
          ·
            refine ⟨7745589068846473354904291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20654904183590595613078109 7745589068846473354904291)
            ·
              refine ⟨11618383603269710032356437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7745589068846473354904291 11618383603269710032356437)
              ·
                refine ⟨136152932850816914441677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11618383603269710032356437 136152932850816914441677)
                ·
                  rfl

theorem cell23_7159236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 8].length) (baseStart_7159236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159236 prefixEnd_7159236 := by exact prefixLift 7159236
  have htrace : WordTrace (prefixWord ++ tailWord_7159236) baseStart_7159236 baseEnd_7159236 := by
    simpa [prefixWord, tailWord_7159236, baseEnd_7159236] using wordTrace_append hprefix tailTrace_7159236
  have hstable : (prefixWord ++ tailWord_7159236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159236).length < 2 ^ (prefixWord ++ tailWord_7159236).sum := by decide
  have hdescent : baseEnd_7159236 < baseStart_7159236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159256 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 3, 3, 2]
def baseStart_7159256 : Nat := 118140960795 + 7159256 * 2 ^ 59
def prefixEnd_7159256 : Nat := 4983230072969 + 3 ^ 40 * 7159256 * 2
def baseEnd_7159256 : Nat := 3676139456585146611675187

theorem tailTrace_7159256 : CollatzResearch.WordTrace tailWord_7159256 prefixEnd_7159256 3676139456585146611675187 := by
  unfold tailWord_7159256
  simp only [CollatzResearch.WordTrace]
  refine ⟨130559759075622845212752811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174079678767497126950337081 130559759075622845212752811)
  ·
    refine ⟨195839638613434267819129217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130559759075622845212752811 195839638613434267819129217)
    ·
      refine ⟨146879728960075700864346913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195839638613434267819129217 146879728960075700864346913)
      ·
        refine ⟨110159796720056775648260185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146879728960075700864346913 110159796720056775648260185)
        ·
          refine ⟨82619847540042581736195139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110159796720056775648260185 82619847540042581736195139)
          ·
            refine ⟨123929771310063872604292709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82619847540042581736195139 123929771310063872604292709)
            ·
              refine ⟨23236832120636976113304883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123929771310063872604292709 23236832120636976113304883)
              ·
                refine ⟨34855248180955464169957325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23236832120636976113304883 34855248180955464169957325)
                ·
                  refine ⟨13070718067858299063733997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34855248180955464169957325 13070718067858299063733997)
                  ·
                    refine ⟨4901519275446862148900249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13070718067858299063733997 4901519275446862148900249)
                    ·
                      refine ⟨3676139456585146611675187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901519275446862148900249 3676139456585146611675187)
                      ·
                        rfl

theorem cell23_7159256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_7159256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159256 prefixEnd_7159256 := by exact prefixLift 7159256
  have htrace : WordTrace (prefixWord ++ tailWord_7159256) baseStart_7159256 baseEnd_7159256 := by
    simpa [prefixWord, tailWord_7159256, baseEnd_7159256] using wordTrace_append hprefix tailTrace_7159256
  have hstable : (prefixWord ++ tailWord_7159256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159256).length < 2 ^ (prefixWord ++ tailWord_7159256).sum := by decide
  have hdescent : baseEnd_7159256 < baseStart_7159256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159303 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 1, 4, 2]
def baseStart_7159303 : Nat := 118140960795 + 7159303 * 2 ^ 59
def prefixEnd_7159303 : Nat := 4983230072969 + 3 ^ 40 * 7159303 * 2
def baseEnd_7159303 : Nat := 3676163590175907927787471

theorem tailTrace_7159303 : CollatzResearch.WordTrace tailWord_7159303 prefixEnd_7159303 3676163590175907927787471 := by
  unfold tailWord_7159303
  simp only [CollatzResearch.WordTrace]
  refine ⟨261121232382075417452466563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174080821588050278301644375 261121232382075417452466563)
  ·
    refine ⟨391681848573113126178699845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261121232382075417452466563 391681848573113126178699845)
    ·
      refine ⟨73440346607458711158506221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391681848573113126178699845 73440346607458711158506221)
      ·
        refine ⟨27540129977797016684439833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73440346607458711158506221 27540129977797016684439833)
        ·
          refine ⟨20655097483347762513329875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27540129977797016684439833 20655097483347762513329875)
          ·
            refine ⟨30982646225021643769994813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20655097483347762513329875 30982646225021643769994813)
            ·
              refine ⟨11618492334383116413748055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30982646225021643769994813 11618492334383116413748055)
              ·
                refine ⟨17427738501574674620622083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11618492334383116413748055 17427738501574674620622083)
                ·
                  refine ⟨26141607752362011930933125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17427738501574674620622083 26141607752362011930933125)
                  ·
                    refine ⟨4901551453567877237049961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26141607752362011930933125 4901551453567877237049961)
                    ·
                      refine ⟨3676163590175907927787471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901551453567877237049961 3676163590175907927787471)
                      ·
                        rfl

theorem cell23_7159303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_7159303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159303 prefixEnd_7159303 := by exact prefixLift 7159303
  have htrace : WordTrace (prefixWord ++ tailWord_7159303) baseStart_7159303 baseEnd_7159303 := by
    simpa [prefixWord, tailWord_7159303, baseEnd_7159303] using wordTrace_append hprefix tailTrace_7159303
  have hstable : (prefixWord ++ tailWord_7159303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159303).length < 2 ^ (prefixWord ++ tailWord_7159303).sum := by decide
  have hdescent : baseEnd_7159303 < baseStart_7159303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159346 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2]
def baseStart_7159346 : Nat := 118140960795 + 7159346 * 2 ^ 59
def prefixEnd_7159346 : Nat := 4983230072969 + 3 ^ 40 * 7159346 * 2
def baseEnd_7159346 : Nat := 3676185669844051259549773

theorem tailTrace_7159346 : CollatzResearch.WordTrace tailWord_7159346 prefixEnd_7159346 3676185669844051259549773 := by
  unfold tailWord_7159346
  simp only [CollatzResearch.WordTrace]
  refine ⟨65280700180229908949070473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174081867147279757197521261 65280700180229908949070473)
  ·
    refine ⟨48960525135172431711802855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65280700180229908949070473 48960525135172431711802855)
    ·
      refine ⟨73440787702758647567704283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48960525135172431711802855 73440787702758647567704283)
      ·
        refine ⟨110161181554137971351556425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73440787702758647567704283 110161181554137971351556425)
        ·
          refine ⟨82620886165603478513667319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110161181554137971351556425 82620886165603478513667319)
          ·
            refine ⟨123931329248405217770500979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82620886165603478513667319 123931329248405217770500979)
            ·
              refine ⟨185896993872607826655751469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123931329248405217770500979 185896993872607826655751469)
              ·
                refine ⟨69711372702227934995906801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185896993872607826655751469 69711372702227934995906801)
                ·
                  refine ⟨52283529526670951246930101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69711372702227934995906801 52283529526670951246930101)
                  ·
                    refine ⟨4901580893125401679399697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52283529526670951246930101 4901580893125401679399697)
                    ·
                      refine ⟨3676185669844051259549773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901580893125401679399697 3676185669844051259549773)
                      ·
                        rfl

theorem cell23_7159346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_7159346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159346 prefixEnd_7159346 := by exact prefixLift 7159346
  have htrace : WordTrace (prefixWord ++ tailWord_7159346) baseStart_7159346 baseEnd_7159346 := by
    simpa [prefixWord, tailWord_7159346, baseEnd_7159346] using wordTrace_append hprefix tailTrace_7159346
  have hstable : (prefixWord ++ tailWord_7159346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159346).length < 2 ^ (prefixWord ++ tailWord_7159346).sum := by decide
  have hdescent : baseEnd_7159346 < baseStart_7159346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159349 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_7159349 : Nat := 118140960795 + 7159349 * 2 ^ 59
def prefixEnd_7159349 : Nat := 4983230072969 + 3 ^ 40 * 7159349 * 2
def baseEnd_7159349 : Nat := 3676187210286014747812259

theorem tailTrace_7159349 : CollatzResearch.WordTrace tailWord_7159349 prefixEnd_7159349 3676187210286014747812259 := by
  unfold tailWord_7159349
  simp only [CollatzResearch.WordTrace]
  refine ⟨261122910139908767308641101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174081940093272511539094067 261122910139908767308641101)
  ·
    refine ⟨97921091302465787740740413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261122910139908767308641101 97921091302465787740740413)
    ·
      refine ⟨36720409238424670402777655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97921091302465787740740413 36720409238424670402777655)
      ·
        refine ⟨55080613857637005604166483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36720409238424670402777655 55080613857637005604166483)
        ·
          refine ⟨82620920786455508406249725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55080613857637005604166483 82620920786455508406249725)
          ·
            refine ⟨30982845294920815652343647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82620920786455508406249725 30982845294920815652343647)
            ·
              refine ⟨46474267942381223478515471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30982845294920815652343647 46474267942381223478515471)
              ·
                refine ⟨69711401913571835217773207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46474267942381223478515471 69711401913571835217773207)
                ·
                  refine ⟨104567102870357752826659811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69711401913571835217773207 104567102870357752826659811)
                  ·
                    refine ⟨156850654305536629239989717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104567102870357752826659811 156850654305536629239989717)
                    ·
                      refine ⟨3676187210286014747812259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156850654305536629239989717 3676187210286014747812259)
                      ·
                        rfl

theorem cell23_7159349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_7159349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159349 prefixEnd_7159349 := by exact prefixLift 7159349
  have htrace : WordTrace (prefixWord ++ tailWord_7159349) baseStart_7159349 baseEnd_7159349 := by
    simpa [prefixWord, tailWord_7159349, baseEnd_7159349] using wordTrace_append hprefix tailTrace_7159349
  have hstable : (prefixWord ++ tailWord_7159349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159349).length < 2 ^ (prefixWord ++ tailWord_7159349).sum := by decide
  have hdescent : baseEnd_7159349 < baseStart_7159349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159376 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 4]
def baseStart_7159376 : Nat := 118140960795 + 7159376 * 2 ^ 59
def prefixEnd_7159376 : Nat := 4983230072969 + 3 ^ 40 * 7159376 * 2
def baseEnd_7159376 : Nat := 3676201074263686142174635

theorem tailTrace_7159376 : CollatzResearch.WordTrace tailWord_7159376 prefixEnd_7159376 3676201074263686142174635 := by
  unfold tailWord_7159376
  simp only [CollatzResearch.WordTrace]
  refine ⟨130561947455405475459936991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174082596607207300613249321 130561947455405475459936991)
  ·
    refine ⟨195842921183108213189905487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130561947455405475459936991 195842921183108213189905487)
    ·
      refine ⟨293764381774662319784858231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195842921183108213189905487 293764381774662319784858231)
      ·
        refine ⟨440646572661993479677287347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293764381774662319784858231 440646572661993479677287347)
        ·
          refine ⟨660969858992990219515931021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440646572661993479677287347 660969858992990219515931021)
          ·
            refine ⟨247863697122371332318474133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 660969858992990219515931021 247863697122371332318474133)
            ·
              refine ⟨11618610802611156202428475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 247863697122371332318474133 11618610802611156202428475)
              ·
                refine ⟨17427916203916734303642713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11618610802611156202428475 17427916203916734303642713)
                ·
                  refine ⟨13070937152937550727732035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17427916203916734303642713 13070937152937550727732035)
                  ·
                    refine ⟨19606405729406326091598053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13070937152937550727732035 19606405729406326091598053)
                    ·
                      refine ⟨3676201074263686142174635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19606405729406326091598053 3676201074263686142174635)
                      ·
                        rfl

theorem cell23_7159376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 4].length) (baseStart_7159376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159376 prefixEnd_7159376 := by exact prefixLift 7159376
  have htrace : WordTrace (prefixWord ++ tailWord_7159376) baseStart_7159376 baseEnd_7159376 := by
    simpa [prefixWord, tailWord_7159376, baseEnd_7159376] using wordTrace_append hprefix tailTrace_7159376
  have hstable : (prefixWord ++ tailWord_7159376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159376).length < 2 ^ (prefixWord ++ tailWord_7159376).sum := by decide
  have hdescent : baseEnd_7159376 < baseStart_7159376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159399 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 8]
def baseStart_7159399 : Nat := 118140960795 + 7159399 * 2 ^ 59
def prefixEnd_7159399 : Nat := 4983230072969 + 3 ^ 40 * 7159399 * 2
def baseEnd_7159399 : Nat := 408468098257637728020781

theorem tailTrace_7159399 : CollatzResearch.WordTrace tailWord_7159399 prefixEnd_7159399 408468098257637728020781 := by
  unfold tailWord_7159399
  simp only [CollatzResearch.WordTrace]
  refine ⟨261124733789727625847961251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174083155859818417231974167 261124733789727625847961251)
  ·
    refine ⟨391687100684591438771941877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261124733789727625847961251 391687100684591438771941877)
    ·
      refine ⟨36720665689180447384869551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391687100684591438771941877 36720665689180447384869551)
      ·
        refine ⟨55080998533770671077304327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36720665689180447384869551 55080998533770671077304327)
        ·
          refine ⟨82621497800656006615956491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55080998533770671077304327 82621497800656006615956491)
          ·
            refine ⟨123932246700984009923934737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82621497800656006615956491 123932246700984009923934737)
            ·
              refine ⟨92949185025738007442951053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123932246700984009923934737 92949185025738007442951053)
              ·
                refine ⟨34855944384651752791106645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92949185025738007442951053 34855944384651752791106645)
                ·
                  refine ⟨408468098257637728020781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34855944384651752791106645 408468098257637728020781)
                  ·
                    rfl

theorem cell23_7159399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 8].length) (baseStart_7159399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159399 prefixEnd_7159399 := by exact prefixLift 7159399
  have htrace : WordTrace (prefixWord ++ tailWord_7159399) baseStart_7159399 baseEnd_7159399 := by
    simpa [prefixWord, tailWord_7159399, baseEnd_7159399] using wordTrace_append hprefix tailTrace_7159399
  have hstable : (prefixWord ++ tailWord_7159399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159399).length < 2 ^ (prefixWord ++ tailWord_7159399).sum := by decide
  have hdescent : baseEnd_7159399 < baseStart_7159399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159453 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_7159453 : Nat := 118140960795 + 7159453 * 2 ^ 59
def prefixEnd_7159453 : Nat := 4983230072969 + 3 ^ 40 * 7159453 * 2
def baseEnd_7159453 : Nat := 3676240612274082340911781

theorem tailTrace_7159453 : CollatzResearch.WordTrace tailWord_7159453 prefixEnd_7159453 3676240612274082340911781 := by
  unfold tailWord_7159453
  simp only [CollatzResearch.WordTrace]
  refine ⟨261126703331531993070427013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174084468887687995380284675 261126703331531993070427013)
  ·
    refine ⟨48961256874662248700705065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261126703331531993070427013 48961256874662248700705065)
    ·
      refine ⟨36720942655996686525528799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48961256874662248700705065 36720942655996686525528799)
      ·
        refine ⟨55081413983995029788293199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36720942655996686525528799 55081413983995029788293199)
        ·
          refine ⟨82622120975992544682439799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55081413983995029788293199 82622120975992544682439799)
          ·
            refine ⟨123933181463988817023659699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82622120975992544682439799 123933181463988817023659699)
            ·
              refine ⟨185899772195983225535489549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123933181463988817023659699 185899772195983225535489549)
              ·
                refine ⟨69712414573493709575808581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185899772195983225535489549 69712414573493709575808581)
                ·
                  refine ⟨13071077732530070545464109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69712414573493709575808581 13071077732530070545464109)
                  ·
                    refine ⟨4901654149698776454549041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13071077732530070545464109 4901654149698776454549041)
                    ·
                      refine ⟨3676240612274082340911781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901654149698776454549041 3676240612274082340911781)
                      ·
                        rfl

theorem cell23_7159453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_7159453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159453 prefixEnd_7159453 := by exact prefixLift 7159453
  have htrace : WordTrace (prefixWord ++ tailWord_7159453) baseStart_7159453 baseEnd_7159453 := by
    simpa [prefixWord, tailWord_7159453, baseEnd_7159453] using wordTrace_append hprefix tailTrace_7159453
  have hstable : (prefixWord ++ tailWord_7159453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159453).length < 2 ^ (prefixWord ++ tailWord_7159453).sum := by decide
  have hdescent : baseEnd_7159453 < baseStart_7159453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159460 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_7159460 : Nat := 118140960795 + 7159460 * 2 ^ 59
def prefixEnd_7159460 : Nat := 4983230072969 + 3 ^ 40 * 7159460 * 2
def baseEnd_7159460 : Nat := 3676244206638663813524249

theorem tailTrace_7159460 : CollatzResearch.WordTrace tailWord_7159460 prefixEnd_7159460 3676244206638663813524249 := by
  unfold tailWord_7159460
  simp only [CollatzResearch.WordTrace]
  refine ⟨130563479321253316632965917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174084639095004422177287889 130563479321253316632965917)
  ·
    refine ⟨48961304745469993737362219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130563479321253316632965917 48961304745469993737362219)
    ·
      refine ⟨73441957118204990606043329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48961304745469993737362219 73441957118204990606043329)
      ·
        refine ⟨55081467838653742954532497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73441957118204990606043329 55081467838653742954532497)
        ·
          refine ⟨41311100878990307215899373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55081467838653742954532497 41311100878990307215899373)
          ·
            refine ⟨15491662829621365205962265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41311100878990307215899373 15491662829621365205962265)
            ·
              refine ⟨11618747122216023904471699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15491662829621365205962265 11618747122216023904471699)
              ·
                refine ⟨17428120683324035856707549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11618747122216023904471699 17428120683324035856707549)
                ·
                  refine ⟨6535545256246513446265331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17428120683324035856707549 6535545256246513446265331)
                  ·
                    refine ⟨9803317884369770169397997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6535545256246513446265331 9803317884369770169397997)
                    ·
                      refine ⟨3676244206638663813524249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9803317884369770169397997 3676244206638663813524249)
                      ·
                        rfl

theorem cell23_7159460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_7159460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159460 prefixEnd_7159460 := by exact prefixLift 7159460
  have htrace : WordTrace (prefixWord ++ tailWord_7159460) baseStart_7159460 baseEnd_7159460 := by
    simpa [prefixWord, tailWord_7159460, baseEnd_7159460] using wordTrace_append hprefix tailTrace_7159460
  have hstable : (prefixWord ++ tailWord_7159460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159460).length < 2 ^ (prefixWord ++ tailWord_7159460).sum := by decide
  have hdescent : baseEnd_7159460 < baseStart_7159460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159496 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_7159496 : Nat := 118140960795 + 7159496 * 2 ^ 59
def prefixEnd_7159496 : Nat := 4983230072969 + 3 ^ 40 * 7159496 * 2
def baseEnd_7159496 : Nat := 3676262691942225672674083

theorem tailTrace_7159496 : CollatzResearch.WordTrace tailWord_7159496 prefixEnd_7159496 3676262691942225672674083 := by
  unfold tailWord_7159496
  simp only [CollatzResearch.WordTrace]
  refine ⟨130564135835188105707121171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174085514446917474276161561 130564135835188105707121171)
  ·
    refine ⟨195846203752782158560681757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130564135835188105707121171 195846203752782158560681757)
    ·
      refine ⟨73442326407293309460255659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195846203752782158560681757 73442326407293309460255659)
      ·
        refine ⟨110163489610939964190383489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73442326407293309460255659 110163489610939964190383489)
        ·
          refine ⟨82622617208204973142787617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110163489610939964190383489 82622617208204973142787617)
          ·
            refine ⟨61966962906153729857090713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82622617208204973142787617 61966962906153729857090713)
            ·
              refine ⟨46475222179615297392818035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61966962906153729857090713 46475222179615297392818035)
              ·
                refine ⟨69712833269422946089227053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46475222179615297392818035 69712833269422946089227053)
                ·
                  refine ⟨26142312476033604783460145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69712833269422946089227053 26142312476033604783460145)
                  ·
                    refine ⟨19606734357025203587595109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26142312476033604783460145 19606734357025203587595109)
                    ·
                      refine ⟨3676262691942225672674083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19606734357025203587595109 3676262691942225672674083)
                      ·
                        rfl

theorem cell23_7159496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_7159496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159496 prefixEnd_7159496 := by exact prefixLift 7159496
  have htrace : WordTrace (prefixWord ++ tailWord_7159496) baseStart_7159496 baseEnd_7159496 := by
    simpa [prefixWord, tailWord_7159496, baseEnd_7159496] using wordTrace_append hprefix tailTrace_7159496
  have hstable : (prefixWord ++ tailWord_7159496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159496).length < 2 ^ (prefixWord ++ tailWord_7159496).sum := by decide
  have hdescent : baseEnd_7159496 < baseStart_7159496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159506 : List Nat := [3, 2, 2, 2, 2, 1, 11]
def baseStart_7159506 : Nat := 118140960795 + 7159506 * 2 ^ 59
def prefixEnd_7159506 : Nat := 4983230072969 + 3 ^ 40 * 7159506 * 2
def baseEnd_7159506 : Nat := 45386022552453958438877

theorem tailTrace_7159506 : CollatzResearch.WordTrace tailWord_7159506 prefixEnd_7159506 45386022552453958438877 := by
  unfold tailWord_7159506
  simp only [CollatzResearch.WordTrace]
  refine ⟨65282159100084995780526593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174085757600226655414737581 65282159100084995780526593)
  ·
    refine ⟨48961619325063746835394945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65282159100084995780526593 48961619325063746835394945)
    ·
      refine ⟨36721214493797810126546209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48961619325063746835394945 36721214493797810126546209)
      ·
        refine ⟨27540910870348357594909657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36721214493797810126546209 27540910870348357594909657)
        ·
          refine ⟨20655683152761268196182243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27540910870348357594909657 20655683152761268196182243)
          ·
            refine ⟨30983524729141902294273365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20655683152761268196182243 30983524729141902294273365)
            ·
              refine ⟨45386022552453958438877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30983524729141902294273365 45386022552453958438877)
              ·
                rfl

theorem cell23_7159506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 11].length) (baseStart_7159506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159506 prefixEnd_7159506 := by exact prefixLift 7159506
  have htrace : WordTrace (prefixWord ++ tailWord_7159506) baseStart_7159506 baseEnd_7159506 := by
    simpa [prefixWord, tailWord_7159506, baseEnd_7159506] using wordTrace_append hprefix tailTrace_7159506
  have hstable : (prefixWord ++ tailWord_7159506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159506).length < 2 ^ (prefixWord ++ tailWord_7159506).sum := by decide
  have hdescent : baseEnd_7159506 < baseStart_7159506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159523 : List Nat := [1, 1, 1, 7, 2, 1, 2, 8]
def baseStart_7159523 : Nat := 118140960795 + 7159523 * 2 ^ 59
def prefixEnd_7159523 : Nat := 4983230072969 + 3 ^ 40 * 7159523 * 2
def baseEnd_7159523 : Nat := 136158390959996187668017

theorem tailTrace_7159523 : CollatzResearch.WordTrace tailWord_7159523 prefixEnd_7159523 136158390959996187668017 := by
  unfold tailWord_7159523
  simp only [CollatzResearch.WordTrace]
  refine ⟨261129256441278395025475223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174086170960852263350316815 261129256441278395025475223)
  ·
    refine ⟨391693884661917592538212835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261129256441278395025475223 391693884661917592538212835)
    ·
      refine ⟨587540826992876388807319253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391693884661917592538212835 587540826992876388807319253)
      ·
        refine ⟨13770488132645540362671545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 587540826992876388807319253 13770488132645540362671545)
        ·
          refine ⟨10327866099484155272003659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13770488132645540362671545 10327866099484155272003659)
          ·
            refine ⟨15491799149226232908005489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10327866099484155272003659 15491799149226232908005489)
            ·
              refine ⟨11618849361919674681004117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15491799149226232908005489 11618849361919674681004117)
              ·
                refine ⟨136158390959996187668017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11618849361919674681004117 136158390959996187668017)
                ·
                  rfl

theorem cell23_7159523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 8].length) (baseStart_7159523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159523 prefixEnd_7159523 := by exact prefixLift 7159523
  have htrace : WordTrace (prefixWord ++ tailWord_7159523) baseStart_7159523 baseEnd_7159523 := by
    simpa [prefixWord, tailWord_7159523, baseEnd_7159523] using wordTrace_append hprefix tailTrace_7159523
  have hstable : (prefixWord ++ tailWord_7159523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159523).length < 2 ^ (prefixWord ++ tailWord_7159523).sum := by decide
  have hdescent : baseEnd_7159523 < baseStart_7159523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159527 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 2, 4]
def baseStart_7159527 : Nat := 118140960795 + 7159527 * 2 ^ 59
def prefixEnd_7159527 : Nat := 4983230072969 + 3 ^ 40 * 7159527 * 2
def baseEnd_7159527 : Nat := 1225426203280838350462147

theorem tailTrace_7159527 : CollatzResearch.WordTrace tailWord_7159527 prefixEnd_7159527 1225426203280838350462147 := by
  unfold tailWord_7159527
  simp only [CollatzResearch.WordTrace]
  refine ⟨261129402333263903708620835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174086268222175935805747223 261129402333263903708620835)
  ·
    refine ⟨391694103499895855562931253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261129402333263903708620835 391694103499895855562931253)
    ·
      refine ⟨36721322203115236459024805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391694103499895855562931253 36721322203115236459024805)
      ·
        refine ⟨6885247913084106836067151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36721322203115236459024805 6885247913084106836067151)
        ·
          refine ⟨10327871869626160254100727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885247913084106836067151 10327871869626160254100727)
          ·
            refine ⟨15491807804439240381151091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10327871869626160254100727 15491807804439240381151091)
            ·
              refine ⟨23237711706658860571726637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15491807804439240381151091 23237711706658860571726637)
              ·
                refine ⟨8714141889997072714397489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23237711706658860571726637 8714141889997072714397489)
                ·
                  refine ⟨6535606417497804535798117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8714141889997072714397489 6535606417497804535798117)
                  ·
                    refine ⟨1225426203280838350462147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6535606417497804535798117 1225426203280838350462147)
                    ·
                      rfl

theorem cell23_7159527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_7159527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159527 prefixEnd_7159527 := by exact prefixLift 7159527
  have htrace : WordTrace (prefixWord ++ tailWord_7159527) baseStart_7159527 baseEnd_7159527 := by
    simpa [prefixWord, tailWord_7159527, baseEnd_7159527] using wordTrace_append hprefix tailTrace_7159527
  have hstable : (prefixWord ++ tailWord_7159527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159527).length < 2 ^ (prefixWord ++ tailWord_7159527).sum := by decide
  have hdescent : baseEnd_7159527 < baseStart_7159527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159540 : List Nat := [2, 6, 1, 1, 1, 1, 2, 9]
def baseStart_7159540 : Nat := 118140960795 + 7159540 * 2 ^ 59
def prefixEnd_7159540 : Nat := 4983230072969 + 3 ^ 40 * 7159540 * 2
def baseEnd_7159540 : Nat := 136158714262630500019403

theorem tailTrace_7159540 : CollatzResearch.WordTrace tailWord_7159540 prefixEnd_7159540 136158714262630500019403 := by
  unfold tailWord_7159540
  simp only [CollatzResearch.WordTrace]
  refine ⟨130564938241108403464422037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174086584321477871285896049 130564938241108403464422037)
  ·
    refine ⟨6120231480051956412394783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130564938241108403464422037 6120231480051956412394783)
    ·
      refine ⟨9180347220077934618592175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6120231480051956412394783 9180347220077934618592175)
      ·
        refine ⟨13770520830116901927888263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9180347220077934618592175 13770520830116901927888263)
        ·
          refine ⟨20655781245175352891832395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13770520830116901927888263 20655781245175352891832395)
          ·
            refine ⟨30983671867763029337748593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20655781245175352891832395 30983671867763029337748593)
            ·
              refine ⟨23237753900822272003311445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30983671867763029337748593 23237753900822272003311445)
              ·
                refine ⟨136158714262630500019403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23237753900822272003311445 136158714262630500019403)
                ·
                  rfl

theorem cell23_7159540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 9].length) (baseStart_7159540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159540 prefixEnd_7159540 := by exact prefixLift 7159540
  have htrace : WordTrace (prefixWord ++ tailWord_7159540) baseStart_7159540 baseEnd_7159540 := by
    simpa [prefixWord, tailWord_7159540, baseEnd_7159540] using wordTrace_append hprefix tailTrace_7159540
  have hstable : (prefixWord ++ tailWord_7159540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159540).length < 2 ^ (prefixWord ++ tailWord_7159540).sum := by decide
  have hdescent : baseEnd_7159540 < baseStart_7159540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159576 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_7159576 : Nat := 118140960795 + 7159576 * 2 ^ 59
def prefixEnd_7159576 : Nat := 4983230072969 + 3 ^ 40 * 7159576 * 2
def baseEnd_7159576 : Nat := 3676303770394585359673715

theorem tailTrace_7159576 : CollatzResearch.WordTrace tailWord_7159576 prefixEnd_7159576 3676303770394585359673715 := by
  unfold tailWord_7159576
  simp only [CollatzResearch.WordTrace]
  refine ⟨130565594755043192538577291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174087459673390923384769721 130565594755043192538577291)
  ·
    refine ⟨195848392132564788807865937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130565594755043192538577291 195848392132564788807865937)
    ·
      refine ⟨146886294099423591605899453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195848392132564788807865937 146886294099423591605899453)
      ·
        refine ⟨55082360287283846852212295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146886294099423591605899453 55082360287283846852212295)
        ·
          refine ⟨82623540430925770278318443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55082360287283846852212295 82623540430925770278318443)
          ·
            refine ⟨123935310646388655417477665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82623540430925770278318443 123935310646388655417477665)
            ·
              refine ⟨92951482984791491563108249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123935310646388655417477665 92951482984791491563108249)
              ·
                refine ⟨69713612238593618672331187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92951482984791491563108249 69713612238593618672331187)
                ·
                  refine ⟨104570418357890428008496781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69713612238593618672331187 104570418357890428008496781)
                  ·
                    refine ⟨39213906884208910503186293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104570418357890428008496781 39213906884208910503186293)
                    ·
                      refine ⟨3676303770394585359673715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39213906884208910503186293 3676303770394585359673715)
                      ·
                        rfl

theorem cell23_7159576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_7159576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159576 prefixEnd_7159576 := by exact prefixLift 7159576
  have htrace : WordTrace (prefixWord ++ tailWord_7159576) baseStart_7159576 baseEnd_7159576 := by
    simpa [prefixWord, tailWord_7159576, baseEnd_7159576] using wordTrace_append hprefix tailTrace_7159576
  have hstable : (prefixWord ++ tailWord_7159576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159576).length < 2 ^ (prefixWord ++ tailWord_7159576).sum := by decide
  have hdescent : baseEnd_7159576 < baseStart_7159576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159596 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 9]
def baseStart_7159596 : Nat := 118140960795 + 7159596 * 2 ^ 59
def prefixEnd_7159596 : Nat := 4983230072969 + 3 ^ 40 * 7159596 * 2
def baseEnd_7159596 : Nat := 408479337778630586824847

theorem tailTrace_7159596 : CollatzResearch.WordTrace tailWord_7159596 prefixEnd_7159596 408479337778630586824847 := by
  unfold tailWord_7159596
  simp only [CollatzResearch.WordTrace]
  refine ⟨130565959485006964246441321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174087945980009285661921761 130565959485006964246441321)
  ·
    refine ⟨97924469613755223184830991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130565959485006964246441321 97924469613755223184830991)
    ·
      refine ⟨146886704420632834777246487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97924469613755223184830991 146886704420632834777246487)
      ·
        refine ⟨220330056630949252165869731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146886704420632834777246487 220330056630949252165869731)
        ·
          refine ⟨330495084946423878248804597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220330056630949252165869731 330495084946423878248804597)
          ·
            refine ⟨30983914213727238585825431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 330495084946423878248804597 30983914213727238585825431)
            ·
              refine ⟨46475871320590857878738147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30983914213727238585825431 46475871320590857878738147)
              ·
                refine ⟨69713806980886286818107221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46475871320590857878738147 69713806980886286818107221)
                ·
                  refine ⟨408479337778630586824847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69713806980886286818107221 408479337778630586824847)
                  ·
                    rfl

theorem cell23_7159596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_7159596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159596 prefixEnd_7159596 := by exact prefixLift 7159596
  have htrace : WordTrace (prefixWord ++ tailWord_7159596) baseStart_7159596 baseEnd_7159596 := by
    simpa [prefixWord, tailWord_7159596, baseEnd_7159596] using wordTrace_append hprefix tailTrace_7159596
  have hstable : (prefixWord ++ tailWord_7159596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159596).length < 2 ^ (prefixWord ++ tailWord_7159596).sum := by decide
  have hdescent : baseEnd_7159596 < baseStart_7159596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159623 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_7159623 : Nat := 118140960795 + 7159623 * 2 ^ 59
def prefixEnd_7159623 : Nat := 4983230072969 + 3 ^ 40 * 7159623 * 2
def baseEnd_7159623 : Nat := 3676327903985346675785999

theorem tailTrace_7159623 : CollatzResearch.WordTrace tailWord_7159623 prefixEnd_7159623 3676327903985346675785999 := by
  unfold tailWord_7159623
  simp only [CollatzResearch.WordTrace]
  refine ⟨261132903740916112104115523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174088602493944074736077015 261132903740916112104115523)
  ·
    refine ⟨391699355611374168156173285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261132903740916112104115523 391699355611374168156173285)
    ·
      refine ⟨73443629177132656529282491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391699355611374168156173285 73443629177132656529282491)
      ·
        refine ⟨110165443765698984793923737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73443629177132656529282491 110165443765698984793923737)
        ·
          refine ⟨82624082824274238595442803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110165443765698984793923737 82624082824274238595442803)
          ·
            refine ⟨123936124236411357893164205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82624082824274238595442803 123936124236411357893164205)
            ·
              refine ⟨46476046588654259209936577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123936124236411357893164205 46476046588654259209936577)
              ·
                refine ⟨34857034941490694407452433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46476046588654259209936577 34857034941490694407452433)
                ·
                  refine ⟨26142776206118020805589325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34857034941490694407452433 26142776206118020805589325)
                  ·
                    refine ⟨9803541077294257802095997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26142776206118020805589325 9803541077294257802095997)
                    ·
                      refine ⟨3676327903985346675785999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9803541077294257802095997 3676327903985346675785999)
                      ·
                        rfl

theorem cell23_7159623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_7159623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159623 prefixEnd_7159623 := by exact prefixLift 7159623
  have htrace : WordTrace (prefixWord ++ tailWord_7159623) baseStart_7159623 baseEnd_7159623 := by
    simpa [prefixWord, tailWord_7159623, baseEnd_7159623] using wordTrace_append hprefix tailTrace_7159623
  have hstable : (prefixWord ++ tailWord_7159623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159623).length < 2 ^ (prefixWord ++ tailWord_7159623).sum := by decide
  have hdescent : baseEnd_7159623 < baseStart_7159623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159624 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 2, 2, 2]
def baseStart_7159624 : Nat := 118140960795 + 7159624 * 2 ^ 59
def prefixEnd_7159624 : Nat := 4983230072969 + 3 ^ 40 * 7159624 * 2
def baseEnd_7159624 : Nat := 3676328417466001171873495

theorem tailTrace_7159624 : CollatzResearch.WordTrace tailWord_7159624 prefixEnd_7159624 3676328417466001171873495 := by
  unfold tailWord_7159624
  simp only [CollatzResearch.WordTrace]
  refine ⟨130566470106956244637450963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174088626809274992849934617 130566470106956244637450963)
  ·
    refine ⟨195849705160434366956176445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130566470106956244637450963 195849705160434366956176445)
    ·
      refine ⟨73443639435162887608566167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195849705160434366956176445 73443639435162887608566167)
      ·
        refine ⟨110165459152744331412849251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73443639435162887608566167 110165459152744331412849251)
        ·
          refine ⟨165248188729116497119273877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110165459152744331412849251 165248188729116497119273877)
          ·
            refine ⟨7746008846677335802465963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165248188729116497119273877 7746008846677335802465963)
            ·
              refine ⟨11619013270016003703698945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7746008846677335802465963 11619013270016003703698945)
              ·
                refine ⟨8714259952512002777774209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11619013270016003703698945 8714259952512002777774209)
                ·
                  refine ⟨6535694964384002083330657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8714259952512002777774209 6535694964384002083330657)
                  ·
                    refine ⟨4901771223288001562497993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6535694964384002083330657 4901771223288001562497993)
                    ·
                      refine ⟨3676328417466001171873495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901771223288001562497993 3676328417466001171873495)
                      ·
                        rfl

theorem cell23_7159624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_7159624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159624 prefixEnd_7159624 := by exact prefixLift 7159624
  have htrace : WordTrace (prefixWord ++ tailWord_7159624) baseStart_7159624 baseEnd_7159624 := by
    simpa [prefixWord, tailWord_7159624, baseEnd_7159624] using wordTrace_append hprefix tailTrace_7159624
  have hstable : (prefixWord ++ tailWord_7159624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159624).length < 2 ^ (prefixWord ++ tailWord_7159624).sum := by decide
  have hdescent : baseEnd_7159624 < baseStart_7159624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159741 : List Nat := [1, 4, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_7159741 : Nat := 118140960795 + 7159741 * 2 ^ 59
def prefixEnd_7159741 : Nat := 4983230072969 + 3 ^ 40 * 7159741 * 2
def baseEnd_7159741 : Nat := 1225462831567525738036819

theorem tailTrace_7159741 : CollatzResearch.WordTrace tailWord_7159741 prefixEnd_7159741 1225462831567525738036819 := by
  unfold tailWord_7159741
  simp only [CollatzResearch.WordTrace]
  refine ⟨261137207554488618256911077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174091471702992412171274051 261137207554488618256911077)
  ·
    refine ⟨48963226416466615923170827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261137207554488618256911077 48963226416466615923170827)
    ·
      refine ⟨73444839624699923884756241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48963226416466615923170827 73444839624699923884756241)
      ·
        refine ⟨55083629718524942913567181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73444839624699923884756241 55083629718524942913567181)
        ·
          refine ⟨20656361144446853592587693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55083629718524942913567181 20656361144446853592587693)
          ·
            refine ⟨7746135429167570097220385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20656361144446853592587693 7746135429167570097220385)
            ·
              refine ⟨5809601571875677572915289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7746135429167570097220385 5809601571875677572915289)
              ·
                refine ⟨4357201178906758179686467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5809601571875677572915289 4357201178906758179686467)
                ·
                  refine ⟨6535801768360137269529701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357201178906758179686467 6535801768360137269529701)
                  ·
                    refine ⟨1225462831567525738036819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6535801768360137269529701 1225462831567525738036819)
                    ·
                      rfl

theorem cell23_7159741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_7159741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159741 prefixEnd_7159741 := by exact prefixLift 7159741
  have htrace : WordTrace (prefixWord ++ tailWord_7159741) baseStart_7159741 baseEnd_7159741 := by
    simpa [prefixWord, tailWord_7159741, baseEnd_7159741] using wordTrace_append hprefix tailTrace_7159741
  have hstable : (prefixWord ++ tailWord_7159741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159741).length < 2 ^ (prefixWord ++ tailWord_7159741).sum := by decide
  have hdescent : baseEnd_7159741 < baseStart_7159741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159780 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_7159780 : Nat := 118140960795 + 7159780 * 2 ^ 59
def prefixEnd_7159780 : Nat := 4983230072969 + 3 ^ 40 * 7159780 * 2
def baseEnd_7159780 : Nat := 1225469506816034187174259

theorem tailTrace_7159780 : CollatzResearch.WordTrace tailWord_7159780 prefixEnd_7159780 1225469506816034187174259 := by
  unfold tailWord_7159780
  simp only [CollatzResearch.WordTrace]
  refine ⟨130569315000673663958790397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174092420000898218611720529 130569315000673663958790397)
  ·
    refine ⟨48963493125252623984546399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130569315000673663958790397 48963493125252623984546399)
    ·
      refine ⟨73445239687878935976819599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48963493125252623984546399 73445239687878935976819599)
      ·
        refine ⟨110167859531818403965229399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73445239687878935976819599 110167859531818403965229399)
        ·
          refine ⟨165251789297727605947844099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110167859531818403965229399 165251789297727605947844099)
          ·
            refine ⟨247877683946591408921766149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165251789297727605947844099 247877683946591408921766149)
            ·
              refine ⟨46477065739985889172831153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247877683946591408921766149 46477065739985889172831153)
              ·
                refine ⟨34857799304989416879623365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46477065739985889172831153 34857799304989416879623365)
                ·
                  refine ⟨6535837369685515664929381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34857799304989416879623365 6535837369685515664929381)
                  ·
                    refine ⟨1225469506816034187174259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6535837369685515664929381 1225469506816034187174259)
                    ·
                      rfl

theorem cell23_7159780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_7159780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159780 prefixEnd_7159780 := by exact prefixLift 7159780
  have htrace : WordTrace (prefixWord ++ tailWord_7159780) baseStart_7159780 baseEnd_7159780 := by
    simpa [prefixWord, tailWord_7159780, baseEnd_7159780] using wordTrace_append hprefix tailTrace_7159780
  have hstable : (prefixWord ++ tailWord_7159780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159780).length < 2 ^ (prefixWord ++ tailWord_7159780).sum := by decide
  have hdescent : baseEnd_7159780 < baseStart_7159780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159804 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 3, 2, 2]
def baseStart_7159804 : Nat := 118140960795 + 7159804 * 2 ^ 59
def prefixEnd_7159804 : Nat := 4983230072969 + 3 ^ 40 * 7159804 * 2
def baseEnd_7159804 : Nat := 3676420843983810467622667

theorem tailTrace_7159804 : CollatzResearch.WordTrace tailWord_7159804 prefixEnd_7159804 3676420843983810467622667 := by
  unfold tailWord_7159804
  simp only [CollatzResearch.WordTrace]
  refine ⟨130569752676630190008227233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174093003568840253344302977 130569752676630190008227233)
  ·
    refine ⟨97927314507472642506170425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130569752676630190008227233 97927314507472642506170425)
    ·
      refine ⟨73445485880604481879627819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97927314507472642506170425 73445485880604481879627819)
      ·
        refine ⟨110168228820906722819441729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73445485880604481879627819 110168228820906722819441729)
        ·
          refine ⟨82626171615680042114581297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110168228820906722819441729 82626171615680042114581297)
          ·
            refine ⟨61969628711760031585935973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82626171615680042114581297 61969628711760031585935973)
            ·
              refine ⟨11619305383455005922362995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61969628711760031585935973 11619305383455005922362995)
              ·
                refine ⟨17428958075182508883544493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11619305383455005922362995 17428958075182508883544493)
                ·
                  refine ⟨6535859278193440831329185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17428958075182508883544493 6535859278193440831329185)
                  ·
                    refine ⟨4901894458645080623496889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6535859278193440831329185 4901894458645080623496889)
                    ·
                      refine ⟨3676420843983810467622667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901894458645080623496889 3676420843983810467622667)
                      ·
                        rfl

theorem cell23_7159804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_7159804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159804 prefixEnd_7159804 := by exact prefixLift 7159804
  have htrace : WordTrace (prefixWord ++ tailWord_7159804) baseStart_7159804 baseEnd_7159804 := by
    simpa [prefixWord, tailWord_7159804, baseEnd_7159804] using wordTrace_append hprefix tailTrace_7159804
  have hstable : (prefixWord ++ tailWord_7159804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159804).length < 2 ^ (prefixWord ++ tailWord_7159804).sum := by decide
  have hdescent : baseEnd_7159804 < baseStart_7159804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159854 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_7159854 : Nat := 118140960795 + 7159854 * 2 ^ 59
def prefixEnd_7159854 : Nat := 4983230072969 + 3 ^ 40 * 7159854 * 2
def baseEnd_7159854 : Nat := 3676446518016535271997437

theorem tailTrace_7159854 : CollatzResearch.WordTrace tailWord_7159854 prefixEnd_7159854 3676446518016535271997437 := by
  unfold tailWord_7159854
  simp only [CollatzResearch.WordTrace]
  refine ⟨32642666125384904819471827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174094219335386159037183077 32642666125384904819471827)
  ·
    refine ⟨48963999188077357229207741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32642666125384904819471827 48963999188077357229207741)
    ·
      refine ⟨18361499695529008960952903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48963999188077357229207741 18361499695529008960952903)
      ·
        refine ⟨27542249543293513441429355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18361499695529008960952903 27542249543293513441429355)
        ·
          refine ⟨41313374314940270162144033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27542249543293513441429355 41313374314940270162144033)
          ·
            refine ⟨30985030736205202621608025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41313374314940270162144033 30985030736205202621608025)
            ·
              refine ⟨23238773052153901966206019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30985030736205202621608025 23238773052153901966206019)
              ·
                refine ⟨34858159578230852949309029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23238773052153901966206019 34858159578230852949309029)
                ·
                  refine ⟨6535904920918284927995443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34858159578230852949309029 6535904920918284927995443)
                  ·
                    refine ⟨9803857381377427391993165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6535904920918284927995443 9803857381377427391993165)
                    ·
                      refine ⟨3676446518016535271997437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9803857381377427391993165 3676446518016535271997437)
                      ·
                        rfl

theorem cell23_7159854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_7159854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159854 prefixEnd_7159854 := by exact prefixLift 7159854
  have htrace : WordTrace (prefixWord ++ tailWord_7159854) baseStart_7159854 baseEnd_7159854 := by
    simpa [prefixWord, tailWord_7159854, baseEnd_7159854] using wordTrace_append hprefix tailTrace_7159854
  have hstable : (prefixWord ++ tailWord_7159854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159854).length < 2 ^ (prefixWord ++ tailWord_7159854).sum := by decide
  have hdescent : baseEnd_7159854 < baseStart_7159854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159877 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 1, 4, 2]
def baseStart_7159877 : Nat := 118140960795 + 7159877 * 2 ^ 59
def prefixEnd_7159877 : Nat := 4983230072969 + 3 ^ 40 * 7159877 * 2
def baseEnd_7159877 : Nat := 3676458328071588682009831

theorem tailTrace_7159877 : CollatzResearch.WordTrace tailWord_7159877 prefixEnd_7159877 3676458328071588682009831 := by
  unfold tailWord_7159877
  simp only [CollatzResearch.WordTrace]
  refine ⟨261142167881995913483861885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174094778587997275655907923 261142167881995913483861885)
  ·
    refine ⟨97928312955748467556448207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261142167881995913483861885 97928312955748467556448207)
    ·
      refine ⟨146892469433622701334672311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97928312955748467556448207 146892469433622701334672311)
      ·
        refine ⟨220338704150434052002008467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146892469433622701334672311 220338704150434052002008467)
        ·
          refine ⟨330508056225651078003012701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220338704150434052002008467 330508056225651078003012701)
          ·
            refine ⟨123940521084619154251129763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330508056225651078003012701 123940521084619154251129763)
            ·
              refine ⟨185910781626928731376694645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123940521084619154251129763 185910781626928731376694645)
              ·
                refine ⟨17429135777524568566565123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185910781626928731376694645 17429135777524568566565123)
                ·
                  refine ⟨26143703666286852849847685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17429135777524568566565123 26143703666286852849847685)
                  ·
                    refine ⟨4901944437428784909346441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26143703666286852849847685 4901944437428784909346441)
                    ·
                      refine ⟨3676458328071588682009831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901944437428784909346441 3676458328071588682009831)
                      ·
                        rfl

theorem cell23_7159877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_7159877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159877 prefixEnd_7159877 := by exact prefixLift 7159877
  have htrace : WordTrace (prefixWord ++ tailWord_7159877) baseStart_7159877 baseEnd_7159877 := by
    simpa [prefixWord, tailWord_7159877, baseEnd_7159877] using wordTrace_append hprefix tailTrace_7159877
  have hstable : (prefixWord ++ tailWord_7159877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159877).length < 2 ^ (prefixWord ++ tailWord_7159877).sum := by decide
  have hdescent : baseEnd_7159877 < baseStart_7159877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159880 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_7159880 : Nat := 118140960795 + 7159880 * 2 ^ 59
def prefixEnd_7159880 : Nat := 4983230072969 + 3 ^ 40 * 7159880 * 2
def baseEnd_7159880 : Nat := 3676459868513552170272317

theorem tailTrace_7159880 : CollatzResearch.WordTrace tailWord_7159880 prefixEnd_7159880 3676459868513552170272317 := by
  unfold tailWord_7159880
  simp only [CollatzResearch.WordTrace]
  refine ⟨130571138650492522498110547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174094851533990029997480729 130571138650492522498110547)
  ·
    refine ⟨195856707975738783747165821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130571138650492522498110547 195856707975738783747165821)
    ·
      refine ⟨73446265490902043905187183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195856707975738783747165821 73446265490902043905187183)
      ·
        refine ⟨110169398236353065857780775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73446265490902043905187183 110169398236353065857780775)
        ·
          refine ⟨165254097354529598786671163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110169398236353065857780775 165254097354529598786671163)
          ·
            refine ⟨247881146031794398180006745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165254097354529598786671163 247881146031794398180006745)
            ·
              refine ⟨185910859523845798635005059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247881146031794398180006745 185910859523845798635005059)
              ·
                refine ⟨278866289285768697952507589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185910859523845798635005059 278866289285768697952507589)
                ·
                  refine ⟨52287429241081630866095173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278866289285768697952507589 52287429241081630866095173)
                  ·
                    refine ⟨9803892982702805787392845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52287429241081630866095173 9803892982702805787392845)
                    ·
                      refine ⟨3676459868513552170272317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9803892982702805787392845 3676459868513552170272317)
                      ·
                        rfl

theorem cell23_7159880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_7159880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159880 prefixEnd_7159880 := by exact prefixLift 7159880
  have htrace : WordTrace (prefixWord ++ tailWord_7159880) baseStart_7159880 baseEnd_7159880 := by
    simpa [prefixWord, tailWord_7159880, baseEnd_7159880] using wordTrace_append hprefix tailTrace_7159880
  have hstable : (prefixWord ++ tailWord_7159880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159880).length < 2 ^ (prefixWord ++ tailWord_7159880).sum := by decide
  have hdescent : baseEnd_7159880 < baseStart_7159880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159911 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_7159911 : Nat := 118140960795 + 7159911 * 2 ^ 59
def prefixEnd_7159911 : Nat := 4983230072969 + 3 ^ 40 * 7159911 * 2
def baseEnd_7159911 : Nat := 3676475786413841548984675

theorem tailTrace_7159911 : CollatzResearch.WordTrace tailWord_7159911 prefixEnd_7159911 3676475786413841548984675 := by
  unfold tailWord_7159911
  simp only [CollatzResearch.WordTrace]
  refine ⟨261143407963872737290599587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174095605309248491527066391 261143407963872737290599587)
  ·
    refine ⟨391715111945809105935899381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261143407963872737290599587 391715111945809105935899381)
    ·
      refine ⟨36723291744919603681490567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391715111945809105935899381 36723291744919603681490567)
      ·
        refine ⟨55084937617379405522235851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36723291744919603681490567 55084937617379405522235851)
        ·
          refine ⟨82627406426069108283353777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55084937617379405522235851 82627406426069108283353777)
          ·
            refine ⟨61970554819551831212515333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82627406426069108283353777 61970554819551831212515333)
            ·
              refine ⟨11619479028665968352346625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61970554819551831212515333 11619479028665968352346625)
              ·
                refine ⟨8714609271499476264259969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11619479028665968352346625 8714609271499476264259969)
                ·
                  refine ⟨6535956953624607198194977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8714609271499476264259969 6535956953624607198194977)
                  ·
                    refine ⟨4901967715218455398646233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6535956953624607198194977 4901967715218455398646233)
                    ·
                      refine ⟨3676475786413841548984675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4901967715218455398646233 3676475786413841548984675)
                      ·
                        rfl

theorem cell23_7159911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_7159911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159911 prefixEnd_7159911 := by exact prefixLift 7159911
  have htrace : WordTrace (prefixWord ++ tailWord_7159911) baseStart_7159911 baseEnd_7159911 := by
    simpa [prefixWord, tailWord_7159911, baseEnd_7159911] using wordTrace_append hprefix tailTrace_7159911
  have hstable : (prefixWord ++ tailWord_7159911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159911).length < 2 ^ (prefixWord ++ tailWord_7159911).sum := by decide
  have hdescent : baseEnd_7159911 < baseStart_7159911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7159927 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 3]
def baseStart_7159927 : Nat := 118140960795 + 7159927 * 2 ^ 59
def prefixEnd_7159927 : Nat := 4983230072969 + 3 ^ 40 * 7159927 * 2
def baseEnd_7159927 : Nat := 3676484002104313486384601

theorem tailTrace_7159927 : CollatzResearch.WordTrace tailWord_7159927 prefixEnd_7159927 3676484002104313486384601 := by
  unfold tailWord_7159927
  simp only [CollatzResearch.WordTrace]
  refine ⟨261143991531814772023182035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174095994354543181348788023 261143991531814772023182035)
  ·
    refine ⟨391715987297722158034773053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261143991531814772023182035 391715987297722158034773053)
    ·
      refine ⟨146893495236645809263039895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391715987297722158034773053 146893495236645809263039895)
      ·
        refine ⟨220340242854968713894559843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146893495236645809263039895 220340242854968713894559843)
        ·
          refine ⟨330510364282453070841839765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220340242854968713894559843 330510364282453070841839765)
          ·
            refine ⟨15492673325739987695711239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 330510364282453070841839765 15492673325739987695711239)
            ·
              refine ⟨23239009988609981543566859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15492673325739987695711239 23239009988609981543566859)
              ·
                refine ⟨34858514982914972315350289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23239009988609981543566859 34858514982914972315350289)
                ·
                  refine ⟨26143886237186229236512717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34858514982914972315350289 26143886237186229236512717)
                  ·
                    refine ⟨9803957338944835963692269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26143886237186229236512717 9803957338944835963692269)
                    ·
                      refine ⟨3676484002104313486384601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9803957338944835963692269 3676484002104313486384601)
                      ·
                        rfl

theorem cell23_7159927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_7159927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7159927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7159927 prefixEnd_7159927 := by exact prefixLift 7159927
  have htrace : WordTrace (prefixWord ++ tailWord_7159927) baseStart_7159927 baseEnd_7159927 := by
    simpa [prefixWord, tailWord_7159927, baseEnd_7159927] using wordTrace_append hprefix tailTrace_7159927
  have hstable : (prefixWord ++ tailWord_7159927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7159927).length < 2 ^ (prefixWord ++ tailWord_7159927).sum := by decide
  have hdescent : baseEnd_7159927 < baseStart_7159927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7159927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160004 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_7160004 : Nat := 118140960795 + 7160004 * 2 ^ 59
def prefixEnd_7160004 : Nat := 4983230072969 + 3 ^ 40 * 7160004 * 2
def baseEnd_7160004 : Nat := 3676523540114709685121747

theorem tailTrace_7160004 : CollatzResearch.WordTrace tailWord_7160004 prefixEnd_7160004 3676523540114709685121747 := by
  unfold tailWord_7160004
  simp only [CollatzResearch.WordTrace]
  refine ⟨130573399976267907086867533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174097866635023876115823377 130573399976267907086867533)
  ·
    refine ⟨48965024991100465157575325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130573399976267907086867533 48965024991100465157575325)
    ·
      refine ⟨18361884371662674434090747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48965024991100465157575325 18361884371662674434090747)
      ·
        refine ⟨27542826557494011651136121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18361884371662674434090747 27542826557494011651136121)
        ·
          refine ⟨20657119918120508738352091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27542826557494011651136121 20657119918120508738352091)
          ·
            refine ⟨30985679877180763107528137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20657119918120508738352091 30985679877180763107528137)
            ·
              refine ⟨23239259907885572330646103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30985679877180763107528137 23239259907885572330646103)
              ·
                refine ⟨34858889861828358495969155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23239259907885572330646103 34858889861828358495969155)
                ·
                  refine ⟨52288334792742537743953733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34858889861828358495969155 52288334792742537743953733)
                  ·
                    refine ⟨9804062773639225826991325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52288334792742537743953733 9804062773639225826991325)
                    ·
                      refine ⟨3676523540114709685121747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9804062773639225826991325 3676523540114709685121747)
                      ·
                        rfl

theorem cell23_7160004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_7160004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160004 prefixEnd_7160004 := by exact prefixLift 7160004
  have htrace : WordTrace (prefixWord ++ tailWord_7160004) baseStart_7160004 baseEnd_7160004 := by
    simpa [prefixWord, tailWord_7160004, baseEnd_7160004] using wordTrace_append hprefix tailTrace_7160004
  have hstable : (prefixWord ++ tailWord_7160004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160004).length < 2 ^ (prefixWord ++ tailWord_7160004).sum := by decide
  have hdescent : baseEnd_7160004 < baseStart_7160004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160021 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_7160021 : Nat := 118140960795 + 7160021 * 2 ^ 59
def prefixEnd_7160021 : Nat := 4983230072969 + 3 ^ 40 * 7160021 * 2
def baseEnd_7160021 : Nat := 3676532269285836118609169

theorem tailTrace_7160021 : CollatzResearch.WordTrace tailWord_7160021 prefixEnd_7160021 3676532269285836118609169 := by
  unfold tailWord_7160021
  simp only [CollatzResearch.WordTrace]
  refine ⟨261147419993474226077103917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174098279995649484051402611 261147419993474226077103917)
  ·
    refine ⟨97930282497552834778913969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261147419993474226077103917 97930282497552834778913969)
    ·
      refine ⟨73447711873164626084185477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97930282497552834778913969 73447711873164626084185477)
      ·
        refine ⟨13771445976218367390784777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73447711873164626084185477 13771445976218367390784777)
        ·
          refine ⟨10328584482163775543088583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13771445976218367390784777 10328584482163775543088583)
          ·
            refine ⟨15492876723245663314632875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10328584482163775543088583 15492876723245663314632875)
            ·
              refine ⟨23239315084868494971949313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15492876723245663314632875 23239315084868494971949313)
              ·
                refine ⟨17429486313651371228961985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23239315084868494971949313 17429486313651371228961985)
                ·
                  refine ⟨13072114735238528421721489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17429486313651371228961985 13072114735238528421721489)
                  ·
                    refine ⟨9804086051428896316291117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13072114735238528421721489 9804086051428896316291117)
                    ·
                      refine ⟨3676532269285836118609169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9804086051428896316291117 3676532269285836118609169)
                      ·
                        rfl

theorem cell23_7160021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_7160021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160021 prefixEnd_7160021 := by exact prefixLift 7160021
  have htrace : WordTrace (prefixWord ++ tailWord_7160021) baseStart_7160021 baseEnd_7160021 := by
    simpa [prefixWord, tailWord_7160021, baseEnd_7160021] using wordTrace_append hprefix tailTrace_7160021
  have hstable : (prefixWord ++ tailWord_7160021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160021).length < 2 ^ (prefixWord ++ tailWord_7160021).sum := by decide
  have hdescent : baseEnd_7160021 < baseStart_7160021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160044 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 4, 3, 2]
def baseStart_7160044 : Nat := 118140960795 + 7160044 * 2 ^ 59
def prefixEnd_7160044 : Nat := 4983230072969 + 3 ^ 40 * 7160044 * 2
def baseEnd_7160044 : Nat := 3676544079340889528621563

theorem tailTrace_7160044 : CollatzResearch.WordTrace tailWord_7160044 prefixEnd_7160044 3676544079340889528621563 := by
  unfold tailWord_7160044
  simp only [CollatzResearch.WordTrace]
  refine ⟨130574129436195450502595593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174098839248260600670127457 130574129436195450502595593)
  ·
    refine ⟨97930597077146587876946695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130574129436195450502595593 97930597077146587876946695)
    ·
      refine ⟨146895895615719881815420043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97930597077146587876946695 146895895615719881815420043)
      ·
        refine ⟨220343843423579822723130065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146895895615719881815420043 220343843423579822723130065)
        ·
          refine ⟨165257882567684867042347549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220343843423579822723130065 165257882567684867042347549)
          ·
            refine ⟨61971705962881825140880331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165257882567684867042347549 61971705962881825140880331)
            ·
              refine ⟨92957558944322737711320497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61971705962881825140880331 92957558944322737711320497)
              ·
                refine ⟨69718169208242053283490373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92957558944322737711320497 69718169208242053283490373)
                ·
                  refine ⟨13072156726545384990654445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69718169208242053283490373 13072156726545384990654445)
                  ·
                    refine ⟨4902058772454519371495417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13072156726545384990654445 4902058772454519371495417)
                    ·
                      refine ⟨3676544079340889528621563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4902058772454519371495417 3676544079340889528621563)
                      ·
                        rfl

theorem cell23_7160044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_7160044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160044 prefixEnd_7160044 := by exact prefixLift 7160044
  have htrace : WordTrace (prefixWord ++ tailWord_7160044) baseStart_7160044 baseEnd_7160044 := by
    simpa [prefixWord, tailWord_7160044, baseEnd_7160044] using wordTrace_append hprefix tailTrace_7160044
  have hstable : (prefixWord ++ tailWord_7160044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160044).length < 2 ^ (prefixWord ++ tailWord_7160044).sum := by decide
  have hdescent : baseEnd_7160044 < baseStart_7160044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160067 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 1, 6]
def baseStart_7160067 : Nat := 118140960795 + 7160067 * 2 ^ 59
def prefixEnd_7160067 : Nat := 4983230072969 + 3 ^ 40 * 7160067 * 2
def baseEnd_7160067 : Nat := 1225518629798647646211319

theorem tailTrace_7160067 : CollatzResearch.WordTrace tailWord_7160067 prefixEnd_7160067 1225518629798647646211319 := by
  unfold tailWord_7160067
  simp only [CollatzResearch.WordTrace]
  refine ⟨261149097751307575933278455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174099398500871717288852303 261149097751307575933278455)
  ·
    refine ⟨391723646626961363899917683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261149097751307575933278455 391723646626961363899917683)
    ·
      refine ⟨587585469940442045849876525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391723646626961363899917683 587585469940442045849876525)
      ·
        refine ⟨220344551227665767193703697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587585469940442045849876525 220344551227665767193703697)
        ·
          refine ⟨165258413420749325395277773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220344551227665767193703697 165258413420749325395277773)
          ·
            refine ⟨61971905032780997023229165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165258413420749325395277773 61971905032780997023229165)
            ·
              refine ⟨23239464387292873883710937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61971905032780997023229165 23239464387292873883710937)
              ·
                refine ⟨17429598290469655412783203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23239464387292873883710937 17429598290469655412783203)
                ·
                  refine ⟨26144397435704483119174805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17429598290469655412783203 26144397435704483119174805)
                  ·
                    refine ⟨1225518629798647646211319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26144397435704483119174805 1225518629798647646211319)
                    ·
                      rfl

theorem cell23_7160067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 6].length) (baseStart_7160067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160067 prefixEnd_7160067 := by exact prefixLift 7160067
  have htrace : WordTrace (prefixWord ++ tailWord_7160067) baseStart_7160067 baseEnd_7160067 := by
    simpa [prefixWord, tailWord_7160067, baseEnd_7160067] using wordTrace_append hprefix tailTrace_7160067
  have hstable : (prefixWord ++ tailWord_7160067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160067).length < 2 ^ (prefixWord ++ tailWord_7160067).sum := by decide
  have hdescent : baseEnd_7160067 < baseStart_7160067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160074 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_7160074 : Nat := 118140960795 + 7160074 * 2 ^ 59
def prefixEnd_7160074 : Nat := 4983230072969 + 3 ^ 40 * 7160074 * 2
def baseEnd_7160074 : Nat := 3676559483760524411246425

theorem tailTrace_7160074 : CollatzResearch.WordTrace tailWord_7160074 prefixEnd_7160074 3676559483760524411246425 := by
  unfold tailWord_7160074
  simp only [CollatzResearch.WordTrace]
  refine ⟨65287338265570554032195819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174099568708188144085855517 65287338265570554032195819)
  ·
    refine ⟨97931007398355831048293729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65287338265570554032195819 97931007398355831048293729)
    ·
      refine ⟨73448255548766873286220297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97931007398355831048293729 73448255548766873286220297)
      ·
        refine ⟨55086191661575154964665223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73448255548766873286220297 55086191661575154964665223)
        ·
          refine ⟨82629287492362732446997835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55086191661575154964665223 82629287492362732446997835)
          ·
            refine ⟨123943931238544098670496753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82629287492362732446997835 123943931238544098670496753)
            ·
              refine ⟨92957948428908074002872565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123943931238544098670496753 92957948428908074002872565)
              ·
                refine ⟨8714807665210131937769303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92957948428908074002872565 8714807665210131937769303)
                ·
                  refine ⟨13072211497815197906653955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8714807665210131937769303 13072211497815197906653955)
                  ·
                    refine ⟨19608317246722796859980933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13072211497815197906653955 19608317246722796859980933)
                    ·
                      refine ⟨3676559483760524411246425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19608317246722796859980933 3676559483760524411246425)
                      ·
                        rfl

theorem cell23_7160074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_7160074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160074 prefixEnd_7160074 := by exact prefixLift 7160074
  have htrace : WordTrace (prefixWord ++ tailWord_7160074) baseStart_7160074 baseEnd_7160074 := by
    simpa [prefixWord, tailWord_7160074, baseEnd_7160074] using wordTrace_append hprefix tailTrace_7160074
  have hstable : (prefixWord ++ tailWord_7160074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160074).length < 2 ^ (prefixWord ++ tailWord_7160074).sum := by decide
  have hdescent : baseEnd_7160074 < baseStart_7160074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160097 : List Nat := [1, 2, 3, 2, 1, 1, 5, 8]
def baseStart_7160097 : Nat := 118140960795 + 7160097 * 2 ^ 59
def prefixEnd_7160097 : Nat := 4983230072969 + 3 ^ 40 * 7160097 * 2
def baseEnd_7160097 : Nat := 136169307178354734120697

theorem tailTrace_7160097 : CollatzResearch.WordTrace tailWord_7160097 prefixEnd_7160097 136169307178354734120697 := by
  unfold tailWord_7160097
  simp only [CollatzResearch.WordTrace]
  refine ⟨261150191941198891056870545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174100127960799260704580363 261150191941198891056870545)
  ·
    refine ⟨195862643955899168292652909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261150191941198891056870545 195862643955899168292652909)
    ·
      refine ⟨73448491483462188109744841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195862643955899168292652909 73448491483462188109744841)
      ·
        refine ⟨55086368612596641082308631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73448491483462188109744841 55086368612596641082308631)
        ·
          refine ⟨82629552918894961623462947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55086368612596641082308631 82629552918894961623462947)
          ·
            refine ⟨123944329378342442435194421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82629552918894961623462947 123944329378342442435194421)
            ·
              refine ⟨11619780879219603978299477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123944329378342442435194421 11619780879219603978299477)
              ·
                refine ⟨136169307178354734120697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11619780879219603978299477 136169307178354734120697)
                ·
                  rfl

theorem cell23_7160097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 8].length) (baseStart_7160097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160097 prefixEnd_7160097 := by exact prefixLift 7160097
  have htrace : WordTrace (prefixWord ++ tailWord_7160097) baseStart_7160097 baseEnd_7160097 := by
    simpa [prefixWord, tailWord_7160097, baseEnd_7160097] using wordTrace_append hprefix tailTrace_7160097
  have hstable : (prefixWord ++ tailWord_7160097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160097).length < 2 ^ (prefixWord ++ tailWord_7160097).sum := by decide
  have hdescent : baseEnd_7160097 < baseStart_7160097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160124 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_7160124 : Nat := 118140960795 + 7160124 * 2 ^ 59
def prefixEnd_7160124 : Nat := 4983230072969 + 3 ^ 40 * 7160124 * 2
def baseEnd_7160124 : Nat := 3676585157793249215621195

theorem tailTrace_7160124 : CollatzResearch.WordTrace tailWord_7160124 prefixEnd_7160124 3676585157793249215621195 := by
  unfold tailWord_7160124
  simp only [CollatzResearch.WordTrace]
  refine ⟨130575588356050537334051713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174100784474734049778735617 130575588356050537334051713)
  ·
    refine ⟨97931691267037903000538785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130575588356050537334051713 97931691267037903000538785)
    ·
      refine ⟨73448768450278427250404089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97931691267037903000538785 73448768450278427250404089)
      ·
        refine ⟨55086576337708820437803067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73448768450278427250404089 55086576337708820437803067)
        ·
          refine ⟨82629864506563230656704601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55086576337708820437803067 82629864506563230656704601)
          ·
            refine ⟨61972398379922422992528451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82629864506563230656704601 61972398379922422992528451)
            ·
              refine ⟨92958597569883634488792677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61972398379922422992528451 92958597569883634488792677)
              ·
                refine ⟨17429737044353181466648627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92958597569883634488792677 17429737044353181466648627)
                ·
                  refine ⟨26144605566529772199972941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17429737044353181466648627 26144605566529772199972941)
                  ·
                    refine ⟨9804227087448664574989853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26144605566529772199972941 9804227087448664574989853)
                    ·
                      refine ⟨3676585157793249215621195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9804227087448664574989853 3676585157793249215621195)
                      ·
                        rfl

theorem cell23_7160124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_7160124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160124 prefixEnd_7160124 := by exact prefixLift 7160124
  have htrace : WordTrace (prefixWord ++ tailWord_7160124) baseStart_7160124 baseEnd_7160124 := by
    simpa [prefixWord, tailWord_7160124, baseEnd_7160124] using wordTrace_append hprefix tailTrace_7160124
  have hstable : (prefixWord ++ tailWord_7160124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160124).length < 2 ^ (prefixWord ++ tailWord_7160124).sum := by decide
  have hdescent : baseEnd_7160124 < baseStart_7160124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160147 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 4]
def baseStart_7160147 : Nat := 118140960795 + 7160147 * 2 ^ 59
def prefixEnd_7160147 : Nat := 4983230072969 + 3 ^ 40 * 7160147 * 2
def baseEnd_7160147 : Nat := 3676596967848302625633589

theorem tailTrace_7160147 : CollatzResearch.WordTrace tailWord_7160147 prefixEnd_7160147 3676596967848302625633589 := by
  unfold tailWord_7160147
  simp only [CollatzResearch.WordTrace]
  refine ⟨261152015591017749596190695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174101343727345166397460463 261152015591017749596190695)
  ·
    refine ⟨391728023386526624394286043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261152015591017749596190695 391728023386526624394286043)
    ·
      refine ⟨587592035079789936591429065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391728023386526624394286043 587592035079789936591429065)
      ·
        refine ⟨440694026309842452443571799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587592035079789936591429065 440694026309842452443571799)
        ·
          refine ⟨661041039464763678665357699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440694026309842452443571799 661041039464763678665357699)
          ·
            refine ⟨991561559197145517998036549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661041039464763678665357699 991561559197145517998036549)
            ·
              refine ⟨185917792349464784624631853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 991561559197145517998036549 185917792349464784624631853)
              ·
                refine ⟨69719172131049294234236945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185917792349464784624631853 69719172131049294234236945)
                ·
                  refine ⟨52289379098286970675677709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69719172131049294234236945 52289379098286970675677709)
                  ·
                    refine ⟨19608517161857614003379141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52289379098286970675677709 19608517161857614003379141)
                    ·
                      refine ⟨3676596967848302625633589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19608517161857614003379141 3676596967848302625633589)
                      ·
                        rfl

theorem cell23_7160147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_7160147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160147 prefixEnd_7160147 := by exact prefixLift 7160147
  have htrace : WordTrace (prefixWord ++ tailWord_7160147) baseStart_7160147 baseEnd_7160147 := by
    simpa [prefixWord, tailWord_7160147, baseEnd_7160147] using wordTrace_append hprefix tailTrace_7160147
  have hstable : (prefixWord ++ tailWord_7160147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160147).length < 2 ^ (prefixWord ++ tailWord_7160147).sum := by decide
  have hdescent : baseEnd_7160147 < baseStart_7160147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160168 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_7160168 : Nat := 118140960795 + 7160168 * 2 ^ 59
def prefixEnd_7160168 : Nat := 4983230072969 + 3 ^ 40 * 7160168 * 2
def baseEnd_7160168 : Nat := 3676607750942047043470993

theorem tailTrace_7160168 : CollatzResearch.WordTrace tailWord_7160168 prefixEnd_7160168 3676607750942047043470993 := by
  unfold tailWord_7160168
  simp only [CollatzResearch.WordTrace]
  refine ⟨130576390761970835091352579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174101854349294446788470105 130576390761970835091352579)
  ·
    refine ⟨195864586142956252637028869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130576390761970835091352579 195864586142956252637028869)
    ·
      refine ⟨36724609901804297369442913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195864586142956252637028869 36724609901804297369442913)
      ·
        refine ⟨27543457426353223027082185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36724609901804297369442913 27543457426353223027082185)
        ·
          refine ⟨20657593069764917270311639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27543457426353223027082185 20657593069764917270311639)
          ·
            refine ⟨30986389604647375905467459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20657593069764917270311639 30986389604647375905467459)
            ·
              refine ⟨46479584406971063858201189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30986389604647375905467459 46479584406971063858201189)
              ·
                refine ⟨8714922076307074473412723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46479584406971063858201189 8714922076307074473412723)
                ·
                  refine ⟨13072383114460611710119085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8714922076307074473412723 13072383114460611710119085)
                  ·
                    refine ⟨4902143667922729391294657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13072383114460611710119085 4902143667922729391294657)
                    ·
                      refine ⟨3676607750942047043470993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4902143667922729391294657 3676607750942047043470993)
                      ·
                        rfl

theorem cell23_7160168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_7160168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160168 prefixEnd_7160168 := by exact prefixLift 7160168
  have htrace : WordTrace (prefixWord ++ tailWord_7160168) baseStart_7160168 baseEnd_7160168 := by
    simpa [prefixWord, tailWord_7160168, baseEnd_7160168] using wordTrace_append hprefix tailTrace_7160168
  have hstable : (prefixWord ++ tailWord_7160168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160168).length < 2 ^ (prefixWord ++ tailWord_7160168).sum := by decide
  have hdescent : baseEnd_7160168 < baseStart_7160168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160197 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_7160197 : Nat := 118140960795 + 7160197 * 2 ^ 59
def prefixEnd_7160197 : Nat := 4983230072969 + 3 ^ 40 * 7160197 * 2
def baseEnd_7160197 : Nat := 3676622641881027430008359

theorem tailTrace_7160197 : CollatzResearch.WordTrace tailWord_7160197 prefixEnd_7160197 3676622641881027430008359 := by
  unfold tailWord_7160197
  simp only [CollatzResearch.WordTrace]
  refine ⟨261153839240836608135510845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174102559493891072090340563 261153839240836608135510845)
  ·
    refine ⟨97932689715313728050816567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261153839240836608135510845 97932689715313728050816567)
    ·
      refine ⟨146899034572970592076224851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97932689715313728050816567 146899034572970592076224851)
      ·
        refine ⟨220348551859455888114337277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146899034572970592076224851 220348551859455888114337277)
        ·
          refine ⟨82630706947295958042876479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220348551859455888114337277 82630706947295958042876479)
          ·
            refine ⟨123946060420943937064314719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82630706947295958042876479 123946060420943937064314719)
            ·
              refine ⟨185919090631415905596472079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123946060420943937064314719 185919090631415905596472079)
              ·
                refine ⟨278878635947123858394708119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185919090631415905596472079 278878635947123858394708119)
                ·
                  refine ⟨418317953920685787592062179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278878635947123858394708119 418317953920685787592062179)
                  ·
                    refine ⟨627476930881028681388093269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 418317953920685787592062179 627476930881028681388093269)
                    ·
                      refine ⟨3676622641881027430008359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 627476930881028681388093269 3676622641881027430008359)
                      ·
                        rfl

theorem cell23_7160197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_7160197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160197 prefixEnd_7160197 := by exact prefixLift 7160197
  have htrace : WordTrace (prefixWord ++ tailWord_7160197) baseStart_7160197 baseEnd_7160197 := by
    simpa [prefixWord, tailWord_7160197, baseEnd_7160197] using wordTrace_append hprefix tailTrace_7160197
  have hstable : (prefixWord ++ tailWord_7160197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160197).length < 2 ^ (prefixWord ++ tailWord_7160197).sum := by decide
  have hdescent : baseEnd_7160197 < baseStart_7160197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160204 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 7]
def baseStart_7160204 : Nat := 118140960795 + 7160204 * 2 ^ 59
def prefixEnd_7160204 : Nat := 4983230072969 + 3 ^ 40 * 7160204 * 2
def baseEnd_7160204 : Nat := 408514026249512100291203

theorem tailTrace_7160204 : CollatzResearch.WordTrace tailWord_7160204 prefixEnd_7160204 408514026249512100291203 := by
  unfold tailWord_7160204
  simp only [CollatzResearch.WordTrace]
  refine ⟨130577047275905624165507833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174102729701207498887343777 130577047275905624165507833)
  ·
    refine ⟨97932785456929218124130875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130577047275905624165507833 97932785456929218124130875)
    ·
      refine ⟨146899178185393827186196313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97932785456929218124130875 146899178185393827186196313)
      ·
        refine ⟨110174383639045370389647235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146899178185393827186196313 110174383639045370389647235)
        ·
          refine ⟨165261575458568055584470853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110174383639045370389647235 165261575458568055584470853)
          ·
            refine ⟨30986545398481510422088285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165261575458568055584470853 30986545398481510422088285)
            ·
              refine ⟨11619954524430566408283107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30986545398481510422088285 11619954524430566408283107)
              ·
                refine ⟨17429931786645849612424661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11619954524430566408283107 17429931786645849612424661)
                ·
                  refine ⟨408514026249512100291203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17429931786645849612424661 408514026249512100291203)
                  ·
                    rfl

theorem cell23_7160204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_7160204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160204 prefixEnd_7160204 := by exact prefixLift 7160204
  have htrace : WordTrace (prefixWord ++ tailWord_7160204) baseStart_7160204 baseEnd_7160204 := by
    simpa [prefixWord, tailWord_7160204, baseEnd_7160204] using wordTrace_append hprefix tailTrace_7160204
  have hstable : (prefixWord ++ tailWord_7160204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160204).length < 2 ^ (prefixWord ++ tailWord_7160204).sum := by decide
  have hdescent : baseEnd_7160204 < baseStart_7160204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160215 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 2, 2, 2]
def baseStart_7160215 : Nat := 118140960795 + 7160215 * 2 ^ 59
def prefixEnd_7160215 : Nat := 4983230072969 + 3 ^ 40 * 7160215 * 2
def baseEnd_7160215 : Nat := 3676631884532808359583277

theorem tailTrace_7160215 : CollatzResearch.WordTrace tailWord_7160215 prefixEnd_7160215 3676631884532808359583277 := by
  unfold tailWord_7160215
  simp only [CollatzResearch.WordTrace]
  refine ⟨261154495754771397209666099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174102997169847598139777399 261154495754771397209666099)
  ·
    refine ⟨391731743632157095814499149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261154495754771397209666099 391731743632157095814499149)
    ·
      refine ⟨146899403862058910930437181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391731743632157095814499149 146899403862058910930437181)
      ·
        refine ⟨55087276448272091598913943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146899403862058910930437181 55087276448272091598913943)
        ·
          refine ⟨82630914672408137398370915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55087276448272091598913943 82630914672408137398370915)
          ·
            refine ⟨123946372008612206097556373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82630914672408137398370915 123946372008612206097556373)
            ·
              refine ⟨5809986187903697160822955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123946372008612206097556373 5809986187903697160822955)
              ·
                refine ⟨8714979281855545741234433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5809986187903697160822955 8714979281855545741234433)
                ·
                  refine ⟨6536234461391659305925825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8714979281855545741234433 6536234461391659305925825)
                  ·
                    refine ⟨4902175846043744479444369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6536234461391659305925825 4902175846043744479444369)
                    ·
                      refine ⟨3676631884532808359583277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4902175846043744479444369 3676631884532808359583277)
                      ·
                        rfl

theorem cell23_7160215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_7160215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160215 prefixEnd_7160215 := by exact prefixLift 7160215
  have htrace : WordTrace (prefixWord ++ tailWord_7160215) baseStart_7160215 baseEnd_7160215 := by
    simpa [prefixWord, tailWord_7160215, baseEnd_7160215] using wordTrace_append hprefix tailTrace_7160215
  have hstable : (prefixWord ++ tailWord_7160215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160215).length < 2 ^ (prefixWord ++ tailWord_7160215).sum := by decide
  have hdescent : baseEnd_7160215 < baseStart_7160215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160281 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 3, 4]
def baseStart_7160281 : Nat := 118140960795 + 7160281 * 2 ^ 59
def prefixEnd_7160281 : Nat := 4983230072969 + 3 ^ 40 * 7160281 * 2
def baseEnd_7160281 : Nat := 1225555258085335033785991

theorem tailTrace_7160281 : CollatzResearch.WordTrace tailWord_7160281 prefixEnd_7160281 1225555258085335033785991 := by
  unfold tailWord_7160281
  simp only [CollatzResearch.WordTrace]
  refine ⟨261156902972532290481568697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174104601981688193654379131 261156902972532290481568697)
  ·
    refine ⟨195867677229399217861176523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261156902972532290481568697 195867677229399217861176523)
    ·
      refine ⟨293801515844098826791764785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195867677229399217861176523 293801515844098826791764785)
      ·
        refine ⟨220351136883074120093823589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293801515844098826791764785 220351136883074120093823589)
        ·
          refine ⟨41315838165576397517591923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220351136883074120093823589 41315838165576397517591923)
          ·
            refine ⟨61973757248364596276387885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41315838165576397517591923 61973757248364596276387885)
            ·
              refine ⟨23240158968136723603645457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61973757248364596276387885 23240158968136723603645457)
              ·
                refine ⟨17430119226102542702734093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23240158968136723603645457 17430119226102542702734093)
                ·
                  refine ⟨6536294709788453513525285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17430119226102542702734093 6536294709788453513525285)
                  ·
                    refine ⟨1225555258085335033785991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6536294709788453513525285 1225555258085335033785991)
                    ·
                      rfl

theorem cell23_7160281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 4].length) (baseStart_7160281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160281 prefixEnd_7160281 := by exact prefixLift 7160281
  have htrace : WordTrace (prefixWord ++ tailWord_7160281) baseStart_7160281 baseEnd_7160281 := by
    simpa [prefixWord, tailWord_7160281, baseEnd_7160281] using wordTrace_append hprefix tailTrace_7160281
  have hstable : (prefixWord ++ tailWord_7160281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160281).length < 2 ^ (prefixWord ++ tailWord_7160281).sum := by decide
  have hdescent : baseEnd_7160281 < baseStart_7160281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160301 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7160301 : Nat := 118140960795 + 7160301 * 2 ^ 59
def prefixEnd_7160301 : Nat := 4983230072969 + 3 ^ 40 * 7160301 * 2
def baseEnd_7160301 : Nat := 3676676043869095023107881

theorem tailTrace_7160301 : CollatzResearch.WordTrace tailWord_7160301 prefixEnd_7160301 3676676043869095023107881 := by
  unfold tailWord_7160301
  simp only [CollatzResearch.WordTrace]
  refine ⟨261157632432459833897296757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174105088288306555931531171 261157632432459833897296757)
  ·
    refine ⟨24483528040543109427871571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261157632432459833897296757 24483528040543109427871571)
    ·
      refine ⟨36725292060814664141807357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24483528040543109427871571 36725292060814664141807357)
      ·
        refine ⟨13771984522805499053177759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36725292060814664141807357 13771984522805499053177759)
        ·
          refine ⟨20657976784208248579766639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13771984522805499053177759 20657976784208248579766639)
          ·
            refine ⟨30986965176312372869649959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20657976784208248579766639 30986965176312372869649959)
            ·
              refine ⟨46480447764468559304474939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30986965176312372869649959 46480447764468559304474939)
              ·
                refine ⟨69720671646702838956712409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46480447764468559304474939 69720671646702838956712409)
                ·
                  refine ⟨52290503735027129217534307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69720671646702838956712409 52290503735027129217534307)
                  ·
                    refine ⟨78435755602540693826301461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52290503735027129217534307 78435755602540693826301461)
                    ·
                      refine ⟨3676676043869095023107881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78435755602540693826301461 3676676043869095023107881)
                      ·
                        rfl

theorem cell23_7160301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7160301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160301 prefixEnd_7160301 := by exact prefixLift 7160301
  have htrace : WordTrace (prefixWord ++ tailWord_7160301) baseStart_7160301 baseEnd_7160301 := by
    simpa [prefixWord, tailWord_7160301, baseEnd_7160301] using wordTrace_append hprefix tailTrace_7160301
  have hstable : (prefixWord ++ tailWord_7160301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160301).length < 2 ^ (prefixWord ++ tailWord_7160301).sum := by decide
  have hdescent : baseEnd_7160301 < baseStart_7160301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160348 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_7160348 : Nat := 118140960795 + 7160348 * 2 ^ 59
def prefixEnd_7160348 : Nat := 4983230072969 + 3 ^ 40 * 7160348 * 2
def baseEnd_7160348 : Nat := 3676700177459856339220165

theorem tailTrace_7160348 : CollatzResearch.WordTrace tailWord_7160348 prefixEnd_7160348 3676700177459856339220165 := by
  unfold tailWord_7160348
  simp only [CollatzResearch.WordTrace]
  refine ⟨130579673331644780462128849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174106231108859707282838465 130579673331644780462128849)
  ·
    refine ⟨97934754998733585346596637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130579673331644780462128849 97934754998733585346596637)
    ·
      refine ⟨36725533124525094504973739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97934754998733585346596637 36725533124525094504973739)
      ·
        refine ⟨55088299686787641757460609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36725533124525094504973739 55088299686787641757460609)
        ·
          refine ⟨41316224765090731318095457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55088299686787641757460609 41316224765090731318095457)
          ·
            refine ⟨30987168573818048488571593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41316224765090731318095457 30987168573818048488571593)
            ·
              refine ⟨23240376430363536366428695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30987168573818048488571593 23240376430363536366428695)
              ·
                refine ⟨34860564645545304549643043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23240376430363536366428695 34860564645545304549643043)
                ·
                  refine ⟨52290846968317956824464565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34860564645545304549643043 52290846968317956824464565)
                  ·
                    refine ⟨4902266903279808452293553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52290846968317956824464565 4902266903279808452293553)
                    ·
                      refine ⟨3676700177459856339220165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4902266903279808452293553 3676700177459856339220165)
                      ·
                        rfl

theorem cell23_7160348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_7160348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160348 prefixEnd_7160348 := by exact prefixLift 7160348
  have htrace : WordTrace (prefixWord ++ tailWord_7160348) baseStart_7160348 baseEnd_7160348 := by
    simpa [prefixWord, tailWord_7160348, baseEnd_7160348] using wordTrace_append hprefix tailTrace_7160348
  have hstable : (prefixWord ++ tailWord_7160348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160348).length < 2 ^ (prefixWord ++ tailWord_7160348).sum := by decide
  have hdescent : baseEnd_7160348 < baseStart_7160348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160371 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 4, 4]
def baseStart_7160371 : Nat := 118140960795 + 7160371 * 2 ^ 59
def prefixEnd_7160371 : Nat := 4983230072969 + 3 ^ 40 * 7160371 * 2
def baseEnd_7160371 : Nat := 1225570662504969916410853

theorem tailTrace_7160371 : CollatzResearch.WordTrace tailWord_7160371 prefixEnd_7160371 1225570662504969916410853 := by
  unfold tailWord_7160371
  simp only [CollatzResearch.WordTrace]
  refine ⟨261160185542206235852344967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174106790361470823901563311 261160185542206235852344967)
  ·
    refine ⟨391740278313309353778517451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261160185542206235852344967 391740278313309353778517451)
    ·
      refine ⟨587610417469964030667776177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391740278313309353778517451 587610417469964030667776177)
      ·
        refine ⟨440707813102473023000832133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587610417469964030667776177 440707813102473023000832133)
        ·
          refine ⟨82632714956713691812656025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440707813102473023000832133 82632714956713691812656025)
          ·
            refine ⟨61974536217535268859492019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82632714956713691812656025 61974536217535268859492019)
            ·
              refine ⟨92961804326302903289238029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61974536217535268859492019 92961804326302903289238029)
              ·
                refine ⟨34860676622363588733464261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92961804326302903289238029 34860676622363588733464261)
                ·
                  refine ⟨6536376866693172887524549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34860676622363588733464261 6536376866693172887524549)
                  ·
                    refine ⟨1225570662504969916410853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6536376866693172887524549 1225570662504969916410853)
                    ·
                      rfl

theorem cell23_7160371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 4].length) (baseStart_7160371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160371 prefixEnd_7160371 := by exact prefixLift 7160371
  have htrace : WordTrace (prefixWord ++ tailWord_7160371) baseStart_7160371 baseEnd_7160371 := by
    simpa [prefixWord, tailWord_7160371, baseEnd_7160371] using wordTrace_append hprefix tailTrace_7160371
  have hstable : (prefixWord ++ tailWord_7160371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160371).length < 2 ^ (prefixWord ++ tailWord_7160371).sum := by decide
  have hdescent : baseEnd_7160371 < baseStart_7160371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160384 : List Nat := [2, 1, 1, 2, 2, 2, 3, 10]
def baseStart_7160384 : Nat := 118140960795 + 7160384 * 2 ^ 59
def prefixEnd_7160384 : Nat := 4983230072969 + 3 ^ 40 * 7160384 * 2
def baseEnd_7160384 : Nat := 136174765287534007347037

theorem tailTrace_7160384 : CollatzResearch.WordTrace tailWord_7160384 prefixEnd_7160384 136174765287534007347037 := by
  unfold tailWord_7160384
  simp only [CollatzResearch.WordTrace]
  refine ⟨130580329845579569536284103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174107106460772759381712137 130580329845579569536284103)
  ·
    refine ⟨195870494768369354304426155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130580329845579569536284103 195870494768369354304426155)
    ·
      refine ⟨293805742152554031456639233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195870494768369354304426155 293805742152554031456639233)
      ·
        refine ⟨220354306614415523592479425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293805742152554031456639233 220354306614415523592479425)
        ·
          refine ⟨165265729960811642694359569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220354306614415523592479425 165265729960811642694359569)
          ·
            refine ⟨123949297470608732020769677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165265729960811642694359569 123949297470608732020769677)
            ·
              refine ⟨46480986551478274507788629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123949297470608732020769677 46480986551478274507788629)
              ·
                refine ⟨136174765287534007347037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46480986551478274507788629 136174765287534007347037)
                ·
                  rfl

theorem cell23_7160384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 10].length) (baseStart_7160384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160384 prefixEnd_7160384 := by exact prefixLift 7160384
  have htrace : WordTrace (prefixWord ++ tailWord_7160384) baseStart_7160384 baseEnd_7160384 := by
    simpa [prefixWord, tailWord_7160384, baseEnd_7160384] using wordTrace_append hprefix tailTrace_7160384
  have hstable : (prefixWord ++ tailWord_7160384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160384).length < 2 ^ (prefixWord ++ tailWord_7160384).sum := by decide
  have hdescent : baseEnd_7160384 < baseStart_7160384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160391 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_7160391 : Nat := 118140960795 + 7160391 * 2 ^ 59
def prefixEnd_7160391 : Nat := 4983230072969 + 3 ^ 40 * 7160391 * 2
def baseEnd_7160391 : Nat := 3676722257127999670982467

theorem tailTrace_7160391 : CollatzResearch.WordTrace tailWord_7160391 prefixEnd_7160391 3676722257127999670982467 := by
  unfold tailWord_7160391
  simp only [CollatzResearch.WordTrace]
  refine ⟨261160915002133779268073027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174107276668089186178715351 261160915002133779268073027)
  ·
    refine ⟨391741372503200668902109541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261160915002133779268073027 391741372503200668902109541)
    ·
      refine ⟨73451507344350125419145539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391741372503200668902109541 73451507344350125419145539)
      ·
        refine ⟨110177261016525188128718309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73451507344350125419145539 110177261016525188128718309)
        ·
          refine ⟨20658236440598472774134683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110177261016525188128718309 20658236440598472774134683)
          ·
            refine ⟨30987354660897709161202025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20658236440598472774134683 30987354660897709161202025)
            ·
              refine ⟨23240515995673281870901519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30987354660897709161202025 23240515995673281870901519)
              ·
                refine ⟨34860773993509922806352279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23240515995673281870901519 34860773993509922806352279)
                ·
                  refine ⟨52291160990264884209528419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34860773993509922806352279 52291160990264884209528419)
                  ·
                    refine ⟨78436741485397326314292629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52291160990264884209528419 78436741485397326314292629)
                    ·
                      refine ⟨3676722257127999670982467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78436741485397326314292629 3676722257127999670982467)
                      ·
                        rfl

theorem cell23_7160391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_7160391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160391 prefixEnd_7160391 := by exact prefixLift 7160391
  have htrace : WordTrace (prefixWord ++ tailWord_7160391) baseStart_7160391 baseEnd_7160391 := by
    simpa [prefixWord, tailWord_7160391, baseEnd_7160391] using wordTrace_append hprefix tailTrace_7160391
  have hstable : (prefixWord ++ tailWord_7160391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160391).length < 2 ^ (prefixWord ++ tailWord_7160391).sum := by decide
  have hdescent : baseEnd_7160391 < baseStart_7160391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160412 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_7160412 : Nat := 118140960795 + 7160412 * 2 ^ 59
def prefixEnd_7160412 : Nat := 4983230072969 + 3 ^ 40 * 7160412 * 2
def baseEnd_7160412 : Nat := 3676733040221744088819871

theorem tailTrace_7160412 : CollatzResearch.WordTrace tailWord_7160412 prefixEnd_7160412 3676733040221744088819871 := by
  unfold tailWord_7160412
  simp only [CollatzResearch.WordTrace]
  refine ⟨130580840467528849927293745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174107787290038466569724993 130580840467528849927293745)
  ·
    refine ⟨97935630350646637445470309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130580840467528849927293745 97935630350646637445470309)
    ·
      refine ⟨18362930690746244521025683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97935630350646637445470309 18362930690746244521025683)
      ·
        refine ⟨27544396036119366781538525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18362930690746244521025683 27544396036119366781538525)
        ·
          refine ⟨10329148513544762543076947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27544396036119366781538525 10329148513544762543076947)
          ·
            refine ⟨15493722770317143814615421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329148513544762543076947 15493722770317143814615421)
            ·
              refine ⟨5810146038868928930480783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15493722770317143814615421 5810146038868928930480783)
              ·
                refine ⟨8715219058303393395721175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5810146038868928930480783 8715219058303393395721175)
                ·
                  refine ⟨13072828587455090093581763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8715219058303393395721175 13072828587455090093581763)
                  ·
                    refine ⟨19609242881182635140372645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13072828587455090093581763 19609242881182635140372645)
                    ·
                      refine ⟨3676733040221744088819871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19609242881182635140372645 3676733040221744088819871)
                      ·
                        rfl

theorem cell23_7160412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_7160412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160412 prefixEnd_7160412 := by exact prefixLift 7160412
  have htrace : WordTrace (prefixWord ++ tailWord_7160412) baseStart_7160412 baseEnd_7160412 := by
    simpa [prefixWord, tailWord_7160412, baseEnd_7160412] using wordTrace_append hprefix tailTrace_7160412
  have hstable : (prefixWord ++ tailWord_7160412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160412).length < 2 ^ (prefixWord ++ tailWord_7160412).sum := by decide
  have hdescent : baseEnd_7160412 < baseStart_7160412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160418 : List Nat := [3, 3, 2, 3, 1, 11]
def baseStart_7160418 : Nat := 118140960795 + 7160418 * 2 ^ 59
def prefixEnd_7160418 : Nat := 4983230072969 + 3 ^ 40 * 7160418 * 2
def baseEnd_7160418 : Nat := 15130601321422514672201

theorem tailTrace_7160418 : CollatzResearch.WordTrace tailWord_7160418 prefixEnd_7160418 15130601321422514672201 := by
  unfold tailWord_7160418
  simp only [CollatzResearch.WordTrace]
  refine ⟨65290474943258990719826477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174107933182023975252870605 65290474943258990719826477)
  ·
    refine ⟨24483928103722121519934929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65290474943258990719826477 24483928103722121519934929)
    ·
      refine ⟨18362946077791591139951197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24483928103722121519934929 18362946077791591139951197)
      ·
        refine ⟨6886104779171846677481699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18362946077791591139951197 6886104779171846677481699)
        ·
          refine ⟨10329157168757770016222549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6886104779171846677481699 10329157168757770016222549)
          ·
            refine ⟨15130601321422514672201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10329157168757770016222549 15130601321422514672201)
            ·
              rfl

theorem cell23_7160418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 11].length) (baseStart_7160418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160418 prefixEnd_7160418 := by exact prefixLift 7160418
  have htrace : WordTrace (prefixWord ++ tailWord_7160418) baseStart_7160418 baseEnd_7160418 := by
    simpa [prefixWord, tailWord_7160418, baseEnd_7160418] using wordTrace_append hprefix tailTrace_7160418
  have hstable : (prefixWord ++ tailWord_7160418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160418).length < 2 ^ (prefixWord ++ tailWord_7160418).sum := by decide
  have hdescent : baseEnd_7160418 < baseStart_7160418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160428 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 3]
def baseStart_7160428 : Nat := 118140960795 + 7160428 * 2 ^ 59
def prefixEnd_7160428 : Nat := 4983230072969 + 3 ^ 40 * 7160428 * 2
def baseEnd_7160428 : Nat := 3676741255912216026219797

theorem tailTrace_7160428 : CollatzResearch.WordTrace tailWord_7160428 prefixEnd_7160428 3676741255912216026219797 := by
  unfold tailWord_7160428
  simp only [CollatzResearch.WordTrace]
  refine ⟨130581132251499867293584969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174108176335333156391446625 130581132251499867293584969)
  ·
    refine ⟨97935849188624900470188727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130581132251499867293584969 97935849188624900470188727)
    ·
      refine ⟨146903773782937350705283091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97935849188624900470188727 146903773782937350705283091)
      ·
        refine ⟨220355660674406026057924637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146903773782937350705283091 220355660674406026057924637)
        ·
          refine ⟨82633372752902259771721739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220355660674406026057924637 82633372752902259771721739)
          ·
            refine ⟨123950059129353389657582609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82633372752902259771721739 123950059129353389657582609)
            ·
              refine ⟨92962544347015042243186957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123950059129353389657582609 92962544347015042243186957)
              ·
                refine ⟨34860954130130640841195109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92962544347015042243186957 34860954130130640841195109)
                ·
                  refine ⟨6536428899399495157724083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34860954130130640841195109 6536428899399495157724083)
                  ·
                    refine ⟨9804643349099242736586125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6536428899399495157724083 9804643349099242736586125)
                    ·
                      refine ⟨3676741255912216026219797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9804643349099242736586125 3676741255912216026219797)
                      ·
                        rfl

theorem cell23_7160428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_7160428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160428 prefixEnd_7160428 := by exact prefixLift 7160428
  have htrace : WordTrace (prefixWord ++ tailWord_7160428) baseStart_7160428 baseEnd_7160428 := by
    simpa [prefixWord, tailWord_7160428, baseEnd_7160428] using wordTrace_append hprefix tailTrace_7160428
  have hstable : (prefixWord ++ tailWord_7160428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160428).length < 2 ^ (prefixWord ++ tailWord_7160428).sum := by decide
  have hdescent : baseEnd_7160428 < baseStart_7160428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160429 : List Nat := [1, 5, 1, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_7160429 : Nat := 118140960795 + 7160429 * 2 ^ 59
def prefixEnd_7160429 : Nat := 4983230072969 + 3 ^ 40 * 7160429 * 2
def baseEnd_7160429 : Nat := 3676741769392870522307293

theorem tailTrace_7160429 : CollatzResearch.WordTrace tailWord_7160429 prefixEnd_7160429 3676741769392870522307293 := by
  unfold tailWord_7160429
  simp only [CollatzResearch.WordTrace]
  refine ⟨261162300975996111757956341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174108200650664074505304227 261162300975996111757956341)
  ·
    refine ⟨24483965716499635477308407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261162300975996111757956341 24483965716499635477308407)
    ·
      refine ⟨36725948574749453215962611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24483965716499635477308407 36725948574749453215962611)
      ·
        refine ⟨55088922862124179823943917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36725948574749453215962611 55088922862124179823943917)
        ·
          refine ⟨20658346073296567433978969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55088922862124179823943917 20658346073296567433978969)
          ·
            refine ⟨15493759554972425575484227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20658346073296567433978969 15493759554972425575484227)
            ·
              refine ⟨23240639332458638363226341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15493759554972425575484227 23240639332458638363226341)
              ·
                refine ⟨4357619874835994693104939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23240639332458638363226341 4357619874835994693104939)
                ·
                  refine ⟨6536429812253992039657409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357619874835994693104939 6536429812253992039657409)
                  ·
                    refine ⟨4902322359190494029743057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6536429812253992039657409 4902322359190494029743057)
                    ·
                      refine ⟨3676741769392870522307293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4902322359190494029743057 3676741769392870522307293)
                      ·
                        rfl

theorem cell23_7160429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_7160429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160429 prefixEnd_7160429 := by exact prefixLift 7160429
  have htrace : WordTrace (prefixWord ++ tailWord_7160429) baseStart_7160429 baseEnd_7160429 := by
    simpa [prefixWord, tailWord_7160429, baseEnd_7160429] using wordTrace_append hprefix tailTrace_7160429
  have hstable : (prefixWord ++ tailWord_7160429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160429).length < 2 ^ (prefixWord ++ tailWord_7160429).sum := by decide
  have hdescent : baseEnd_7160429 < baseStart_7160429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160445 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_7160445 : Nat := 118140960795 + 7160445 * 2 ^ 59
def prefixEnd_7160445 : Nat := 4983230072969 + 3 ^ 40 * 7160445 * 2
def baseEnd_7160445 : Nat := 3676749985083342459707219

theorem tailTrace_7160445 : CollatzResearch.WordTrace tailWord_7160445 prefixEnd_7160445 3676749985083342459707219 := by
  unfold tailWord_7160445
  simp only [CollatzResearch.WordTrace]
  refine ⟨261162884543938146490538789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174108589695958764327025859 261162884543938146490538789)
  ·
    refine ⟨48968040851988402466976023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261162884543938146490538789 48968040851988402466976023)
    ·
      refine ⟨73452061277982603700464035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48968040851988402466976023 73452061277982603700464035)
      ·
        refine ⟨110178091916973905550696053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73452061277982603700464035 110178091916973905550696053)
        ·
          refine ⟨10329196117216303645377755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110178091916973905550696053 10329196117216303645377755)
          ·
            refine ⟨15493794175824455468066633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329196117216303645377755 15493794175824455468066633)
            ·
              refine ⟨11620345631868341601049975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15493794175824455468066633 11620345631868341601049975)
              ·
                refine ⟨17430518447802512401574963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11620345631868341601049975 17430518447802512401574963)
                ·
                  refine ⟨26145777671703768602362445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17430518447802512401574963 26145777671703768602362445)
                  ·
                    refine ⟨9804666626888913225885917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26145777671703768602362445 9804666626888913225885917)
                    ·
                      refine ⟨3676749985083342459707219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9804666626888913225885917 3676749985083342459707219)
                      ·
                        rfl

theorem cell23_7160445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_7160445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160445 prefixEnd_7160445 := by exact prefixLift 7160445
  have htrace : WordTrace (prefixWord ++ tailWord_7160445) baseStart_7160445 baseEnd_7160445 := by
    simpa [prefixWord, tailWord_7160445, baseEnd_7160445] using wordTrace_append hprefix tailTrace_7160445
  have hstable : (prefixWord ++ tailWord_7160445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160445).length < 2 ^ (prefixWord ++ tailWord_7160445).sum := by decide
  have hdescent : baseEnd_7160445 < baseStart_7160445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160455 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 1, 3, 2]
def baseStart_7160455 : Nat := 118140960795 + 7160455 * 2 ^ 59
def prefixEnd_7160455 : Nat := 4983230072969 + 3 ^ 40 * 7160455 * 2
def baseEnd_7160455 : Nat := 3676755119889887420582173

theorem tailTrace_7160455 : CollatzResearch.WordTrace tailWord_7160455 prefixEnd_7160455 3676755119889887420582173 := by
  unfold tailWord_7160455
  simp only [CollatzResearch.WordTrace]
  refine ⟨261163249273901918198402819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174108832849267945465601879 261163249273901918198402819)
  ·
    refine ⟨391744873910852877297604229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261163249273901918198402819 391744873910852877297604229)
    ·
      refine ⟨73452163858284914493300793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391744873910852877297604229 73452163858284914493300793)
      ·
        refine ⟨55089122893713685869975595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73452163858284914493300793 55089122893713685869975595)
        ·
          refine ⟨82633684340570528804963393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55089122893713685869975595 82633684340570528804963393)
          ·
            refine ⟨61975263255427896603722545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82633684340570528804963393 61975263255427896603722545)
            ·
              refine ⟨46481447441570922452791909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61975263255427896603722545 46481447441570922452791909)
              ·
                refine ⟨8715271395294547959898483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46481447441570922452791909 8715271395294547959898483)
                ·
                  refine ⟨13072907092941821939847725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8715271395294547959898483 13072907092941821939847725)
                  ·
                    refine ⟨4902340159853183227442897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13072907092941821939847725 4902340159853183227442897)
                    ·
                      refine ⟨3676755119889887420582173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4902340159853183227442897 3676755119889887420582173)
                      ·
                        rfl

theorem cell23_7160455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_7160455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160455 prefixEnd_7160455 := by exact prefixLift 7160455
  have htrace : WordTrace (prefixWord ++ tailWord_7160455) baseStart_7160455 baseEnd_7160455 := by
    simpa [prefixWord, tailWord_7160455, baseEnd_7160455] using wordTrace_append hprefix tailTrace_7160455
  have hstable : (prefixWord ++ tailWord_7160455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160455).length < 2 ^ (prefixWord ++ tailWord_7160455).sum := by decide
  have hdescent : baseEnd_7160455 < baseStart_7160455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160471 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_7160471 : Nat := 118140960795 + 7160471 * 2 ^ 59
def prefixEnd_7160471 : Nat := 4983230072969 + 3 ^ 40 * 7160471 * 2
def baseEnd_7160471 : Nat := 3676763335580359357982099

theorem tailTrace_7160471 : CollatzResearch.WordTrace tailWord_7160471 prefixEnd_7160471 3676763335580359357982099 := by
  unfold tailWord_7160471
  simp only [CollatzResearch.WordTrace]
  refine ⟨261163832841843952930985267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174109221894562635287323511 261163832841843952930985267)
  ·
    refine ⟨391745749262765929396477901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261163832841843952930985267 391745749262765929396477901)
    ·
      refine ⟨146904655973537223523679213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391745749262765929396477901 146904655973537223523679213)
      ·
        refine ⟨55089245990076458821379705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146904655973537223523679213 55089245990076458821379705)
        ·
          refine ⟨41316934492557344116034779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55089245990076458821379705 41316934492557344116034779)
          ·
            refine ⟨61975401738836016174052169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41316934492557344116034779 61975401738836016174052169)
            ·
              refine ⟨46481551304127012130539127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61975401738836016174052169 46481551304127012130539127)
              ·
                refine ⟨69722326956190518195808691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46481551304127012130539127 69722326956190518195808691)
                ·
                  refine ⟨104583490434285777293713037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69722326956190518195808691 104583490434285777293713037)
                  ·
                    refine ⟨39218808912857166485142389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104583490434285777293713037 39218808912857166485142389)
                    ·
                      refine ⟨3676763335580359357982099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39218808912857166485142389 3676763335580359357982099)
                      ·
                        rfl

theorem cell23_7160471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_7160471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160471 prefixEnd_7160471 := by exact prefixLift 7160471
  have htrace : WordTrace (prefixWord ++ tailWord_7160471) baseStart_7160471 baseEnd_7160471 := by
    simpa [prefixWord, tailWord_7160471, baseEnd_7160471] using wordTrace_append hprefix tailTrace_7160471
  have hstable : (prefixWord ++ tailWord_7160471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160471).length < 2 ^ (prefixWord ++ tailWord_7160471).sum := by decide
  have hdescent : baseEnd_7160471 < baseStart_7160471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160478 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_7160478 : Nat := 118140960795 + 7160478 * 2 ^ 59
def prefixEnd_7160478 : Nat := 4983230072969 + 3 ^ 40 * 7160478 * 2
def baseEnd_7160478 : Nat := 1225588976648313610198189

theorem tailTrace_7160478 : CollatzResearch.WordTrace tailWord_7160478 prefixEnd_7160478 1225588976648313610198189 := by
  unfold tailWord_7160478
  simp only [CollatzResearch.WordTrace]
  refine ⟨32645511019102324140811261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174109392101879062084326725 32645511019102324140811261)
  ·
    refine ⟨12242066632163371552804223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32645511019102324140811261 12242066632163371552804223)
    ·
      refine ⟨18363099948245057329206335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12242066632163371552804223 18363099948245057329206335)
      ·
        refine ⟨27544649922367585993809503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18363099948245057329206335 27544649922367585993809503)
        ·
          refine ⟨41316974883551378990714255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27544649922367585993809503 41316974883551378990714255)
          ·
            refine ⟨61975462325327068486071383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41316974883551378990714255 61975462325327068486071383)
            ·
              refine ⟨92963193487990602729107075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61975462325327068486071383 92963193487990602729107075)
              ·
                refine ⟨139444790231985904093660613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92963193487990602729107075 139444790231985904093660613)
                ·
                  refine ⟨26145898168497357017561365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139444790231985904093660613 26145898168497357017561365)
                  ·
                    refine ⟨1225588976648313610198189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26145898168497357017561365 1225588976648313610198189)
                    ·
                      rfl

theorem cell23_7160478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_7160478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160478 prefixEnd_7160478 := by exact prefixLift 7160478
  have htrace : WordTrace (prefixWord ++ tailWord_7160478) baseStart_7160478 baseEnd_7160478 := by
    simpa [prefixWord, tailWord_7160478, baseEnd_7160478] using wordTrace_append hprefix tailTrace_7160478
  have hstable : (prefixWord ++ tailWord_7160478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160478).length < 2 ^ (prefixWord ++ tailWord_7160478).sum := by decide
  have hdescent : baseEnd_7160478 < baseStart_7160478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160521 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 8, 5]
def baseStart_7160521 : Nat := 118140960795 + 7160521 * 2 ^ 59
def prefixEnd_7160521 : Nat := 4983230072969 + 3 ^ 40 * 7160521 * 2
def baseEnd_7160521 : Nat := 1225596336537694720785623

theorem tailTrace_7160521 : CollatzResearch.WordTrace tailWord_7160521 prefixEnd_7160521 1225596336537694720785623 := by
  unfold tailWord_7160521
  simp only [CollatzResearch.WordTrace]
  refine ⟨261165656491662811470305417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174110437661108540980203611 261165656491662811470305417)
  ·
    refine ⟨195874242368747108602729063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261165656491662811470305417 195874242368747108602729063)
    ·
      refine ⟨293811363553120662904093595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195874242368747108602729063 293811363553120662904093595)
      ·
        refine ⟨440717045329680994356140393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293811363553120662904093595 440717045329680994356140393)
        ·
          refine ⟨330537783997260745767105295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440717045329680994356140393 330537783997260745767105295)
          ·
            refine ⟨495806675995891118650657943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330537783997260745767105295 495806675995891118650657943)
            ·
              refine ⟨743710013993836677975986915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495806675995891118650657943 743710013993836677975986915)
              ·
                refine ⟨1115565020990755016963980373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743710013993836677975986915 1115565020990755016963980373)
                ·
                  refine ⟨13073027589735410355046645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1115565020990755016963980373 13073027589735410355046645)
                  ·
                    refine ⟨1225596336537694720785623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13073027589735410355046645 1225596336537694720785623)
                    ·
                      rfl

theorem cell23_7160521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_7160521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160521 prefixEnd_7160521 := by exact prefixLift 7160521
  have htrace : WordTrace (prefixWord ++ tailWord_7160521) baseStart_7160521 baseEnd_7160521 := by
    simpa [prefixWord, tailWord_7160521, baseEnd_7160521] using wordTrace_append hprefix tailTrace_7160521
  have hstable : (prefixWord ++ tailWord_7160521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160521).length < 2 ^ (prefixWord ++ tailWord_7160521).sum := by decide
  have hdescent : baseEnd_7160521 < baseStart_7160521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160538 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_7160538 : Nat := 118140960795 + 7160538 * 2 ^ 59
def prefixEnd_7160538 : Nat := 4983230072969 + 3 ^ 40 * 7160538 * 2
def baseEnd_7160538 : Nat := 1225599246261403531948097

theorem tailTrace_7160538 : CollatzResearch.WordTrace tailWord_7160538 prefixEnd_7160538 1225599246261403531948097 := by
  unfold tailWord_7160538
  simp only [CollatzResearch.WordTrace]
  refine ⟨65291569133150305843418567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174110851021734148915782845 65291569133150305843418567)
  ·
    refine ⟨97937353699725458765127851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65291569133150305843418567 97937353699725458765127851)
    ·
      refine ⟨146906030549588188147691777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97937353699725458765127851 146906030549588188147691777)
      ·
        refine ⟨110179522912191141110768833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146906030549588188147691777 110179522912191141110768833)
        ·
          refine ⟨82634642184143355833076625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110179522912191141110768833 82634642184143355833076625)
          ·
            refine ⟨61975981638107516874807469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82634642184143355833076625 61975981638107516874807469)
            ·
              refine ⟨23240993114290318828052801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61975981638107516874807469 23240993114290318828052801)
              ·
                refine ⟨17430744835717739121039601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23240993114290318828052801 17430744835717739121039601)
                ·
                  refine ⟨13073058626788304340779701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17430744835717739121039601 13073058626788304340779701)
                  ·
                    refine ⟨1225599246261403531948097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13073058626788304340779701 1225599246261403531948097)
                    ·
                      rfl

theorem cell23_7160538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_7160538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160538 prefixEnd_7160538 := by exact prefixLift 7160538
  have htrace : WordTrace (prefixWord ++ tailWord_7160538) baseStart_7160538 baseEnd_7160538 := by
    simpa [prefixWord, tailWord_7160538, baseEnd_7160538] using wordTrace_append hprefix tailTrace_7160538
  have hstable : (prefixWord ++ tailWord_7160538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160538).length < 2 ^ (prefixWord ++ tailWord_7160538).sum := by decide
  have hdescent : baseEnd_7160538 < baseStart_7160538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160548 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_7160548 : Nat := 118140960795 + 7160548 * 2 ^ 59
def prefixEnd_7160548 : Nat := 4983230072969 + 3 ^ 40 * 7160548 * 2
def baseEnd_7160548 : Nat := 3676802873590755556719245

theorem tailTrace_7160548 : CollatzResearch.WordTrace tailWord_7160548 prefixEnd_7160548 3676802873590755556719245 := by
  unfold tailWord_7160548
  simp only [CollatzResearch.WordTrace]
  refine ⟨130583320631282497540769149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174111094175043330054358865 130583320631282497540769149)
  ·
    refine ⟨48968745236730936577788431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130583320631282497540769149 48968745236730936577788431)
    ·
      refine ⟨73453117855096404866682647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48968745236730936577788431 73453117855096404866682647)
      ·
        refine ⟨110179676782644607300023971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73453117855096404866682647 110179676782644607300023971)
        ·
          refine ⟨165269515173966910950035957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110179676782644607300023971 165269515173966910950035957)
          ·
            refine ⟨15494017047559397901565871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165269515173966910950035957 15494017047559397901565871)
            ·
              refine ⟨23241025571339096852348807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15494017047559397901565871 23241025571339096852348807)
              ·
                refine ⟨34861538357008645278523211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23241025571339096852348807 34861538357008645278523211)
                ·
                  refine ⟨52292307535512967917784817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34861538357008645278523211 52292307535512967917784817)
                  ·
                    refine ⟨39219230651634725938338613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52292307535512967917784817 39219230651634725938338613)
                    ·
                      refine ⟨3676802873590755556719245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39219230651634725938338613 3676802873590755556719245)
                      ·
                        rfl

theorem cell23_7160548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_7160548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160548 prefixEnd_7160548 := by exact prefixLift 7160548
  have htrace : WordTrace (prefixWord ++ tailWord_7160548) baseStart_7160548 baseEnd_7160548 := by
    simpa [prefixWord, tailWord_7160548, baseEnd_7160548] using wordTrace_append hprefix tailTrace_7160548
  have hstable : (prefixWord ++ tailWord_7160548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160548).length < 2 ^ (prefixWord ++ tailWord_7160548).sum := by decide
  have hdescent : baseEnd_7160548 < baseStart_7160548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160568 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 5, 4]
def baseStart_7160568 : Nat := 118140960795 + 7160568 * 2 ^ 59
def prefixEnd_7160568 : Nat := 4983230072969 + 3 ^ 40 * 7160568 * 2
def baseEnd_7160568 : Nat := 1225604381067948492823051

theorem tailTrace_7160568 : CollatzResearch.WordTrace tailWord_7160568 prefixEnd_7160568 1225604381067948492823051 := by
  unfold tailWord_7160568
  simp only [CollatzResearch.WordTrace]
  refine ⟨130583685361246269248633179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174111580481661692331510905 130583685361246269248633179)
  ·
    refine ⟨195875528041869403872949769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130583685361246269248633179 195875528041869403872949769)
    ·
      refine ⟨146906646031402052904712327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195875528041869403872949769 146906646031402052904712327)
      ·
        refine ⟨220359969047103079357068491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146906646031402052904712327 220359969047103079357068491)
        ·
          refine ⟨330539953570654619035602737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220359969047103079357068491 330539953570654619035602737)
          ·
            refine ⟨247904965177990964276702053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330539953570654619035602737 247904965177990964276702053)
            ·
              refine ⟨46482180970873305801881635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247904965177990964276702053 46482180970873305801881635)
              ·
                refine ⟨69723271456309958702822453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46482180970873305801881635 69723271456309958702822453)
                ·
                  refine ⟨6536556699029058628389605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69723271456309958702822453 6536556699029058628389605)
                  ·
                    refine ⟨1225604381067948492823051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6536556699029058628389605 1225604381067948492823051)
                    ·
                      rfl

theorem cell23_7160568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_7160568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160568 prefixEnd_7160568 := by exact prefixLift 7160568
  have htrace : WordTrace (prefixWord ++ tailWord_7160568) baseStart_7160568 baseEnd_7160568 := by
    simpa [prefixWord, tailWord_7160568, baseEnd_7160568] using wordTrace_append hprefix tailTrace_7160568
  have hstable : (prefixWord ++ tailWord_7160568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160568).length < 2 ^ (prefixWord ++ tailWord_7160568).sum := by decide
  have hdescent : baseEnd_7160568 < baseStart_7160568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160581 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 10]
def baseStart_7160581 : Nat := 118140960795 + 7160581 * 2 ^ 59
def prefixEnd_7160581 : Nat := 4983230072969 + 3 ^ 40 * 7160581 * 2
def baseEnd_7160581 : Nat := 408535535383594880845177

theorem tailTrace_7160581 : CollatzResearch.WordTrace tailWord_7160581 prefixEnd_7160581 408535535383594880845177 := by
  unfold tailWord_7160581
  simp only [CollatzResearch.WordTrace]
  refine ⟨261167844871445441717489597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174111896580963627811659731 261167844871445441717489597)
  ·
    refine ⟨97937941826792040644058599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261167844871445441717489597 97937941826792040644058599)
    ·
      refine ⟨146906912740188060966087899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97937941826792040644058599 146906912740188060966087899)
      ·
        refine ⟨220360369110282091449131849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146906912740188060966087899 220360369110282091449131849)
        ·
          refine ⟨165270276832711568586848887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220360369110282091449131849 165270276832711568586848887)
          ·
            refine ⟨247905415249067352880273331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165270276832711568586848887 247905415249067352880273331)
            ·
              refine ⟨371858122873601029320409997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247905415249067352880273331 371858122873601029320409997)
              ·
                refine ⟨139446796077600385995153749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371858122873601029320409997 139446796077600385995153749)
                ·
                  refine ⟨408535535383594880845177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 139446796077600385995153749 408535535383594880845177)
                  ·
                    rfl

theorem cell23_7160581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_7160581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160581 prefixEnd_7160581 := by exact prefixLift 7160581
  have htrace : WordTrace (prefixWord ++ tailWord_7160581) baseStart_7160581 baseEnd_7160581 := by
    simpa [prefixWord, tailWord_7160581, baseEnd_7160581] using wordTrace_append hprefix tailTrace_7160581
  have hstable : (prefixWord ++ tailWord_7160581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160581).length < 2 ^ (prefixWord ++ tailWord_7160581).sum := by decide
  have hdescent : baseEnd_7160581 < baseStart_7160581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160602 : List Nat := [3, 1, 1, 3, 2, 1, 3, 4, 1, 4]
def baseStart_7160602 : Nat := 118140960795 + 7160602 * 2 ^ 59
def prefixEnd_7160602 : Nat := 4983230072969 + 3 ^ 40 * 7160602 * 2
def baseEnd_7160602 : Nat := 1225610200515366115147999

theorem tailTrace_7160602 : CollatzResearch.WordTrace tailWord_7160602 prefixEnd_7160602 1225610200515366115147999 := by
  unfold tailWord_7160602
  simp only [CollatzResearch.WordTrace]
  refine ⟨65292152701092340576001015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174112407202912908202669373 65292152701092340576001015)
  ·
    refine ⟨97938229051638510864001523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65292152701092340576001015 97938229051638510864001523)
    ·
      refine ⟨146907343577457766296002285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97938229051638510864001523 146907343577457766296002285)
      ·
        refine ⟨55090253841546662361000857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146907343577457766296002285 55090253841546662361000857)
        ·
          refine ⟨41317690381159996770750643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55090253841546662361000857 41317690381159996770750643)
          ·
            refine ⟨61976535571739995156125965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41317690381159996770750643 61976535571739995156125965)
            ·
              refine ⟨23241200839402498183547237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61976535571739995156125965 23241200839402498183547237)
              ·
                refine ⟨4357725157387968409415107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23241200839402498183547237 4357725157387968409415107)
                ·
                  refine ⟨6536587736081952614122661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357725157387968409415107 6536587736081952614122661)
                  ·
                    refine ⟨1225610200515366115147999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6536587736081952614122661 1225610200515366115147999)
                    ·
                      rfl

theorem cell23_7160602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_7160602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160602 prefixEnd_7160602 := by exact prefixLift 7160602
  have htrace : WordTrace (prefixWord ++ tailWord_7160602) baseStart_7160602 baseEnd_7160602 := by
    simpa [prefixWord, tailWord_7160602, baseEnd_7160602] using wordTrace_append hprefix tailTrace_7160602
  have hstable : (prefixWord ++ tailWord_7160602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160602).length < 2 ^ (prefixWord ++ tailWord_7160602).sum := by decide
  have hdescent : baseEnd_7160602 < baseStart_7160602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160675 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 1, 6]
def baseStart_7160675 : Nat := 118140960795 + 7160675 * 2 ^ 59
def prefixEnd_7160675 : Nat := 4983230072969 + 3 ^ 40 * 7160675 * 2
def baseEnd_7160675 : Nat := 1225622695211292186610387

theorem tailTrace_7160675 : CollatzResearch.WordTrace tailWord_7160675 prefixEnd_7160675 1225622695211292186610387 := by
  unfold tailWord_7160675
  simp only [CollatzResearch.WordTrace]
  refine ⟨261171273333104895771411479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174114182222069930514274319 261171273333104895771411479)
  ·
    refine ⟨391756909999657343657117219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261171273333104895771411479 391756909999657343657117219)
    ·
      refine ⟨587635364999486015485675829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391756909999657343657117219 587635364999486015485675829)
      ·
        refine ⟨55090815468701813951782109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 587635364999486015485675829 55090815468701813951782109)
        ·
          refine ⟨20659055800763180231918291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55090815468701813951782109 20659055800763180231918291)
          ·
            refine ⟨30988583701144770347877437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20659055800763180231918291 30988583701144770347877437)
            ·
              refine ⟨11620718887929288880454039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30988583701144770347877437 11620718887929288880454039)
              ·
                refine ⟨17431078331893933320681059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11620718887929288880454039 17431078331893933320681059)
                ·
                  refine ⟨26146617497840899981021589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17431078331893933320681059 26146617497840899981021589)
                  ·
                    refine ⟨1225622695211292186610387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26146617497840899981021589 1225622695211292186610387)
                    ·
                      rfl

theorem cell23_7160675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 6].length) (baseStart_7160675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160675 prefixEnd_7160675 := by exact prefixLift 7160675
  have htrace : WordTrace (prefixWord ++ tailWord_7160675) baseStart_7160675 baseEnd_7160675 := by
    simpa [prefixWord, tailWord_7160675, baseEnd_7160675] using wordTrace_append hprefix tailTrace_7160675
  have hstable : (prefixWord ++ tailWord_7160675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160675).length < 2 ^ (prefixWord ++ tailWord_7160675).sum := by decide
  have hdescent : baseEnd_7160675 < baseStart_7160675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160722 : List Nat := [3, 2, 3, 2, 2, 1, 2, 8]
def baseStart_7160722 : Nat := 118140960795 + 7160722 * 2 ^ 59
def prefixEnd_7160722 : Nat := 4983230072969 + 3 ^ 40 * 7160722 * 2
def baseEnd_7160722 : Nat := 136181193304616217627535

theorem tailTrace_7160722 : CollatzResearch.WordTrace tailWord_7160722 prefixEnd_7160722 136181193304616217627535 := by
  unfold tailWord_7160722
  simp only [CollatzResearch.WordTrace]
  refine ⟨65293246890983655699593105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174115325042623081865581613 65293246890983655699593105)
  ·
    refine ⟨48969935168237741774694829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65293246890983655699593105 48969935168237741774694829)
    ·
      refine ⟨18363725688089153165510561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48969935168237741774694829 18363725688089153165510561)
      ·
        refine ⟨13772794266066864874132921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18363725688089153165510561 13772794266066864874132921)
        ·
          refine ⟨10329595699550148655599691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13772794266066864874132921 10329595699550148655599691)
          ·
            refine ⟨15494393549325222983399537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329595699550148655599691 15494393549325222983399537)
            ·
              refine ⟨11620795161993917237549653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15494393549325222983399537 11620795161993917237549653)
              ·
                refine ⟨136181193304616217627535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11620795161993917237549653 136181193304616217627535)
                ·
                  rfl

theorem cell23_7160722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 8].length) (baseStart_7160722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160722 prefixEnd_7160722 := by exact prefixLift 7160722
  have htrace : WordTrace (prefixWord ++ tailWord_7160722) baseStart_7160722 baseEnd_7160722 := by
    simpa [prefixWord, tailWord_7160722, baseEnd_7160722] using wordTrace_append hprefix tailTrace_7160722
  have hstable : (prefixWord ++ tailWord_7160722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160722).length < 2 ^ (prefixWord ++ tailWord_7160722).sum := by decide
  have hdescent : baseEnd_7160722 < baseStart_7160722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160748 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_7160748 : Nat := 118140960795 + 7160748 * 2 ^ 59
def prefixEnd_7160748 : Nat := 4983230072969 + 3 ^ 40 * 7160748 * 2
def baseEnd_7160748 : Nat := 1225635189907218258072775

theorem tailTrace_7160748 : CollatzResearch.WordTrace tailWord_7160748 prefixEnd_7160748 1225635189907218258072775 := by
  unfold tailWord_7160748
  simp only [CollatzResearch.WordTrace]
  refine ⟨130586967930920214619409449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174115957241226952825879265 130586967930920214619409449)
  ·
    refine ⟨97940225948190160964557087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130586967930920214619409449 97940225948190160964557087)
    ·
      refine ⟨146910338922285241446835631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97940225948190160964557087 146910338922285241446835631)
      ·
        refine ⟨220365508383427862170253447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146910338922285241446835631 220365508383427862170253447)
        ·
          refine ⟨330548262575141793255380171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220365508383427862170253447 330548262575141793255380171)
          ·
            refine ⟨495822393862712689883070257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330548262575141793255380171 495822393862712689883070257)
            ·
              refine ⟨371866795397034517412302693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495822393862712689883070257 371866795397034517412302693)
              ·
                refine ⟨69725024136943972014806755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371866795397034517412302693 69725024136943972014806755)
                ·
                  refine ⟨104587536205415958022210133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69725024136943972014806755 104587536205415958022210133)
                  ·
                    refine ⟨1225635189907218258072775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104587536205415958022210133 1225635189907218258072775)
                    ·
                      rfl

theorem cell23_7160748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_7160748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160748 prefixEnd_7160748 := by exact prefixLift 7160748
  have htrace : WordTrace (prefixWord ++ tailWord_7160748) baseStart_7160748 baseEnd_7160748 := by
    simpa [prefixWord, tailWord_7160748, baseEnd_7160748] using wordTrace_append hprefix tailTrace_7160748
  have hstable : (prefixWord ++ tailWord_7160748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160748).length < 2 ^ (prefixWord ++ tailWord_7160748).sum := by decide
  have hdescent : baseEnd_7160748 < baseStart_7160748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160775 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_7160775 : Nat := 118140960795 + 7160775 * 2 ^ 59
def prefixEnd_7160775 : Nat := 4983230072969 + 3 ^ 40 * 7160775 * 2
def baseEnd_7160775 : Nat := 3676919433699326168580701

theorem tailTrace_7160775 : CollatzResearch.WordTrace tailWord_7160775 prefixEnd_7160775 3676919433699326168580701 := by
  unfold tailWord_7160775
  simp only [CollatzResearch.WordTrace]
  refine ⟨261174920632742612850051779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174116613755161741900034519 261174920632742612850051779)
  ·
    refine ⟨391762380949113919275077669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261174920632742612850051779 391762380949113919275077669)
    ·
      refine ⟨73455446427958859864077063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391762380949113919275077669 73455446427958859864077063)
      ·
        refine ⟨110183169641938289796115595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73455446427958859864077063 110183169641938289796115595)
        ·
          refine ⟨165274754462907434694173393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110183169641938289796115595 165274754462907434694173393)
          ·
            refine ⟨123956065847180576020630045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165274754462907434694173393 123956065847180576020630045)
            ·
              refine ⟨46483524692692716007736267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123956065847180576020630045 46483524692692716007736267)
              ·
                refine ⟨69725287039039074011604401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46483524692692716007736267 69725287039039074011604401)
                ·
                  refine ⟨52293965279279305508703301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69725287039039074011604401 52293965279279305508703301)
                  ·
                    refine ⟨9805118489864869782881869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52293965279279305508703301 9805118489864869782881869)
                    ·
                      refine ⟨3676919433699326168580701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9805118489864869782881869 3676919433699326168580701)
                      ·
                        rfl

theorem cell23_7160775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_7160775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160775 prefixEnd_7160775 := by exact prefixLift 7160775
  have htrace : WordTrace (prefixWord ++ tailWord_7160775) baseStart_7160775 baseEnd_7160775 := by
    simpa [prefixWord, tailWord_7160775, baseEnd_7160775] using wordTrace_append hprefix tailTrace_7160775
  have hstable : (prefixWord ++ tailWord_7160775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160775).length < 2 ^ (prefixWord ++ tailWord_7160775).sum := by decide
  have hdescent : baseEnd_7160775 < baseStart_7160775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160785 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_7160785 : Nat := 118140960795 + 7160785 * 2 ^ 59
def prefixEnd_7160785 : Nat := 4983230072969 + 3 ^ 40 * 7160785 * 2
def baseEnd_7160785 : Nat := 3676924568505871129455655

theorem tailTrace_7160785 : CollatzResearch.WordTrace tailWord_7160785 prefixEnd_7160785 3676924568505871129455655 := by
  unfold tailWord_7160785
  simp only [CollatzResearch.WordTrace]
  refine ⟨261175285362706384557915809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174116856908470923038610539 261175285362706384557915809)
  ·
    refine ⟨195881464022029788418436857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261175285362706384557915809 195881464022029788418436857)
    ·
      refine ⟨146911098016522341313827643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195881464022029788418436857 146911098016522341313827643)
      ·
        refine ⟨220366647024783511970741465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146911098016522341313827643 220366647024783511970741465)
        ·
          refine ⟨165274985268587633978056099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220366647024783511970741465 165274985268587633978056099)
          ·
            refine ⟨247912477902881450967084149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165274985268587633978056099 247912477902881450967084149)
            ·
              refine ⟨23241794803395136028164139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247912477902881450967084149 23241794803395136028164139)
              ·
                refine ⟨34862692205092704042246209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23241794803395136028164139 34862692205092704042246209)
                ·
                  refine ⟨26147019153819528031684657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34862692205092704042246209 26147019153819528031684657)
                  ·
                    refine ⟨19610264365364646023763493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26147019153819528031684657 19610264365364646023763493)
                    ·
                      refine ⟨3676924568505871129455655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19610264365364646023763493 3676924568505871129455655)
                      ·
                        rfl

theorem cell23_7160785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_7160785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160785 prefixEnd_7160785 := by exact prefixLift 7160785
  have htrace : WordTrace (prefixWord ++ tailWord_7160785) baseStart_7160785 baseEnd_7160785 := by
    simpa [prefixWord, tailWord_7160785, baseEnd_7160785] using wordTrace_append hprefix tailTrace_7160785
  have hstable : (prefixWord ++ tailWord_7160785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160785).length < 2 ^ (prefixWord ++ tailWord_7160785).sum := by decide
  have hdescent : baseEnd_7160785 < baseStart_7160785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160825 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 4, 5]
def baseStart_7160825 : Nat := 118140960795 + 7160825 * 2 ^ 59
def prefixEnd_7160825 : Nat := 4983230072969 + 3 ^ 40 * 7160825 * 2
def baseEnd_7160825 : Nat := 1225648369244016990985157

theorem tailTrace_7160825 : CollatzResearch.WordTrace tailWord_7160825 prefixEnd_7160825 1225648369244016990985157 := by
  unfold tailWord_7160825
  simp only [CollatzResearch.WordTrace]
  refine ⟨261176744282561471389371929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174117829521707647592914619 261176744282561471389371929)
  ·
    refine ⟨195882558211921103542028947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261176744282561471389371929 195882558211921103542028947)
    ·
      refine ⟨293823837317881655313043421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195882558211921103542028947 293823837317881655313043421)
      ·
        refine ⟨110183938994205620742391283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293823837317881655313043421 110183938994205620742391283)
        ·
          refine ⟨165275908491308431113586925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110183938994205620742391283 165275908491308431113586925)
          ·
            refine ⟨61978465684240661667595097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165275908491308431113586925 61978465684240661667595097)
            ·
              refine ⟨46483849263180496250696323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61978465684240661667595097 46483849263180496250696323)
              ·
                refine ⟨69725773894770744376044485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46483849263180496250696323 69725773894770744376044485)
                ·
                  refine ⟨13073582605269514570508341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69725773894770744376044485 13073582605269514570508341)
                  ·
                    refine ⟨1225648369244016990985157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13073582605269514570508341 1225648369244016990985157)
                    ·
                      rfl

theorem cell23_7160825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_7160825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160825 prefixEnd_7160825 := by exact prefixLift 7160825
  have htrace : WordTrace (prefixWord ++ tailWord_7160825) baseStart_7160825 baseEnd_7160825 := by
    simpa [prefixWord, tailWord_7160825, baseEnd_7160825] using wordTrace_append hprefix tailTrace_7160825
  have hstable : (prefixWord ++ tailWord_7160825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160825).length < 2 ^ (prefixWord ++ tailWord_7160825).sum := by decide
  have hdescent : baseEnd_7160825 < baseStart_7160825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160889 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 3, 4]
def baseStart_7160889 : Nat := 118140960795 + 7160889 * 2 ^ 59
def prefixEnd_7160889 : Nat := 4983230072969 + 3 ^ 40 * 7160889 * 2
def baseEnd_7160889 : Nat := 1225659323497979574185059

theorem tailTrace_7160889 : CollatzResearch.WordTrace tailWord_7160889 prefixEnd_7160889 1225659323497979574185059 := by
  unfold tailWord_7160889
  simp only [CollatzResearch.WordTrace]
  refine ⟨261179078554329610319701721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174119385702886406879801147 261179078554329610319701721)
  ·
    refine ⟨195884308915747207739776291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261179078554329610319701721 195884308915747207739776291)
    ·
      refine ⟨293826463373620811609664437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195884308915747207739776291 293826463373620811609664437)
      ·
        refine ⟨27546230941276951088406041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293826463373620811609664437 27546230941276951088406041)
        ·
          refine ⟨20659673205957713316304531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27546230941276951088406041 20659673205957713316304531)
          ·
            refine ⟨30989509808936569974456797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20659673205957713316304531 30989509808936569974456797)
            ·
              refine ⟨11621066178351213740421299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30989509808936569974456797 11621066178351213740421299)
              ·
                refine ⟨17431599267526820610631949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11621066178351213740421299 17431599267526820610631949)
                ·
                  refine ⟨6536849725322557728986981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17431599267526820610631949 6536849725322557728986981)
                  ·
                    refine ⟨1225659323497979574185059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6536849725322557728986981 1225659323497979574185059)
                    ·
                      rfl

theorem cell23_7160889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 4].length) (baseStart_7160889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160889 prefixEnd_7160889 := by exact prefixLift 7160889
  have htrace : WordTrace (prefixWord ++ tailWord_7160889) baseStart_7160889 baseEnd_7160889 := by
    simpa [prefixWord, tailWord_7160889, baseEnd_7160889] using wordTrace_append hprefix tailTrace_7160889
  have hstable : (prefixWord ++ tailWord_7160889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160889).length < 2 ^ (prefixWord ++ tailWord_7160889).sum := by decide
  have hdescent : baseEnd_7160889 < baseStart_7160889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160936 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 6]
def baseStart_7160936 : Nat := 118140960795 + 7160936 * 2 ^ 59
def prefixEnd_7160936 : Nat := 4983230072969 + 3 ^ 40 * 7160936 * 2
def baseEnd_7160936 : Nat := 408555789342744448740829

theorem tailTrace_7160936 : CollatzResearch.WordTrace tailWord_7160936 prefixEnd_7160936 408555789342744448740829 := by
  unfold tailWord_7160936
  simp only [CollatzResearch.WordTrace]
  refine ⟨130590396392579668673331331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174120528523439558231108441 130590396392579668673331331)
  ·
    refine ⟨195885594588869503009996997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130590396392579668673331331 195885594588869503009996997)
    ·
      refine ⟨36728548985413031814374437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195885594588869503009996997 36728548985413031814374437)
      ·
        refine ⟨6886602934764943465195207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36728548985413031814374437 6886602934764943465195207)
        ·
          refine ⟨10329904402147415197792811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6886602934764943465195207 10329904402147415197792811)
          ·
            refine ⟨15494856603221122796689217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329904402147415197792811 15494856603221122796689217)
            ·
              refine ⟨11621142452415842097516913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15494856603221122796689217 11621142452415842097516913)
              ·
                refine ⟨8715856839311881573137685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11621142452415842097516913 8715856839311881573137685)
                ·
                  refine ⟨408555789342744448740829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8715856839311881573137685 408555789342744448740829)
                  ·
                    rfl

theorem cell23_7160936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 6].length) (baseStart_7160936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160936 prefixEnd_7160936 := by exact prefixLift 7160936
  have htrace : WordTrace (prefixWord ++ tailWord_7160936) baseStart_7160936 baseEnd_7160936 := by
    simpa [prefixWord, tailWord_7160936, baseEnd_7160936] using wordTrace_append hprefix tailTrace_7160936
  have hstable : (prefixWord ++ tailWord_7160936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160936).length < 2 ^ (prefixWord ++ tailWord_7160936).sum := by decide
  have hdescent : baseEnd_7160936 < baseStart_7160936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160952 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_7160952 : Nat := 118140960795 + 7160952 * 2 ^ 59
def prefixEnd_7160952 : Nat := 4983230072969 + 3 ^ 40 * 7160952 * 2
def baseEnd_7160952 : Nat := 3677010319775171976067387

theorem tailTrace_7160952 : CollatzResearch.WordTrace tailWord_7160952 prefixEnd_7160952 3677010319775171976067387 := by
  unfold tailWord_7160952
  simp only [CollatzResearch.WordTrace]
  refine ⟨130590688176550686039622555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174120917568734248052830073 130590688176550686039622555)
  ·
    refine ⟨195886032264826029059433833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130590688176550686039622555 195886032264826029059433833)
    ·
      refine ⟨146914524198619521794575375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195886032264826029059433833 146914524198619521794575375)
      ·
        refine ⟨220371786297929282691863063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146914524198619521794575375 220371786297929282691863063)
        ·
          refine ⟨330557679446893924037794595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220371786297929282691863063 330557679446893924037794595)
          ·
            refine ⟨495836519170340886056691893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330557679446893924037794595 495836519170340886056691893)
            ·
              refine ⟨46484673672219458067814865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 495836519170340886056691893 46484673672219458067814865)
              ·
                refine ⟨34863505254164593550861149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46484673672219458067814865 34863505254164593550861149)
                ·
                  refine ⟨13073814470311722581572931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34863505254164593550861149 13073814470311722581572931)
                  ·
                    refine ⟨19610721705467583872359397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13073814470311722581572931 19610721705467583872359397)
                    ·
                      refine ⟨3677010319775171976067387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19610721705467583872359397 3677010319775171976067387)
                      ·
                        rfl

theorem cell23_7160952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_7160952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160952 prefixEnd_7160952 := by exact prefixLift 7160952
  have htrace : WordTrace (prefixWord ++ tailWord_7160952) baseStart_7160952 baseEnd_7160952 := by
    simpa [prefixWord, tailWord_7160952, baseEnd_7160952] using wordTrace_append hprefix tailTrace_7160952
  have hstable : (prefixWord ++ tailWord_7160952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160952).length < 2 ^ (prefixWord ++ tailWord_7160952).sum := by decide
  have hdescent : baseEnd_7160952 < baseStart_7160952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160986 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4]
def baseStart_7160986 : Nat := 118140960795 + 7160986 * 2 ^ 59
def prefixEnd_7160986 : Nat := 4983230072969 + 3 ^ 40 * 7160986 * 2
def baseEnd_7160986 : Nat := 3677027778117424843042231

theorem tailTrace_7160986 : CollatzResearch.WordTrace tailWord_7160986 prefixEnd_7160986 3677027778117424843042231 := by
  unfold tailWord_7160986
  simp only [CollatzResearch.WordTrace]
  refine ⟨65295654108744548971495703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174121744289985463923988541 65295654108744548971495703)
  ·
    refine ⟨97943481163116823457243555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65295654108744548971495703 97943481163116823457243555)
    ·
      refine ⟨146915221744675235185865333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97943481163116823457243555 146915221744675235185865333)
      ·
        refine ⟨13773302038563303298674875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146915221744675235185865333 13773302038563303298674875)
        ·
          refine ⟨20659953057844954948012313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13773302038563303298674875 20659953057844954948012313)
          ·
            refine ⟨15494964793383716211009235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20659953057844954948012313 15494964793383716211009235)
            ·
              refine ⟨23242447190075574316513853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15494964793383716211009235 23242447190075574316513853)
              ·
                refine ⟨8715917696278340368692695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23242447190075574316513853 8715917696278340368692695)
                ·
                  refine ⟨13073876544417510553039043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8715917696278340368692695 13073876544417510553039043)
                  ·
                    refine ⟨19610814816626265829558565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13073876544417510553039043 19610814816626265829558565)
                    ·
                      refine ⟨3677027778117424843042231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19610814816626265829558565 3677027778117424843042231)
                      ·
                        rfl

theorem cell23_7160986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_7160986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160986 prefixEnd_7160986 := by exact prefixLift 7160986
  have htrace : WordTrace (prefixWord ++ tailWord_7160986) baseStart_7160986 baseEnd_7160986 := by
    simpa [prefixWord, tailWord_7160986, baseEnd_7160986] using wordTrace_append hprefix tailTrace_7160986
  have hstable : (prefixWord ++ tailWord_7160986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160986).length < 2 ^ (prefixWord ++ tailWord_7160986).sum := by decide
  have hdescent : baseEnd_7160986 < baseStart_7160986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7160996 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_7160996 : Nat := 118140960795 + 7160996 * 2 ^ 59
def prefixEnd_7160996 : Nat := 4983230072969 + 3 ^ 40 * 7160996 * 2
def baseEnd_7160996 : Nat := 1225677637641323267972395

theorem tailTrace_7160996 : CollatzResearch.WordTrace tailWord_7160996 prefixEnd_7160996 1225677637641323267972395 := by
  unfold tailWord_7160996
  simp only [CollatzResearch.WordTrace]
  refine ⟨130591490582470983796923421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174121987443294645062564561 130591490582470983796923421)
  ·
    refine ⟨48971808968426618923846283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130591490582470983796923421 48971808968426618923846283)
    ·
      refine ⟨73457713452639928385769425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48971808968426618923846283 73457713452639928385769425)
      ·
        refine ⟨55093285089479946289327069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73457713452639928385769425 55093285089479946289327069)
        ·
          refine ⟨20659981908554979858497651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55093285089479946289327069 20659981908554979858497651)
          ·
            refine ⟨30989972862832469787746477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20659981908554979858497651 30989972862832469787746477)
            ·
              refine ⟨11621239823562176170404929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30989972862832469787746477 11621239823562176170404929)
              ·
                refine ⟨8715929867671632127803697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11621239823562176170404929 8715929867671632127803697)
                ·
                  refine ⟨6536947400753724095852773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8715929867671632127803697 6536947400753724095852773)
                  ·
                    refine ⟨1225677637641323267972395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6536947400753724095852773 1225677637641323267972395)
                    ·
                      rfl

theorem cell23_7160996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_7160996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7160996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7160996 prefixEnd_7160996 := by exact prefixLift 7160996
  have htrace : WordTrace (prefixWord ++ tailWord_7160996) baseStart_7160996 baseEnd_7160996 := by
    simpa [prefixWord, tailWord_7160996, baseEnd_7160996] using wordTrace_append hprefix tailTrace_7160996
  have hstable : (prefixWord ++ tailWord_7160996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7160996).length < 2 ^ (prefixWord ++ tailWord_7160996).sum := by decide
  have hdescent : baseEnd_7160996 < baseStart_7160996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7160996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161032 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_7161032 : Nat := 118140960795 + 7161032 * 2 ^ 59
def prefixEnd_7161032 : Nat := 4983230072969 + 3 ^ 40 * 7161032 * 2
def baseEnd_7161032 : Nat := 3677051398227531663067019

theorem tailTrace_7161032 : CollatzResearch.WordTrace tailWord_7161032 prefixEnd_7161032 3677051398227531663067019 := by
  unfold tailWord_7161032
  simp only [CollatzResearch.WordTrace]
  refine ⟨130592147096405772871078675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174122862795207697161438233 130592147096405772871078675)
  ·
    refine ⟨195888220644608659306618013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130592147096405772871078675 195888220644608659306618013)
    ·
      refine ⟨73458082741728247239981755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195888220644608659306618013 73458082741728247239981755)
      ·
        refine ⟨110187124112592370859972633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73458082741728247239981755 110187124112592370859972633)
        ·
          refine ⟨82640343084444278144979475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110187124112592370859972633 82640343084444278144979475)
          ·
            refine ⟨123960514626666417217469213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82640343084444278144979475 123960514626666417217469213)
            ·
              refine ⟨46485192984999906456550955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123960514626666417217469213 46485192984999906456550955)
              ·
                refine ⟨69727789477499859684826433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46485192984999906456550955 69727789477499859684826433)
                ·
                  refine ⟨52295842108124894763619825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69727789477499859684826433 52295842108124894763619825)
                  ·
                    refine ⟨39221881581093671072714869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52295842108124894763619825 39221881581093671072714869)
                    ·
                      refine ⟨3677051398227531663067019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39221881581093671072714869 3677051398227531663067019)
                      ·
                        rfl

theorem cell23_7161032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_7161032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161032 prefixEnd_7161032 := by exact prefixLift 7161032
  have htrace : WordTrace (prefixWord ++ tailWord_7161032) baseStart_7161032 baseEnd_7161032 := by
    simpa [prefixWord, tailWord_7161032, baseEnd_7161032] using wordTrace_append hprefix tailTrace_7161032
  have hstable : (prefixWord ++ tailWord_7161032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161032).length < 2 ^ (prefixWord ++ tailWord_7161032).sum := by decide
  have hdescent : baseEnd_7161032 < baseStart_7161032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161082 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 9]
def baseStart_7161082 : Nat := 118140960795 + 7161082 * 2 ^ 59
def prefixEnd_7161082 : Nat := 4983230072969 + 3 ^ 40 * 7161082 * 2
def baseEnd_7161082 : Nat := 408564119140028496382421

theorem tailTrace_7161082 : CollatzResearch.WordTrace tailWord_7161082 prefixEnd_7161082 408564119140028496382421 := by
  unfold tailWord_7161082
  simp only [CollatzResearch.WordTrace]
  refine ⟨65296529460657601070369375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174124078561753602854318333 65296529460657601070369375)
  ·
    refine ⟨97944794190986401605554063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65296529460657601070369375 97944794190986401605554063)
    ·
      refine ⟨146917191286479602408331095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97944794190986401605554063 146917191286479602408331095)
      ·
        refine ⟨220375786929719403612496643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146917191286479602408331095 220375786929719403612496643)
        ·
          refine ⟨330563680394579105418744965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220375786929719403612496643 330563680394579105418744965)
          ·
            refine ⟨61980690073983582266014681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330563680394579105418744965 61980690073983582266014681)
            ·
              refine ⟨46485517555487686699511011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61980690073983582266014681 46485517555487686699511011)
              ·
                refine ⟨69728276333231530049266517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46485517555487686699511011 69728276333231530049266517)
                ·
                  refine ⟨408564119140028496382421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69728276333231530049266517 408564119140028496382421)
                  ·
                    rfl

theorem cell23_7161082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_7161082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161082 prefixEnd_7161082 := by exact prefixLift 7161082
  have htrace : WordTrace (prefixWord ++ tailWord_7161082) baseStart_7161082 baseEnd_7161082 := by
    simpa [prefixWord, tailWord_7161082, baseEnd_7161082] using wordTrace_append hprefix tailTrace_7161082
  have hstable : (prefixWord ++ tailWord_7161082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161082).length < 2 ^ (prefixWord ++ tailWord_7161082).sum := by decide
  have hdescent : baseEnd_7161082 < baseStart_7161082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161109 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_7161109 : Nat := 118140960795 + 7161109 * 2 ^ 59
def prefixEnd_7161109 : Nat := 4983230072969 + 3 ^ 40 * 7161109 * 2
def baseEnd_7161109 : Nat := 3677090936237927861804165

theorem tailTrace_7161109 : CollatzResearch.WordTrace tailWord_7161109 prefixEnd_7161109 3677090936237927861804165 := by
  unfold tailWord_7161109
  simp only [CollatzResearch.WordTrace]
  refine ⟨261187102613532587892710381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174124735075688391928473587 261187102613532587892710381)
  ·
    refine ⟨97945163480074720459766393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261187102613532587892710381 97945163480074720459766393)
    ·
      refine ⟨73458872610056040344824795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97945163480074720459766393 73458872610056040344824795)
      ·
        refine ⟨110188308915084060517237193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73458872610056040344824795 110188308915084060517237193)
        ·
          refine ⟨82641231686313045387927895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110188308915084060517237193 82641231686313045387927895)
          ·
            refine ⟨123961847529469568081891843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82641231686313045387927895 123961847529469568081891843)
            ·
              refine ⟨185942771294204352122837765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123961847529469568081891843 185942771294204352122837765)
              ·
                refine ⟨34864269617663316023032081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185942771294204352122837765 34864269617663316023032081)
                ·
                  refine ⟨26148202213247487017274061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34864269617663316023032081 26148202213247487017274061)
                  ·
                    refine ⟨9805575829967807631477773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26148202213247487017274061 9805575829967807631477773)
                    ·
                      refine ⟨3677090936237927861804165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9805575829967807631477773 3677090936237927861804165)
                      ·
                        rfl

theorem cell23_7161109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_7161109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161109 prefixEnd_7161109 := by exact prefixLift 7161109
  have htrace : WordTrace (prefixWord ++ tailWord_7161109) baseStart_7161109 baseEnd_7161109 := by
    simpa [prefixWord, tailWord_7161109, baseEnd_7161109] using wordTrace_append hprefix tailTrace_7161109
  have hstable : (prefixWord ++ tailWord_7161109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161109).length < 2 ^ (prefixWord ++ tailWord_7161109).sum := by decide
  have hdescent : baseEnd_7161109 < baseStart_7161109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161166 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2]
def baseStart_7161166 : Nat := 118140960795 + 7161166 * 2 ^ 59
def prefixEnd_7161166 : Nat := 4983230072969 + 3 ^ 40 * 7161166 * 2
def baseEnd_7161166 : Nat := 3677120204635234138791403

theorem tailTrace_7161166 : CollatzResearch.WordTrace tailWord_7161166 prefixEnd_7161166 3677120204635234138791403 := by
  unfold tailWord_7161166
  simp only [CollatzResearch.WordTrace]
  refine ⟨32648647696790760828441919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174126121049550724418356901 32648647696790760828441919)
  ·
    refine ⟨48972971545186141242662879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32648647696790760828441919 48972971545186141242662879)
    ·
      refine ⟨73459457317779211863994319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48972971545186141242662879 73459457317779211863994319)
      ·
        refine ⟨110189185976668817795991479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73459457317779211863994319 110189185976668817795991479)
        ·
          refine ⟨165283778965003226693987219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110189185976668817795991479 165283778965003226693987219)
          ·
            refine ⟨247925668447504840040980829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165283778965003226693987219 247925668447504840040980829)
            ·
              refine ⟨92972125667814315015367811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247925668447504840040980829 92972125667814315015367811)
              ·
                refine ⟨139458188501721472523051717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92972125667814315015367811 139458188501721472523051717)
                ·
                  refine ⟨26148410344072776098072197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139458188501721472523051717 26148410344072776098072197)
                  ·
                    refine ⟨4902826939513645518388537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26148410344072776098072197 4902826939513645518388537)
                    ·
                      refine ⟨3677120204635234138791403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4902826939513645518388537 3677120204635234138791403)
                      ·
                        rfl

theorem cell23_7161166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_7161166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161166 prefixEnd_7161166 := by exact prefixLift 7161166
  have htrace : WordTrace (prefixWord ++ tailWord_7161166) baseStart_7161166 baseEnd_7161166 := by
    simpa [prefixWord, tailWord_7161166, baseEnd_7161166] using wordTrace_append hprefix tailTrace_7161166
  have hstable : (prefixWord ++ tailWord_7161166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161166).length < 2 ^ (prefixWord ++ tailWord_7161166).sum := by decide
  have hdescent : baseEnd_7161166 < baseStart_7161166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161176 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 3, 4]
def baseStart_7161176 : Nat := 118140960795 + 7161176 * 2 ^ 59
def prefixEnd_7161176 : Nat := 4983230072969 + 3 ^ 40 * 7161176 * 2
def baseEnd_7161176 : Nat := 1225708446480593033222119

theorem tailTrace_7161176 : CollatzResearch.WordTrace tailWord_7161176 prefixEnd_7161176 1225708446480593033222119 := by
  unfold tailWord_7161176
  simp only [CollatzResearch.WordTrace]
  refine ⟨130594773152144929167699691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174126364202859905556932921 130594773152144929167699691)
  ·
    refine ⟨195892159728217393751549537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130594773152144929167699691 195892159728217393751549537)
    ·
      refine ⟨146919119796163045313662153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195892159728217393751549537 146919119796163045313662153)
      ·
        refine ⟨110189339847122283985246615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146919119796163045313662153 110189339847122283985246615)
        ·
          refine ⟨165284009770683425977869923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110189339847122283985246615 165284009770683425977869923)
          ·
            refine ⟨247926014656025138966804885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165284009770683425977869923 247926014656025138966804885)
            ·
              refine ⟨11621531937001178389068979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 247926014656025138966804885 11621531937001178389068979)
              ·
                refine ⟨17432297905501767583603469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11621531937001178389068979 17432297905501767583603469)
                ·
                  refine ⟨6537111714563162843851301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17432297905501767583603469 6537111714563162843851301)
                  ·
                    refine ⟨1225708446480593033222119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6537111714563162843851301 1225708446480593033222119)
                    ·
                      rfl

theorem cell23_7161176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_7161176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161176 prefixEnd_7161176 := by exact prefixLift 7161176
  have htrace : WordTrace (prefixWord ++ tailWord_7161176) baseStart_7161176 baseEnd_7161176 := by
    simpa [prefixWord, tailWord_7161176, baseEnd_7161176] using wordTrace_append hprefix tailTrace_7161176
  have hstable : (prefixWord ++ tailWord_7161176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161176).length < 2 ^ (prefixWord ++ tailWord_7161176).sum := by decide
  have hdescent : baseEnd_7161176 < baseStart_7161176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161186 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_7161186 : Nat := 118140960795 + 7161186 * 2 ^ 59
def prefixEnd_7161186 : Nat := 4983230072969 + 3 ^ 40 * 7161186 * 2
def baseEnd_7161186 : Nat := 3677130474248324060541311

theorem tailTrace_7161186 : CollatzResearch.WordTrace tailWord_7161186 prefixEnd_7161186 3677130474248324060541311 := by
  unfold tailWord_7161186
  simp only [CollatzResearch.WordTrace]
  refine ⟨65297477758563407510815853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174126607356169086695508941 65297477758563407510815853)
  ·
    refine ⟨24486554159461277816555945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65297477758563407510815853 24486554159461277816555945)
    ·
      refine ⟨18364915619595958362416959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24486554159461277816555945 18364915619595958362416959)
      ·
        refine ⟨27547373429393937543625439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18364915619595958362416959 27547373429393937543625439)
        ·
          refine ⟨41321060144090906315438159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27547373429393937543625439 41321060144090906315438159)
          ·
            refine ⟨61981590216136359473157239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41321060144090906315438159 61981590216136359473157239)
            ·
              refine ⟨92972385324204539209735859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61981590216136359473157239 92972385324204539209735859)
              ·
                refine ⟨139458577986306808814603789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92972385324204539209735859 139458577986306808814603789)
                ·
                  refine ⟨52296966744865053305476421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139458577986306808814603789 52296966744865053305476421)
                  ·
                    refine ⟨9805681264662197494776829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52296966744865053305476421 9805681264662197494776829)
                    ·
                      refine ⟨3677130474248324060541311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9805681264662197494776829 3677130474248324060541311)
                      ·
                        rfl

theorem cell23_7161186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_7161186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161186 prefixEnd_7161186 := by exact prefixLift 7161186
  have htrace : WordTrace (prefixWord ++ tailWord_7161186) baseStart_7161186 baseEnd_7161186 := by
    simpa [prefixWord, tailWord_7161186, baseEnd_7161186] using wordTrace_append hprefix tailTrace_7161186
  have hstable : (prefixWord ++ tailWord_7161186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161186).length < 2 ^ (prefixWord ++ tailWord_7161186).sum := by decide
  have hdescent : baseEnd_7161186 < baseStart_7161186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161199 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 3]
def baseStart_7161199 : Nat := 118140960795 + 7161199 * 2 ^ 59
def prefixEnd_7161199 : Nat := 4983230072969 + 3 ^ 40 * 7161199 * 2
def baseEnd_7161199 : Nat := 3677137149496832509678751

theorem tailTrace_7161199 : CollatzResearch.WordTrace tailWord_7161199 prefixEnd_7161199 3677137149496832509678751 := by
  unfold tailWord_7161199
  simp only [CollatzResearch.WordTrace]
  refine ⟨261190385183206533263486651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174126923455471022175657767 261190385183206533263486651)
  ·
    refine ⟨391785577774809799895229977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261190385183206533263486651 391785577774809799895229977)
    ·
      refine ⟨293839183331107349921422483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391785577774809799895229977 293839183331107349921422483)
      ·
        refine ⟨440758774996661024882133725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293839183331107349921422483 440758774996661024882133725)
        ·
          refine ⟨165284540623747884330800147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440758774996661024882133725 165284540623747884330800147)
          ·
            refine ⟨247926810935621826496200221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165284540623747884330800147 247926810935621826496200221)
            ·
              refine ⟨92972554100858184936075083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247926810935621826496200221 92972554100858184936075083)
              ·
                refine ⟨139458831151287277404112625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92972554100858184936075083 139458831151287277404112625)
                ·
                  refine ⟨104594123363465458053084469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139458831151287277404112625 104594123363465458053084469)
                  ·
                    refine ⟨9805699065324886692476669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104594123363465458053084469 9805699065324886692476669)
                    ·
                      refine ⟨3677137149496832509678751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9805699065324886692476669 3677137149496832509678751)
                      ·
                        rfl

theorem cell23_7161199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 3].length) (baseStart_7161199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161199 prefixEnd_7161199 := by exact prefixLift 7161199
  have htrace : WordTrace (prefixWord ++ tailWord_7161199) baseStart_7161199 baseEnd_7161199 := by
    simpa [prefixWord, tailWord_7161199, baseEnd_7161199] using wordTrace_append hprefix tailTrace_7161199
  have hstable : (prefixWord ++ tailWord_7161199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161199).length < 2 ^ (prefixWord ++ tailWord_7161199).sum := by decide
  have hdescent : baseEnd_7161199 < baseStart_7161199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161216 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 5, 1, 3]
def baseStart_7161216 : Nat := 118140960795 + 7161216 * 2 ^ 59
def prefixEnd_7161216 : Nat := 4983230072969 + 3 ^ 40 * 7161216 * 2
def baseEnd_7161216 : Nat := 3677145878667958943166173

theorem tailTrace_7161216 : CollatzResearch.WordTrace tailWord_7161216 prefixEnd_7161216 3677145878667958943166173 := by
  unfold tailWord_7161216
  simp only [CollatzResearch.WordTrace]
  refine ⟨130595502612072472583427751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174127336816096630111237001 130595502612072472583427751)
  ·
    refine ⟨195893253918108708875141627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130595502612072472583427751 195893253918108708875141627)
    ·
      refine ⟨293839880877163063312712441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195893253918108708875141627 293839880877163063312712441)
      ·
        refine ⟨220379910657872297484534331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293839880877163063312712441 220379910657872297484534331)
        ·
          refine ⟨330569865986808446226801497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220379910657872297484534331 330569865986808446226801497)
          ·
            refine ⟨247927399490106334670101123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330569865986808446226801497 247927399490106334670101123)
            ·
              refine ⟨371891099235159502005151685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247927399490106334670101123 371891099235159502005151685)
              ·
                refine ⟨69729581106592406625965941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371891099235159502005151685 69729581106592406625965941)
                ·
                  refine ⟨6537148228743038121184307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69729581106592406625965941 6537148228743038121184307)
                  ·
                    refine ⟨9805722343114557181776461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6537148228743038121184307 9805722343114557181776461)
                    ·
                      refine ⟨3677145878667958943166173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9805722343114557181776461 3677145878667958943166173)
                      ·
                        rfl

theorem cell23_7161216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_7161216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161216 prefixEnd_7161216 := by exact prefixLift 7161216
  have htrace : WordTrace (prefixWord ++ tailWord_7161216) baseStart_7161216 baseEnd_7161216 := by
    simpa [prefixWord, tailWord_7161216, baseEnd_7161216] using wordTrace_append hprefix tailTrace_7161216
  have hstable : (prefixWord ++ tailWord_7161216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161216).length < 2 ^ (prefixWord ++ tailWord_7161216).sum := by decide
  have hdescent : baseEnd_7161216 < baseStart_7161216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161239 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_7161239 : Nat := 118140960795 + 7161239 * 2 ^ 59
def prefixEnd_7161239 : Nat := 4983230072969 + 3 ^ 40 * 7161239 * 2
def baseEnd_7161239 : Nat := 3677157688723012353178567

theorem tailTrace_7161239 : CollatzResearch.WordTrace tailWord_7161239 prefixEnd_7161239 3677157688723012353178567 := by
  unfold tailWord_7161239
  simp only [CollatzResearch.WordTrace]
  refine ⟨261191844103061620094942771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174127896068707746729961847 261191844103061620094942771)
  ·
    refine ⟨391787766154592430142414157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261191844103061620094942771 391787766154592430142414157)
    ·
      refine ⟨146920412307972161303405309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391787766154592430142414157 146920412307972161303405309)
      ·
        refine ⟨55095154615489560488776991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146920412307972161303405309 55095154615489560488776991)
        ·
          refine ⟨82642731923234340733165487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55095154615489560488776991 82642731923234340733165487)
          ·
            refine ⟨123964097884851511099748231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82642731923234340733165487 123964097884851511099748231)
            ·
              refine ⟨185946146827277266649622347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123964097884851511099748231 185946146827277266649622347)
              ·
                refine ⟨278919220240915899974433521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185946146827277266649622347 278919220240915899974433521)
                ·
                  refine ⟨209189415180686924980825141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278919220240915899974433521 209189415180686924980825141)
                  ·
                    refine ⟨19611507673189399216952357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209189415180686924980825141 19611507673189399216952357)
                    ·
                      refine ⟨3677157688723012353178567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19611507673189399216952357 3677157688723012353178567)
                      ·
                        rfl

theorem cell23_7161239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_7161239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161239 prefixEnd_7161239 := by exact prefixLift 7161239
  have htrace : WordTrace (prefixWord ++ tailWord_7161239) baseStart_7161239 baseEnd_7161239 := by
    simpa [prefixWord, tailWord_7161239, baseEnd_7161239] using wordTrace_append hprefix tailTrace_7161239
  have hstable : (prefixWord ++ tailWord_7161239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161239).length < 2 ^ (prefixWord ++ tailWord_7161239).sum := by decide
  have hdescent : baseEnd_7161239 < baseStart_7161239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161240 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 6]
def baseStart_7161240 : Nat := 118140960795 + 7161240 * 2 ^ 59
def prefixEnd_7161240 : Nat := 4983230072969 + 3 ^ 40 * 7161240 * 2
def baseEnd_7161240 : Nat := 408573133578185205474007

theorem tailTrace_7161240 : CollatzResearch.WordTrace tailWord_7161240 prefixEnd_7161240 408573133578185205474007 := by
  unfold tailWord_7161240
  simp only [CollatzResearch.WordTrace]
  refine ⟨130595940288028998632864587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174127920384038664843819449 130595940288028998632864587)
  ·
    refine ⟨195893910432043497949296881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130595940288028998632864587 195893910432043497949296881)
    ·
      refine ⟨146920432824032623461972661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195893910432043497949296881 146920432824032623461972661)
      ·
        refine ⟨13773790577253058449559937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146920432824032623461972661 13773790577253058449559937)
        ·
          refine ⟨10330342932939793837169953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13773790577253058449559937 10330342932939793837169953)
          ·
            refine ⟨7747757199704845377877465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10330342932939793837169953 7747757199704845377877465)
            ·
              refine ⟨5810817899778634033408099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7747757199704845377877465 5810817899778634033408099)
              ·
                refine ⟨8716226849667951050112149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5810817899778634033408099 8716226849667951050112149)
                ·
                  refine ⟨408573133578185205474007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8716226849667951050112149 408573133578185205474007)
                  ·
                    rfl

theorem cell23_7161240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 6].length) (baseStart_7161240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161240 prefixEnd_7161240 := by exact prefixLift 7161240
  have htrace : WordTrace (prefixWord ++ tailWord_7161240) baseStart_7161240 baseEnd_7161240 := by
    simpa [prefixWord, tailWord_7161240, baseEnd_7161240] using wordTrace_append hprefix tailTrace_7161240
  have hstable : (prefixWord ++ tailWord_7161240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161240).length < 2 ^ (prefixWord ++ tailWord_7161240).sum := by decide
  have hdescent : baseEnd_7161240 < baseStart_7161240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161266 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_7161266 : Nat := 118140960795 + 7161266 * 2 ^ 59
def prefixEnd_7161266 : Nat := 4983230072969 + 3 ^ 40 * 7161266 * 2
def baseEnd_7161266 : Nat := 1225723850900227915846981

theorem tailTrace_7161266 : CollatzResearch.WordTrace tailWord_7161266 prefixEnd_7161266 1225723850900227915846981 := by
  unfold tailWord_7161266
  simp only [CollatzResearch.WordTrace]
  refine ⟨65298207218490950926543913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174128552582642535804117101 65298207218490950926543913)
  ·
    refine ⟨48973655413868213194907935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65298207218490950926543913 48973655413868213194907935)
    ·
      refine ⟨73460483120802319792361903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48973655413868213194907935 73460483120802319792361903)
      ·
        refine ⟨110190724681203479688542855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73460483120802319792361903 110190724681203479688542855)
        ·
          refine ⟨165286087021805219532814283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110190724681203479688542855 165286087021805219532814283)
          ·
            refine ⟨247929130532707829299221425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165286087021805219532814283 247929130532707829299221425)
            ·
              refine ⟨185946847899530871974416069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247929130532707829299221425 185946847899530871974416069)
              ·
                refine ⟨34865033981162038495203013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185946847899530871974416069 34865033981162038495203013)
                ·
                  refine ⟨6537193871467882217850565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34865033981162038495203013 6537193871467882217850565)
                  ·
                    refine ⟨1225723850900227915846981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6537193871467882217850565 1225723850900227915846981)
                    ·
                      rfl

theorem cell23_7161266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_7161266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161266 prefixEnd_7161266 := by exact prefixLift 7161266
  have htrace : WordTrace (prefixWord ++ tailWord_7161266) baseStart_7161266 baseEnd_7161266 := by
    simpa [prefixWord, tailWord_7161266, baseEnd_7161266] using wordTrace_append hprefix tailTrace_7161266
  have hstable : (prefixWord ++ tailWord_7161266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161266).length < 2 ^ (prefixWord ++ tailWord_7161266).sum := by decide
  have hdescent : baseEnd_7161266 < baseStart_7161266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161284 : List Nat := [2, 3, 3, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_7161284 : Nat := 118140960795 + 7161284 * 2 ^ 59
def prefixEnd_7161284 : Nat := 4983230072969 + 3 ^ 40 * 7161284 * 2
def baseEnd_7161284 : Nat := 3677180795352464677115861

theorem tailTrace_7161284 : CollatzResearch.WordTrace tailWord_7161284 prefixEnd_7161284 3677180795352464677115861 := by
  unfold tailWord_7161284
  simp only [CollatzResearch.WordTrace]
  refine ⟨130596742693949296390165453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174128990258599061853553937 130596742693949296390165453)
  ·
    refine ⟨48973778510230986146312045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130596742693949296390165453 48973778510230986146312045)
    ·
      refine ⟨18365166941336619804867017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48973778510230986146312045 18365166941336619804867017)
      ·
        refine ⟨13773875206002464853650263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18365166941336619804867017 13773875206002464853650263)
        ·
          refine ⟨20660812809003697280475395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13773875206002464853650263 20660812809003697280475395)
          ·
            refine ⟨30991219213505545920713093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20660812809003697280475395 30991219213505545920713093)
            ·
              refine ⟨5810853602532289860133705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30991219213505545920713093 5810853602532289860133705)
              ·
                refine ⟨4358140201899217395100279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5810853602532289860133705 4358140201899217395100279)
                ·
                  refine ⟨6537210302848826092650419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358140201899217395100279 6537210302848826092650419)
                  ·
                    refine ⟨9805815454273239138975629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6537210302848826092650419 9805815454273239138975629)
                    ·
                      refine ⟨3677180795352464677115861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9805815454273239138975629 3677180795352464677115861)
                      ·
                        rfl

theorem cell23_7161284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_7161284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161284 prefixEnd_7161284 := by exact prefixLift 7161284
  have htrace : WordTrace (prefixWord ++ tailWord_7161284) baseStart_7161284 baseEnd_7161284 := by
    simpa [prefixWord, tailWord_7161284, baseEnd_7161284] using wordTrace_append hprefix tailTrace_7161284
  have hstable : (prefixWord ++ tailWord_7161284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161284).length < 2 ^ (prefixWord ++ tailWord_7161284).sum := by decide
  have hdescent : baseEnd_7161284 < baseStart_7161284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161339 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 3, 8]
def baseStart_7161339 : Nat := 118140960795 + 7161339 * 2 ^ 59
def prefixEnd_7161339 : Nat := 4983230072969 + 3 ^ 40 * 7161339 * 2
def baseEnd_7161339 : Nat := 1225736345596153987309369

theorem tailTrace_7161339 : CollatzResearch.WordTrace tailWord_7161339 prefixEnd_7161339 1225736345596153987309369 := by
  unfold tailWord_7161339
  simp only [CollatzResearch.WordTrace]
  refine ⟨261195491402699337173583071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174130327601799558115722047 261195491402699337173583071)
  ·
    refine ⟨391793237104049005760374607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261195491402699337173583071 391793237104049005760374607)
    ·
      refine ⟨587689855656073508640561911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391793237104049005760374607 587689855656073508640561911)
      ·
        refine ⟨881534783484110262960842867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587689855656073508640561911 881534783484110262960842867)
        ·
          refine ⟨1322302175226165394441264301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881534783484110262960842867 1322302175226165394441264301)
          ·
            refine ⟨495863315709812022915474113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1322302175226165394441264301 495863315709812022915474113)
            ·
              refine ⟨371897486782359017186605585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495863315709812022915474113 371897486782359017186605585)
              ·
                refine ⟨278923115086769262889954189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371897486782359017186605585 278923115086769262889954189)
                ·
                  refine ⟨104596168157538473583732821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278923115086769262889954189 104596168157538473583732821)
                  ·
                    refine ⟨1225736345596153987309369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104596168157538473583732821 1225736345596153987309369)
                    ·
                      rfl

theorem cell23_7161339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 8].length) (baseStart_7161339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161339 prefixEnd_7161339 := by exact prefixLift 7161339
  have htrace : WordTrace (prefixWord ++ tailWord_7161339) baseStart_7161339 baseEnd_7161339 := by
    simpa [prefixWord, tailWord_7161339, baseEnd_7161339] using wordTrace_append hprefix tailTrace_7161339
  have hstable : (prefixWord ++ tailWord_7161339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161339).length < 2 ^ (prefixWord ++ tailWord_7161339).sum := by decide
  have hdescent : baseEnd_7161339 < baseStart_7161339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161340 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_7161340 : Nat := 118140960795 + 7161340 * 2 ^ 59
def prefixEnd_7161340 : Nat := 4983230072969 + 3 ^ 40 * 7161340 * 2
def baseEnd_7161340 : Nat := 3677209550269116458015603

theorem tailTrace_7161340 : CollatzResearch.WordTrace tailWord_7161340 prefixEnd_7161340 3677209550269116458015603 := by
  unfold tailWord_7161340
  simp only [CollatzResearch.WordTrace]
  refine ⟨130597763937847857172184737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174130351917130476229579649 130597763937847857172184737)
  ·
    refine ⟨97948322953385892879138553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130597763937847857172184737 97948322953385892879138553)
    ·
      refine ⟨73461242215039419659353915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97948322953385892879138553 73461242215039419659353915)
      ·
        refine ⟨110191863322559129489030873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73461242215039419659353915 110191863322559129489030873)
        ·
          refine ⟨82643897491919347116773155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110191863322559129489030873 82643897491919347116773155)
          ·
            refine ⟨123965846237879020675159733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82643897491919347116773155 123965846237879020675159733)
            ·
              refine ⟨11621798084801158188296225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123965846237879020675159733 11621798084801158188296225)
              ·
                refine ⟨8716348563600868641222169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11621798084801158188296225 8716348563600868641222169)
                ·
                  refine ⟨6537261422700651480916627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8716348563600868641222169 6537261422700651480916627)
                  ·
                    refine ⟨9805892134050977221374941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6537261422700651480916627 9805892134050977221374941)
                    ·
                      refine ⟨3677209550269116458015603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9805892134050977221374941 3677209550269116458015603)
                      ·
                        rfl

theorem cell23_7161340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_7161340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161340 prefixEnd_7161340 := by exact prefixLift 7161340
  have htrace : WordTrace (prefixWord ++ tailWord_7161340) baseStart_7161340 baseEnd_7161340 := by
    simpa [prefixWord, tailWord_7161340, baseEnd_7161340] using wordTrace_append hprefix tailTrace_7161340
  have hstable : (prefixWord ++ tailWord_7161340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161340).length < 2 ^ (prefixWord ++ tailWord_7161340).sum := by decide
  have hdescent : baseEnd_7161340 < baseStart_7161340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161454 : List Nat := [4, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_7161454 : Nat := 118140960795 + 7161454 * 2 ^ 59
def prefixEnd_7161454 : Nat := 4983230072969 + 3 ^ 40 * 7161454 * 2
def baseEnd_7161454 : Nat := 408585343007081001332231

theorem tailTrace_7161454 : CollatzResearch.WordTrace tailWord_7161454 prefixEnd_7161454 408585343007081001332231 := by
  unfold tailWord_7161454
  simp only [CollatzResearch.WordTrace]
  refine ⟨32649960724660338976752427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174133123864855141209346277 32649960724660338976752427)
  ·
    refine ⟨48974941086990508465128641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32649960724660338976752427 48974941086990508465128641)
    ·
      refine ⟨36731205815242881348846481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48974941086990508465128641 36731205815242881348846481)
      ·
        refine ⟨27548404361432161011634861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36731205815242881348846481 27548404361432161011634861)
        ·
          refine ⟨10330651635537060379363073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27548404361432161011634861 10330651635537060379363073)
          ·
            refine ⟨7747988726652795284522305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10330651635537060379363073 7747988726652795284522305)
            ·
              refine ⟨5810991544989596463391729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7747988726652795284522305 5810991544989596463391729)
              ·
                refine ⟨4358243658742197347543797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5810991544989596463391729 4358243658742197347543797)
                ·
                  refine ⟨408585343007081001332231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4358243658742197347543797 408585343007081001332231)
                  ·
                    rfl

theorem cell23_7161454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_7161454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161454 prefixEnd_7161454 := by exact prefixLift 7161454
  have htrace : WordTrace (prefixWord ++ tailWord_7161454) baseStart_7161454 baseEnd_7161454 := by
    simpa [prefixWord, tailWord_7161454, baseEnd_7161454] using wordTrace_append hprefix tailTrace_7161454
  have hstable : (prefixWord ++ tailWord_7161454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161454).length < 2 ^ (prefixWord ++ tailWord_7161454).sum := by decide
  have hdescent : baseEnd_7161454 < baseStart_7161454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161463 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 3, 4]
def baseStart_7161463 : Nat := 118140960795 + 7161463 * 2 ^ 59
def prefixEnd_7161463 : Nat := 4983230072969 + 3 ^ 40 * 7161463 * 2
def baseEnd_7161463 : Nat := 1225757569463206492259179

theorem tailTrace_7161463 : CollatzResearch.WordTrace tailWord_7161463 prefixEnd_7161463 1225757569463206492259179 := by
  unfold tailWord_7161463
  simp only [CollatzResearch.WordTrace]
  refine ⟨261200014054250106351097043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174133342702833404234064695 261200014054250106351097043)
  ·
    refine ⟨391800021081375159526645565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261200014054250106351097043 391800021081375159526645565)
    ·
      refine ⟨146925007905515684822492087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391800021081375159526645565 146925007905515684822492087)
      ·
        refine ⟨220387511858273527233738131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146925007905515684822492087 220387511858273527233738131)
        ·
          refine ⟨330581267787410290850607197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220387511858273527233738131 330581267787410290850607197)
          ·
            refine ⟨123967975420278859068977699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330581267787410290850607197 123967975420278859068977699)
            ·
              refine ⟨185951963130418288603466549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123967975420278859068977699 185951963130418288603466549)
              ·
                refine ⟨17432996543476714556574989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185951963130418288603466549 17432996543476714556574989)
                ·
                  refine ⟨6537373703803767958715621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17432996543476714556574989 6537373703803767958715621)
                  ·
                    refine ⟨1225757569463206492259179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6537373703803767958715621 1225757569463206492259179)
                    ·
                      rfl

theorem cell23_7161463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_7161463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161463 prefixEnd_7161463 := by exact prefixLift 7161463
  have htrace : WordTrace (prefixWord ++ tailWord_7161463) baseStart_7161463 baseEnd_7161463 := by
    simpa [prefixWord, tailWord_7161463, baseEnd_7161463] using wordTrace_append hprefix tailTrace_7161463
  have hstable : (prefixWord ++ tailWord_7161463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161463).length < 2 ^ (prefixWord ++ tailWord_7161463).sum := by decide
  have hdescent : baseEnd_7161463 < baseStart_7161463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161466 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_7161466 : Nat := 118140960795 + 7161466 * 2 ^ 59
def prefixEnd_7161466 : Nat := 4983230072969 + 3 ^ 40 * 7161466 * 2
def baseEnd_7161466 : Nat := 3677274248831582965040023

theorem tailTrace_7161466 : CollatzResearch.WordTrace tailWord_7161466 prefixEnd_7161466 3677274248831582965040023 := by
  unfold tailWord_7161466
  simp only [CollatzResearch.WordTrace]
  refine ⟨65300030868309809465864063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174133415648826158575637501 65300030868309809465864063)
  ·
    refine ⟨97950046302464714198796095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65300030868309809465864063 97950046302464714198796095)
    ·
      refine ⟨146925069453697071298194143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97950046302464714198796095 146925069453697071298194143)
      ·
        refine ⟨220387604180545606947291215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146925069453697071298194143 220387604180545606947291215)
        ·
          refine ⟨330581406270818410420936823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220387604180545606947291215 330581406270818410420936823)
          ·
            refine ⟨495872109406227615631405235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330581406270818410420936823 495872109406227615631405235)
            ·
              refine ⟨743808164109341423447107853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495872109406227615631405235 743808164109341423447107853)
              ·
                refine ⟨278928061541003033792665445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 743808164109341423447107853 278928061541003033792665445)
                ·
                  refine ⟨52299011538938068836124771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278928061541003033792665445 52299011538938068836124771)
                  ·
                    refine ⟨78448517308407103254187157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52299011538938068836124771 78448517308407103254187157)
                    ·
                      refine ⟨3677274248831582965040023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78448517308407103254187157 3677274248831582965040023)
                      ·
                        rfl

theorem cell23_7161466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_7161466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161466 prefixEnd_7161466 := by exact prefixLift 7161466
  have htrace : WordTrace (prefixWord ++ tailWord_7161466) baseStart_7161466 baseEnd_7161466 := by
    simpa [prefixWord, tailWord_7161466, baseEnd_7161466] using wordTrace_append hprefix tailTrace_7161466
  have hstable : (prefixWord ++ tailWord_7161466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161466).length < 2 ^ (prefixWord ++ tailWord_7161466).sum := by decide
  have hdescent : baseEnd_7161466 < baseStart_7161466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161520 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 3, 1, 3]
def baseStart_7161520 : Nat := 118140960795 + 7161520 * 2 ^ 59
def prefixEnd_7161520 : Nat := 4983230072969 + 3 ^ 40 * 7161520 * 2
def baseEnd_7161520 : Nat := 3677301976786925753764775

theorem tailTrace_7161520 : CollatzResearch.WordTrace tailWord_7161520 prefixEnd_7161520 3677301976786925753764775 := by
  unfold tailWord_7161520
  simp only [CollatzResearch.WordTrace]
  refine ⟨130601046507521802542961007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174134728676695736723948009 130601046507521802542961007)
  ·
    refine ⟨195901569761282703814441511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130601046507521802542961007 195901569761282703814441511)
    ·
      refine ⟨293852354641924055721662267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195901569761282703814441511 293852354641924055721662267)
      ·
        refine ⟨440778531962886083582493401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293852354641924055721662267 440778531962886083582493401)
        ·
          refine ⟨330583898972164562686870051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440778531962886083582493401 330583898972164562686870051)
          ·
            refine ⟨495875848458246844030305077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330583898972164562686870051 495875848458246844030305077)
            ·
              refine ⟨46488360792960641627841101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 495875848458246844030305077 46488360792960641627841101)
              ·
                refine ⟨17433135297360240610440413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46488360792960641627841101 17433135297360240610440413)
                ·
                  refine ⟨6537425736510090228915155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17433135297360240610440413 6537425736510090228915155)
                  ·
                    refine ⟨9806138604765135343372733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6537425736510090228915155 9806138604765135343372733)
                    ·
                      refine ⟨3677301976786925753764775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9806138604765135343372733 3677301976786925753764775)
                      ·
                        rfl

theorem cell23_7161520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3, 1, 3].length) (baseStart_7161520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161520 prefixEnd_7161520 := by exact prefixLift 7161520
  have htrace : WordTrace (prefixWord ++ tailWord_7161520) baseStart_7161520 baseEnd_7161520 := by
    simpa [prefixWord, tailWord_7161520, baseEnd_7161520] using wordTrace_append hprefix tailTrace_7161520
  have hstable : (prefixWord ++ tailWord_7161520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161520).length < 2 ^ (prefixWord ++ tailWord_7161520).sum := by decide
  have hdescent : baseEnd_7161520 < baseStart_7161520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161530 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2]
def baseStart_7161530 : Nat := 118140960795 + 7161530 * 2 ^ 59
def prefixEnd_7161530 : Nat := 4983230072969 + 3 ^ 40 * 7161530 * 2
def baseEnd_7161530 : Nat := 3677307111593470714639729

theorem tailTrace_7161530 : CollatzResearch.WordTrace tailWord_7161530 prefixEnd_7161530 3677307111593470714639729 := by
  unfold tailWord_7161530
  simp only [CollatzResearch.WordTrace]
  refine ⟨65300614436251844198446511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174134971830004917862524029 65300614436251844198446511)
  ·
    refine ⟨97950921654377766297669767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65300614436251844198446511 97950921654377766297669767)
    ·
      refine ⟨146926382481566649446504651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97950921654377766297669767 146926382481566649446504651)
      ·
        refine ⟨220389573722349974169756977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146926382481566649446504651 220389573722349974169756977)
        ·
          refine ⟨165292180291762480627317733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220389573722349974169756977 165292180291762480627317733)
          ·
            refine ⟨30992283804705465117622075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165292180291762480627317733 30992283804705465117622075)
            ·
              refine ⟨46488425707058197676433113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30992283804705465117622075 46488425707058197676433113)
              ·
                refine ⟨34866319280293648257324835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46488425707058197676433113 34866319280293648257324835)
                ·
                  refine ⟨52299478920440472385987253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34866319280293648257324835 52299478920440472385987253)
                  ·
                    refine ⟨4903076148791294286186305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52299478920440472385987253 4903076148791294286186305)
                    ·
                      refine ⟨3677307111593470714639729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903076148791294286186305 3677307111593470714639729)
                      ·
                        rfl

theorem cell23_7161530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_7161530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161530 prefixEnd_7161530 := by exact prefixLift 7161530
  have htrace : WordTrace (prefixWord ++ tailWord_7161530) baseStart_7161530 baseEnd_7161530 := by
    simpa [prefixWord, tailWord_7161530, baseEnd_7161530] using wordTrace_append hprefix tailTrace_7161530
  have hstable : (prefixWord ++ tailWord_7161530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161530).length < 2 ^ (prefixWord ++ tailWord_7161530).sum := by decide
  have hdescent : baseEnd_7161530 < baseStart_7161530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161560 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 1, 1, 4]
def baseStart_7161560 : Nat := 118140960795 + 7161560 * 2 ^ 59
def prefixEnd_7161560 : Nat := 4983230072969 + 3 ^ 40 * 7161560 * 2
def baseEnd_7161560 : Nat := 3677322516013105597264591

theorem tailTrace_7161560 : CollatzResearch.WordTrace tailWord_7161560 prefixEnd_7161560 3677322516013105597264591 := by
  unfold tailWord_7161560
  simp only [CollatzResearch.WordTrace]
  refine ⟨130601775967449345958689067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174135701289932461278252089 130601775967449345958689067)
  ·
    refine ⟨195902663951174018938033601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130601775967449345958689067 195902663951174018938033601)
    ·
      refine ⟨146926997963380514203525201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195902663951174018938033601 146926997963380514203525201)
      ·
        refine ⟨110195248472535385652643901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146926997963380514203525201 110195248472535385652643901)
        ·
          refine ⟨41323218177200769619741463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110195248472535385652643901 41323218177200769619741463)
          ·
            refine ⟨61984827265801154429612195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41323218177200769619741463 61984827265801154429612195)
            ·
              refine ⟨92977240898701731644418293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61984827265801154429612195 92977240898701731644418293)
              ·
                refine ⟨8716616334253287341664215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92977240898701731644418293 8716616334253287341664215)
                ·
                  refine ⟨13074924501379931012496323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8716616334253287341664215 13074924501379931012496323)
                  ·
                    refine ⟨19612386752069896518744485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13074924501379931012496323 19612386752069896518744485)
                    ·
                      refine ⟨3677322516013105597264591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19612386752069896518744485 3677322516013105597264591)
                      ·
                        rfl

theorem cell23_7161560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_7161560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161560 prefixEnd_7161560 := by exact prefixLift 7161560
  have htrace : WordTrace (prefixWord ++ tailWord_7161560) baseStart_7161560 baseEnd_7161560 := by
    simpa [prefixWord, tailWord_7161560, baseEnd_7161560] using wordTrace_append hprefix tailTrace_7161560
  have hstable : (prefixWord ++ tailWord_7161560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161560).length < 2 ^ (prefixWord ++ tailWord_7161560).sum := by decide
  have hdescent : baseEnd_7161560 < baseStart_7161560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161571 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7161571 : Nat := 118140960795 + 7161571 * 2 ^ 59
def prefixEnd_7161571 : Nat := 4983230072969 + 3 ^ 40 * 7161571 * 2
def baseEnd_7161571 : Nat := 3677328164300305054227041

theorem tailTrace_7161571 : CollatzResearch.WordTrace tailWord_7161571 prefixEnd_7161571 3677328164300305054227041 := by
  unfold tailWord_7161571
  simp only [CollatzResearch.WordTrace]
  refine ⟨261203953137858840796028567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174135968758572560530685711 261203953137858840796028567)
  ·
    refine ⟨391805929706788261194042851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261203953137858840796028567 391805929706788261194042851)
    ·
      refine ⟨587708894560182391791064277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391805929706788261194042851 587708894560182391791064277)
      ·
        refine ⟨13774427216254274807603069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 587708894560182391791064277 13774427216254274807603069)
        ·
          refine ⟨5165410206095353052851151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13774427216254274807603069 5165410206095353052851151)
          ·
            refine ⟨7748115309143029579276727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165410206095353052851151 7748115309143029579276727)
            ·
              refine ⟨11622172963714544368915091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748115309143029579276727 11622172963714544368915091)
              ·
                refine ⟨17433259445571816553372637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11622172963714544368915091 17433259445571816553372637)
                ·
                  refine ⟨6537472292089431207514739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17433259445571816553372637 6537472292089431207514739)
                  ·
                    refine ⟨9806208438134146811272109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6537472292089431207514739 9806208438134146811272109)
                    ·
                      refine ⟨3677328164300305054227041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9806208438134146811272109 3677328164300305054227041)
                      ·
                        rfl

theorem cell23_7161571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7161571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161571 prefixEnd_7161571 := by exact prefixLift 7161571
  have htrace : WordTrace (prefixWord ++ tailWord_7161571) baseStart_7161571 baseEnd_7161571 := by
    simpa [prefixWord, tailWord_7161571, baseEnd_7161571] using wordTrace_append hprefix tailTrace_7161571
  have hstable : (prefixWord ++ tailWord_7161571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161571).length < 2 ^ (prefixWord ++ tailWord_7161571).sum := by decide
  have hdescent : baseEnd_7161571 < baseStart_7161571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161573 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_7161573 : Nat := 118140960795 + 7161573 * 2 ^ 59
def prefixEnd_7161573 : Nat := 4983230072969 + 3 ^ 40 * 7161573 * 2
def baseEnd_7161573 : Nat := 3677329191261614046402031

theorem tailTrace_7161573 : CollatzResearch.WordTrace tailWord_7161573 prefixEnd_7161573 3677329191261614046402031 := by
  unfold tailWord_7161573
  simp only [CollatzResearch.WordTrace]
  refine ⟨261204026083851595137601373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174136017389234396758400915 261204026083851595137601373)
  ·
    refine ⟨97951509781444348176600515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261204026083851595137601373 97951509781444348176600515)
    ·
      refine ⟨146927264672166522264900773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97951509781444348176600515 146927264672166522264900773)
      ·
        refine ⟨27548862126031222924668895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146927264672166522264900773 27548862126031222924668895)
        ·
          refine ⟨41323293189046834387003343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27548862126031222924668895 41323293189046834387003343)
          ·
            refine ⟨61984939783570251580505015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41323293189046834387003343 61984939783570251580505015)
            ·
              refine ⟨92977409675355377370757523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61984939783570251580505015 92977409675355377370757523)
              ·
                refine ⟨139466114513033066056136285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92977409675355377370757523 139466114513033066056136285)
                ·
                  refine ⟨52299792942387399771051107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139466114513033066056136285 52299792942387399771051107)
                  ·
                    refine ⟨78449689413581099656576661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52299792942387399771051107 78449689413581099656576661)
                    ·
                      refine ⟨3677329191261614046402031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78449689413581099656576661 3677329191261614046402031)
                      ·
                        rfl

theorem cell23_7161573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_7161573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161573 prefixEnd_7161573 := by exact prefixLift 7161573
  have htrace : WordTrace (prefixWord ++ tailWord_7161573) baseStart_7161573 baseEnd_7161573 := by
    simpa [prefixWord, tailWord_7161573, baseEnd_7161573] using wordTrace_append hprefix tailTrace_7161573
  have hstable : (prefixWord ++ tailWord_7161573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161573).length < 2 ^ (prefixWord ++ tailWord_7161573).sum := by decide
  have hdescent : baseEnd_7161573 < baseStart_7161573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161583 : List Nat := [1, 1, 2, 1, 5, 1, 4, 8]
def baseStart_7161583 : Nat := 118140960795 + 7161583 * 2 ^ 59
def prefixEnd_7161583 : Nat := 4983230072969 + 3 ^ 40 * 7161583 * 2
def baseEnd_7161583 : Nat := 136197567632154037306555

theorem tailTrace_7161583 : CollatzResearch.WordTrace tailWord_7161583 prefixEnd_7161583 136197567632154037306555 := by
  unfold tailWord_7161583
  simp only [CollatzResearch.WordTrace]
  refine ⟨261204390813815366845465403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174136260542543577896976935 261204390813815366845465403)
  ·
    refine ⟨391806586220723050268198105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261204390813815366845465403 391806586220723050268198105)
    ·
      refine ⟨293854939665542287701148579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391806586220723050268198105 293854939665542287701148579)
      ·
        refine ⟨440782409498313431551722869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293854939665542287701148579 440782409498313431551722869)
        ·
          refine ⟨41323350890466884207974019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 440782409498313431551722869 41323350890466884207974019)
          ·
            refine ⟨61985026335700326311961029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41323350890466884207974019 61985026335700326311961029)
            ·
              refine ⟨11622192437943811183492693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61985026335700326311961029 11622192437943811183492693)
              ·
                refine ⟨136197567632154037306555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11622192437943811183492693 136197567632154037306555)
                ·
                  rfl

theorem cell23_7161583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 8].length) (baseStart_7161583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161583 prefixEnd_7161583 := by exact prefixLift 7161583
  have htrace : WordTrace (prefixWord ++ tailWord_7161583) baseStart_7161583 baseEnd_7161583 := by
    simpa [prefixWord, tailWord_7161583, baseEnd_7161583] using wordTrace_append hprefix tailTrace_7161583
  have hstable : (prefixWord ++ tailWord_7161583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161583).length < 2 ^ (prefixWord ++ tailWord_7161583).sum := by decide
  have hdescent : baseEnd_7161583 < baseStart_7161583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161587 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 2, 4]
def baseStart_7161587 : Nat := 118140960795 + 7161587 * 2 ^ 59
def prefixEnd_7161587 : Nat := 4983230072969 + 3 ^ 40 * 7161587 * 2
def baseEnd_7161587 : Nat := 1225778793330258997208989

theorem tailTrace_7161587 : CollatzResearch.WordTrace tailWord_7161587 prefixEnd_7161587 1225778793330258997208989 := by
  unfold tailWord_7161587
  simp only [CollatzResearch.WordTrace]
  refine ⟨261204536705800875528611015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174136357803867250352407343 261204536705800875528611015)
  ·
    refine ⟨391806805058701313292916523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261204536705800875528611015 391806805058701313292916523)
    ·
      refine ⟨587710207588051969939374785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391806805058701313292916523 587710207588051969939374785)
      ·
        refine ⟨440782655691038977454531089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587710207588051969939374785 440782655691038977454531089)
        ·
          refine ⟨330586991768279233090898317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440782655691038977454531089 330586991768279233090898317)
          ·
            refine ⟨123970121913104712409086869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330586991768279233090898317 123970121913104712409086869)
            ·
              refine ⟨5811099464676783394175947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123970121913104712409086869 5811099464676783394175947)
              ·
                refine ⟨8716649197015175091263921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811099464676783394175947 8716649197015175091263921)
                ·
                  refine ⟨6537486897761381318447941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8716649197015175091263921 6537486897761381318447941)
                  ·
                    refine ⟨1225778793330258997208989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6537486897761381318447941 1225778793330258997208989)
                    ·
                      rfl

theorem cell23_7161587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 2, 4].length) (baseStart_7161587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161587 prefixEnd_7161587 := by exact prefixLift 7161587
  have htrace : WordTrace (prefixWord ++ tailWord_7161587) baseStart_7161587 baseEnd_7161587 := by
    simpa [prefixWord, tailWord_7161587, baseEnd_7161587] using wordTrace_append hprefix tailTrace_7161587
  have hstable : (prefixWord ++ tailWord_7161587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161587).length < 2 ^ (prefixWord ++ tailWord_7161587).sum := by decide
  have hdescent : baseEnd_7161587 < baseStart_7161587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161590 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_7161590 : Nat := 118140960795 + 7161590 * 2 ^ 59
def prefixEnd_7161590 : Nat := 4983230072969 + 3 ^ 40 * 7161590 * 2
def baseEnd_7161590 : Nat := 3677337920432740479889453

theorem tailTrace_7161590 : CollatzResearch.WordTrace tailWord_7161590 prefixEnd_7161590 3677337920432740479889453 := by
  unfold tailWord_7161590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16325290382799375440060639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174136430749860004693980149 16325290382799375440060639)
  ·
    refine ⟨24487935574199063160090959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16325290382799375440060639 24487935574199063160090959)
    ·
      refine ⟨36731903361298594740136439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24487935574199063160090959 36731903361298594740136439)
      ·
        refine ⟨55097855041947892110204659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36731903361298594740136439 55097855041947892110204659)
        ·
          refine ⟨82646782562921838165306989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55097855041947892110204659 82646782562921838165306989)
          ·
            refine ⟨30992543461095689311990121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82646782562921838165306989 30992543461095689311990121)
            ·
              refine ⟨23244407595821766983992591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30992543461095689311990121 23244407595821766983992591)
              ·
                refine ⟨34866611393732650475988887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23244407595821766983992591 34866611393732650475988887)
                ·
                  refine ⟨52299917090598975713983331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34866611393732650475988887 52299917090598975713983331)
                  ·
                    refine ⟨78449875635898463570974997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52299917090598975713983331 78449875635898463570974997)
                    ·
                      refine ⟨3677337920432740479889453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78449875635898463570974997 3677337920432740479889453)
                      ·
                        rfl

theorem cell23_7161590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_7161590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161590 prefixEnd_7161590 := by exact prefixLift 7161590
  have htrace : WordTrace (prefixWord ++ tailWord_7161590) baseStart_7161590 baseEnd_7161590 := by
    simpa [prefixWord, tailWord_7161590, baseEnd_7161590] using wordTrace_append hprefix tailTrace_7161590
  have hstable : (prefixWord ++ tailWord_7161590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161590).length < 2 ^ (prefixWord ++ tailWord_7161590).sum := by decide
  have hdescent : baseEnd_7161590 < baseStart_7161590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161607 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_7161607 : Nat := 118140960795 + 7161607 * 2 ^ 59
def prefixEnd_7161607 : Nat := 4983230072969 + 3 ^ 40 * 7161607 * 2
def baseEnd_7161607 : Nat := 3677346649603866913376875

theorem tailTrace_7161607 : CollatzResearch.WordTrace tailWord_7161607 prefixEnd_7161607 3677346649603866913376875 := by
  unfold tailWord_7161607
  simp only [CollatzResearch.WordTrace]
  refine ⟨261205266165728418944339075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174136844110485612629559383 261205266165728418944339075)
  ·
    refine ⟨391807899248592628416508613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261205266165728418944339075 391807899248592628416508613)
    ·
      refine ⟨73463981109111117828095365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391807899248592628416508613 73463981109111117828095365)
      ·
        refine ⟨13774496457958334592767881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73463981109111117828095365 13774496457958334592767881)
        ·
          refine ⟨10330872343468750944575911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13774496457958334592767881 10330872343468750944575911)
          ·
            refine ⟨15496308515203126416863867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10330872343468750944575911 15496308515203126416863867)
            ·
              refine ⟨23244462772804689625295801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15496308515203126416863867 23244462772804689625295801)
              ·
                refine ⟨17433347079603517218971851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23244462772804689625295801 17433347079603517218971851)
                ·
                  refine ⟨26150020619405275828457777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17433347079603517218971851 26150020619405275828457777)
                  ·
                    refine ⟨19612515464553956871343333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26150020619405275828457777 19612515464553956871343333)
                    ·
                      refine ⟨3677346649603866913376875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19612515464553956871343333 3677346649603866913376875)
                      ·
                        rfl

theorem cell23_7161607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_7161607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161607 prefixEnd_7161607 := by exact prefixLift 7161607
  have htrace : WordTrace (prefixWord ++ tailWord_7161607) baseStart_7161607 baseEnd_7161607 := by
    simpa [prefixWord, tailWord_7161607, baseEnd_7161607] using wordTrace_append hprefix tailTrace_7161607
  have hstable : (prefixWord ++ tailWord_7161607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161607).length < 2 ^ (prefixWord ++ tailWord_7161607).sum := by decide
  have hdescent : baseEnd_7161607 < baseStart_7161607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161610 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_7161610 : Nat := 118140960795 + 7161610 * 2 ^ 59
def prefixEnd_7161610 : Nat := 4983230072969 + 3 ^ 40 * 7161610 * 2
def baseEnd_7161610 : Nat := 3677348190045830401639361

theorem tailTrace_7161610 : CollatzResearch.WordTrace tailWord_7161610 prefixEnd_7161610 3677348190045830401639361 := by
  unfold tailWord_7161610
  simp only [CollatzResearch.WordTrace]
  refine ⟨65301343896179387614174571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174136917056478366971132189 65301343896179387614174571)
  ·
    refine ⟨97952015844269081421261857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65301343896179387614174571 97952015844269081421261857)
    ·
      refine ⟨73464011883201811065946393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97952015844269081421261857 73464011883201811065946393)
      ·
        refine ⟨55098008912401358299459795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73464011883201811065946393 55098008912401358299459795)
        ·
          refine ⟨82647013368602037449189693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55098008912401358299459795 82647013368602037449189693)
          ·
            refine ⟨30992630013225764043446135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82647013368602037449189693 30992630013225764043446135)
            ·
              refine ⟨46488945019838646065169203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30992630013225764043446135 46488945019838646065169203)
              ·
                refine ⟨69733417529757969097753805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46488945019838646065169203 69733417529757969097753805)
                ·
                  refine ⟨26150031573659238411657677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69733417529757969097753805 26150031573659238411657677)
                  ·
                    refine ⟨9806261840122214404371629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26150031573659238411657677 9806261840122214404371629)
                    ·
                      refine ⟨3677348190045830401639361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9806261840122214404371629 3677348190045830401639361)
                      ·
                        rfl

theorem cell23_7161610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_7161610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161610 prefixEnd_7161610 := by exact prefixLift 7161610
  have htrace : WordTrace (prefixWord ++ tailWord_7161610) baseStart_7161610 baseEnd_7161610 := by
    simpa [prefixWord, tailWord_7161610, baseEnd_7161610] using wordTrace_append hprefix tailTrace_7161610
  have hstable : (prefixWord ++ tailWord_7161610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161610).length < 2 ^ (prefixWord ++ tailWord_7161610).sum := by decide
  have hdescent : baseEnd_7161610 < baseStart_7161610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161637 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 3, 3, 2]
def baseStart_7161637 : Nat := 118140960795 + 7161637 * 2 ^ 59
def prefixEnd_7161637 : Nat := 4983230072969 + 3 ^ 40 * 7161637 * 2
def baseEnd_7161637 : Nat := 3677362054023501796001737

theorem tailTrace_7161637 : CollatzResearch.WordTrace tailWord_7161637 prefixEnd_7161637 3677362054023501796001737 := by
  unfold tailWord_7161637
  simp only [CollatzResearch.WordTrace]
  refine ⟨261206360355619734067931165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174137573570413156045287443 261206360355619734067931165)
  ·
    refine ⟨97952385133357400275474187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261206360355619734067931165 97952385133357400275474187)
    ·
      refine ⟨146928577700036100413211281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97952385133357400275474187 146928577700036100413211281)
      ·
        refine ⟨110196433275027075309908461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146928577700036100413211281 110196433275027075309908461)
        ·
          refine ⟨41323662478135153241215673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110196433275027075309908461 41323662478135153241215673)
          ·
            refine ⟨30992746858601364930911755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41323662478135153241215673 30992746858601364930911755)
            ·
              refine ⟨46489120287902047396367633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30992746858601364930911755 46489120287902047396367633)
              ·
                refine ⟨34866840215926535547275725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46489120287902047396367633 34866840215926535547275725)
                ·
                  refine ⟨13075065080972450830228397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34866840215926535547275725 13075065080972450830228397)
                  ·
                    refine ⟨4903149405364669061335649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13075065080972450830228397 4903149405364669061335649)
                    ·
                      refine ⟨3677362054023501796001737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903149405364669061335649 3677362054023501796001737)
                      ·
                        rfl

theorem cell23_7161637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_7161637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161637 prefixEnd_7161637 := by exact prefixLift 7161637
  have htrace : WordTrace (prefixWord ++ tailWord_7161637) baseStart_7161637 baseEnd_7161637 := by
    simpa [prefixWord, tailWord_7161637, baseEnd_7161637] using wordTrace_append hprefix tailTrace_7161637
  have hstable : (prefixWord ++ tailWord_7161637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161637).length < 2 ^ (prefixWord ++ tailWord_7161637).sum := by decide
  have hdescent : baseEnd_7161637 < baseStart_7161637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161667 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 1, 4, 2]
def baseStart_7161667 : Nat := 118140960795 + 7161667 * 2 ^ 59
def prefixEnd_7161667 : Nat := 4983230072969 + 3 ^ 40 * 7161667 * 2
def baseEnd_7161667 : Nat := 3677377458443136678626599

theorem tailTrace_7161667 : CollatzResearch.WordTrace tailWord_7161667 prefixEnd_7161667 3677377458443136678626599 := by
  unfold tailWord_7161667
  simp only [CollatzResearch.WordTrace]
  refine ⟨261207454545511049191523255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174138303030340699461015503 261207454545511049191523255)
  ·
    refine ⟨391811181818266573787284883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261207454545511049191523255 391811181818266573787284883)
    ·
      refine ⟨587716772727399860680927325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391811181818266573787284883 587716772727399860680927325)
      ·
        refine ⟨220393789772774947755347747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587716772727399860680927325 220393789772774947755347747)
        ·
          refine ⟨330590684659162421633021621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220393789772774947755347747 330590684659162421633021621)
          ·
            refine ⟨30992876686796477028095777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 330590684659162421633021621 30992876686796477028095777)
            ·
              refine ⟨23244657515097357771071833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30992876686796477028095777 23244657515097357771071833)
              ·
                refine ⟨17433493136323018328303875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23244657515097357771071833 17433493136323018328303875)
                ·
                  refine ⟨26150239704484527492455813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17433493136323018328303875 26150239704484527492455813)
                  ·
                    refine ⟨4903169944590848904835465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26150239704484527492455813 4903169944590848904835465)
                    ·
                      refine ⟨3677377458443136678626599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903169944590848904835465 3677377458443136678626599)
                      ·
                        rfl

theorem cell23_7161667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_7161667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161667 prefixEnd_7161667 := by exact prefixLift 7161667
  have htrace : WordTrace (prefixWord ++ tailWord_7161667) baseStart_7161667 baseEnd_7161667 := by
    simpa [prefixWord, tailWord_7161667, baseEnd_7161667] using wordTrace_append hprefix tailTrace_7161667
  have hstable : (prefixWord ++ tailWord_7161667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161667).length < 2 ^ (prefixWord ++ tailWord_7161667).sum := by decide
  have hdescent : baseEnd_7161667 < baseStart_7161667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161673 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 9]
def baseStart_7161673 : Nat := 118140960795 + 7161673 * 2 ^ 59
def prefixEnd_7161673 : Nat := 4983230072969 + 3 ^ 40 * 7161673 * 2
def baseEnd_7161673 : Nat := 408597837703007072794619

theorem tailTrace_7161673 : CollatzResearch.WordTrace tailWord_7161673 prefixEnd_7161673 408597837703007072794619 := by
  unfold tailWord_7161673
  simp only [CollatzResearch.WordTrace]
  refine ⟨261207673383489312216241673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174138448922326208144161115 261207673383489312216241673)
  ·
    refine ⟨195905755037616984162181255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261207673383489312216241673 195905755037616984162181255)
    ·
      refine ⟨293858632556425476243271883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195905755037616984162181255 293858632556425476243271883)
      ·
        refine ⟨440787948834638214364907825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293858632556425476243271883 440787948834638214364907825)
        ·
          refine ⟨330590961625978660773680869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440787948834638214364907825 330590961625978660773680869)
          ·
            refine ⟨61985805304870998895065163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330590961625978660773680869 61985805304870998895065163)
            ·
              refine ⟨92978707957306498342597745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61985805304870998895065163 92978707957306498342597745)
              ·
                refine ⟨69734030967979873756948309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92978707957306498342597745 69734030967979873756948309)
                ·
                  refine ⟨408597837703007072794619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69734030967979873756948309 408597837703007072794619)
                  ·
                    rfl

theorem cell23_7161673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 9].length) (baseStart_7161673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161673 prefixEnd_7161673 := by exact prefixLift 7161673
  have htrace : WordTrace (prefixWord ++ tailWord_7161673) baseStart_7161673 baseEnd_7161673 := by
    simpa [prefixWord, tailWord_7161673, baseEnd_7161673] using wordTrace_append hprefix tailTrace_7161673
  have hstable : (prefixWord ++ tailWord_7161673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161673).length < 2 ^ (prefixWord ++ tailWord_7161673).sum := by decide
  have hdescent : baseEnd_7161673 < baseStart_7161673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161677 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_7161677 : Nat := 118140960795 + 7161677 * 2 ^ 59
def prefixEnd_7161677 : Nat := 4983230072969 + 3 ^ 40 * 7161677 * 2
def baseEnd_7161677 : Nat := 1225794197749893879833851

theorem tailTrace_7161677 : CollatzResearch.WordTrace tailWord_7161677 prefixEnd_7161677 1225794197749893879833851 := by
  unfold tailWord_7161677
  simp only [CollatzResearch.WordTrace]
  refine ⟨261207819275474820899387285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174138546183649880599591523 261207819275474820899387285)
  ·
    refine ⟨12244116528537882229658779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 261207819275474820899387285 12244116528537882229658779)
    ·
      refine ⟨18366174792806823344488169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12244116528537882229658779 18366174792806823344488169)
      ·
        refine ⟨13774631094605117508366127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18366174792806823344488169 13774631094605117508366127)
        ·
          refine ⟨20661946641907676262549191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13774631094605117508366127 20661946641907676262549191)
          ·
            refine ⟨30992919962861514393823787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20661946641907676262549191 30992919962861514393823787)
            ·
              refine ⟨46489379944292271590735681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30992919962861514393823787 46489379944292271590735681)
              ·
                refine ⟨34867034958219203693051761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46489379944292271590735681 34867034958219203693051761)
                ·
                  refine ⟨26150276218664402769788821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34867034958219203693051761 26150276218664402769788821)
                  ·
                    refine ⟨1225794197749893879833851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26150276218664402769788821 1225794197749893879833851)
                    ·
                      rfl

theorem cell23_7161677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_7161677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161677 prefixEnd_7161677 := by exact prefixLift 7161677
  have htrace : WordTrace (prefixWord ++ tailWord_7161677) baseStart_7161677 baseEnd_7161677 := by
    simpa [prefixWord, tailWord_7161677, baseEnd_7161677] using wordTrace_append hprefix tailTrace_7161677
  have hstable : (prefixWord ++ tailWord_7161677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161677).length < 2 ^ (prefixWord ++ tailWord_7161677).sum := by decide
  have hdescent : baseEnd_7161677 < baseStart_7161677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161690 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 7]
def baseStart_7161690 : Nat := 118140960795 + 7161690 * 2 ^ 59
def prefixEnd_7161690 : Nat := 4983230072969 + 3 ^ 40 * 7161690 * 2
def baseEnd_7161690 : Nat := 408598807610910009848777

theorem tailTrace_7161690 : CollatzResearch.WordTrace tailWord_7161690 prefixEnd_7161690 408598807610910009848777 := by
  unfold tailWord_7161690
  simp only [CollatzResearch.WordTrace]
  refine ⟨65302073356106931029902631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174138862282951816079740349 65302073356106931029902631)
  ·
    refine ⟨97953110034160396544853947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65302073356106931029902631 97953110034160396544853947)
    ·
      refine ⟨146929665051240594817280921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97953110034160396544853947 146929665051240594817280921)
      ·
        refine ⟨110197248788430446112960691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146929665051240594817280921 110197248788430446112960691)
        ·
          refine ⟨165295873182645669169441037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110197248788430446112960691 165295873182645669169441037)
          ·
            refine ⟨61985952443492125938540389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165295873182645669169441037 61985952443492125938540389)
            ·
              refine ⟨11622366083154773613476323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61985952443492125938540389 11622366083154773613476323)
              ·
                refine ⟨17433549124732160420214485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11622366083154773613476323 17433549124732160420214485)
                ·
                  refine ⟨408598807610910009848777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17433549124732160420214485 408598807610910009848777)
                  ·
                    rfl

theorem cell23_7161690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_7161690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161690 prefixEnd_7161690 := by exact prefixLift 7161690
  have htrace : WordTrace (prefixWord ++ tailWord_7161690) baseStart_7161690 baseEnd_7161690 := by
    simpa [prefixWord, tailWord_7161690, baseEnd_7161690] using wordTrace_append hprefix tailTrace_7161690
  have hstable : (prefixWord ++ tailWord_7161690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161690).length < 2 ^ (prefixWord ++ tailWord_7161690).sum := by decide
  have hdescent : baseEnd_7161690 < baseStart_7161690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161752 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7161752 : Nat := 118140960795 + 7161752 * 2 ^ 59
def prefixEnd_7161752 : Nat := 4983230072969 + 3 ^ 40 * 7161752 * 2
def baseEnd_7161752 : Nat := 3677421104298768846063709

theorem tailTrace_7161752 : CollatzResearch.WordTrace tailWord_7161752 prefixEnd_7161752 3677421104298768846063709 := by
  unfold tailWord_7161752
  simp only [CollatzResearch.WordTrace]
  refine ⟨130605277375101554354183755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174140369833468739138911673 130605277375101554354183755)
  ·
    refine ⟨195907916062652331531275633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130605277375101554354183755 195907916062652331531275633)
    ·
      refine ⟨146930937046989248648456725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195907916062652331531275633 146930937046989248648456725)
      ·
        refine ⟨6887387674077621030396409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146930937046989248648456725 6887387674077621030396409)
        ·
          refine ⟨5165540755558215772797307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6887387674077621030396409 5165540755558215772797307)
          ·
            refine ⟨7748311133337323659195961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165540755558215772797307 7748311133337323659195961)
            ·
              refine ⟨5811233350002992744396971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7748311133337323659195961 5811233350002992744396971)
              ·
                refine ⟨8716850025004489116595457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811233350002992744396971 8716850025004489116595457)
                ·
                  refine ⟨6537637518753366837446593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8716850025004489116595457 6537637518753366837446593)
                  ·
                    refine ⟨4903228139065025128084945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6537637518753366837446593 4903228139065025128084945)
                    ·
                      refine ⟨3677421104298768846063709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903228139065025128084945 3677421104298768846063709)
                      ·
                        rfl

theorem cell23_7161752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7161752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161752 prefixEnd_7161752 := by exact prefixLift 7161752
  have htrace : WordTrace (prefixWord ++ tailWord_7161752) baseStart_7161752 baseEnd_7161752 := by
    simpa [prefixWord, tailWord_7161752, baseEnd_7161752] using wordTrace_append hprefix tailTrace_7161752
  have hstable : (prefixWord ++ tailWord_7161752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161752).length < 2 ^ (prefixWord ++ tailWord_7161752).sum := by decide
  have hdescent : baseEnd_7161752 < baseStart_7161752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161784 : List Nat := [2, 1, 2, 1, 2, 3, 2, 5, 1, 4]
def baseStart_7161784 : Nat := 118140960795 + 7161784 * 2 ^ 59
def prefixEnd_7161784 : Nat := 4983230072969 + 3 ^ 40 * 7161784 * 2
def baseEnd_7161784 : Nat := 1225812511893237573621187

theorem tailTrace_7161784 : CollatzResearch.WordTrace tailWord_7161784 prefixEnd_7161784 1225812511893237573621187 := by
  unfold tailWord_7161784
  simp only [CollatzResearch.WordTrace]
  refine ⟨130605860943043589086766203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174141147924058118782354937 130605860943043589086766203)
  ·
    refine ⟨195908791414565383630149305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130605860943043589086766203 195908791414565383630149305)
    ·
      refine ⟨146931593560924037722611979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195908791414565383630149305 146931593560924037722611979)
      ·
        refine ⟨220397390341386056583917969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146931593560924037722611979 220397390341386056583917969)
        ·
          refine ⟨165298042756039542437938477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220397390341386056583917969 165298042756039542437938477)
          ·
            refine ⟨61986766033514828414226929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165298042756039542437938477 61986766033514828414226929)
            ·
              refine ⟨46490074525136121310670197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61986766033514828414226929 46490074525136121310670197)
              ·
                refine ⟨4358444486731511372875331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46490074525136121310670197 4358444486731511372875331)
                ·
                  refine ⟨6537666730097267059312997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358444486731511372875331 6537666730097267059312997)
                  ·
                    refine ⟨1225812511893237573621187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6537666730097267059312997 1225812511893237573621187)
                    ·
                      rfl

theorem cell23_7161784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_7161784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161784 prefixEnd_7161784 := by exact prefixLift 7161784
  have htrace : WordTrace (prefixWord ++ tailWord_7161784) baseStart_7161784 baseEnd_7161784 := by
    simpa [prefixWord, tailWord_7161784, baseEnd_7161784] using wordTrace_append hprefix tailTrace_7161784
  have hstable : (prefixWord ++ tailWord_7161784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161784).length < 2 ^ (prefixWord ++ tailWord_7161784).sum := by decide
  have hdescent : baseEnd_7161784 < baseStart_7161784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161827 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 3, 5]
def baseStart_7161827 : Nat := 118140960795 + 7161827 * 2 ^ 59
def prefixEnd_7161827 : Nat := 4983230072969 + 3 ^ 40 * 7161827 * 2
def baseEnd_7161827 : Nat := 1225819871782618684208621

theorem tailTrace_7161827 : CollatzResearch.WordTrace tailWord_7161827 prefixEnd_7161827 1225819871782618684208621 := by
  unfold tailWord_7161827
  simp only [CollatzResearch.WordTrace]
  refine ⟨261213290224931396517347735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174142193483287597678231823 261213290224931396517347735)
  ·
    refine ⟨391819935337397094776021603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261213290224931396517347735 391819935337397094776021603)
    ·
      refine ⟨587729903006095642164032405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391819935337397094776021603 587729903006095642164032405)
      ·
        refine ⟨27549839203410733226439019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 587729903006095642164032405 27549839203410733226439019)
        ·
          refine ⟨41324758805116099839658529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27549839203410733226439019 41324758805116099839658529)
          ·
            refine ⟨30993569103837074879743897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41324758805116099839658529 30993569103837074879743897)
            ·
              refine ⟨23245176827877806159807923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30993569103837074879743897 23245176827877806159807923)
              ·
                refine ⟨34867765241816709239711885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23245176827877806159807923 34867765241816709239711885)
                ·
                  refine ⟨13075411965681265964891957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34867765241816709239711885 13075411965681265964891957)
                  ·
                    refine ⟨1225819871782618684208621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13075411965681265964891957 1225819871782618684208621)
                    ·
                      rfl

theorem cell23_7161827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 5].length) (baseStart_7161827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161827 prefixEnd_7161827 := by exact prefixLift 7161827
  have htrace : WordTrace (prefixWord ++ tailWord_7161827) baseStart_7161827 baseEnd_7161827 := by
    simpa [prefixWord, tailWord_7161827, baseEnd_7161827] using wordTrace_append hprefix tailTrace_7161827
  have hstable : (prefixWord ++ tailWord_7161827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161827).length < 2 ^ (prefixWord ++ tailWord_7161827).sum := by decide
  have hdescent : baseEnd_7161827 < baseStart_7161827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161834 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_7161834 : Nat := 118140960795 + 7161834 * 2 ^ 59
def prefixEnd_7161834 : Nat := 4983230072969 + 3 ^ 40 * 7161834 * 2
def baseEnd_7161834 : Nat := 3677463209712437525238331

theorem tailTrace_7161834 : CollatzResearch.WordTrace tailWord_7161834 prefixEnd_7161834 3677463209712437525238331 := by
  unfold tailWord_7161834
  simp only [CollatzResearch.WordTrace]
  refine ⟨65303386383976509178213139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174142363690604024475235037 65303386383976509178213139)
  ·
    refine ⟨97955079575964763767319709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65303386383976509178213139 97955079575964763767319709)
    ·
      refine ⟨36733154840986786412744891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97955079575964763767319709 36733154840986786412744891)
      ·
        refine ⟨55099732261480179619117337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36733154840986786412744891 55099732261480179619117337)
        ·
          refine ⟨41324799196110134714338003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55099732261480179619117337 41324799196110134714338003)
          ·
            refine ⟨61987198794165202071507005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41324799196110134714338003 61987198794165202071507005)
            ·
              refine ⟨23245199547811950776815127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61987198794165202071507005 23245199547811950776815127)
              ·
                refine ⟨34867799321717926165222691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23245199547811950776815127 34867799321717926165222691)
                ·
                  refine ⟨52301698982576889247834037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34867799321717926165222691 52301698982576889247834037)
                  ·
                    refine ⟨4903284279616583366984441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52301698982576889247834037 4903284279616583366984441)
                    ·
                      refine ⟨3677463209712437525238331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903284279616583366984441 3677463209712437525238331)
                      ·
                        rfl

theorem cell23_7161834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_7161834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161834 prefixEnd_7161834 := by exact prefixLift 7161834
  have htrace : WordTrace (prefixWord ++ tailWord_7161834) baseStart_7161834 baseEnd_7161834 := by
    simpa [prefixWord, tailWord_7161834, baseEnd_7161834] using wordTrace_append hprefix tailTrace_7161834
  have hstable : (prefixWord ++ tailWord_7161834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161834).length < 2 ^ (prefixWord ++ tailWord_7161834).sum := by decide
  have hdescent : baseEnd_7161834 < baseStart_7161834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161847 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 3, 8, 2]
def baseStart_7161847 : Nat := 118140960795 + 7161847 * 2 ^ 59
def prefixEnd_7161847 : Nat := 4983230072969 + 3 ^ 40 * 7161847 * 2
def baseEnd_7161847 : Nat := 3677469884960945974375771

theorem tailTrace_7161847 : CollatzResearch.WordTrace tailWord_7161847 prefixEnd_7161847 3677469884960945974375771 := by
  unfold tailWord_7161847
  simp only [CollatzResearch.WordTrace]
  refine ⟨261214019684858939933075795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174142679789905959955383863 261214019684858939933075795)
  ·
    refine ⟨391821029527288409899613693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261214019684858939933075795 391821029527288409899613693)
    ·
      refine ⟨146932886072733153712355135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391821029527288409899613693 146932886072733153712355135)
      ·
        refine ⟨220399329109099730568532703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146932886072733153712355135 220399329109099730568532703)
        ·
          refine ⟨330598993663649595852799055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220399329109099730568532703 330598993663649595852799055)
          ·
            refine ⟨495898490495474393779198583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330598993663649595852799055 495898490495474393779198583)
            ·
              refine ⟨743847735743211590668797875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495898490495474393779198583 743847735743211590668797875)
              ·
                refine ⟨1115771603614817386003196813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743847735743211590668797875 1115771603614817386003196813)
                ·
                  refine ⟨418414351355556519751198805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115771603614817386003196813 418414351355556519751198805)
                  ·
                    refine ⟨4903293179947927965834361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 418414351355556519751198805 4903293179947927965834361)
                    ·
                      refine ⟨3677469884960945974375771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903293179947927965834361 3677469884960945974375771)
                      ·
                        rfl

theorem cell23_7161847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_7161847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161847 prefixEnd_7161847 := by exact prefixLift 7161847
  have htrace : WordTrace (prefixWord ++ tailWord_7161847) baseStart_7161847 baseEnd_7161847 := by
    simpa [prefixWord, tailWord_7161847, baseEnd_7161847] using wordTrace_append hprefix tailTrace_7161847
  have hstable : (prefixWord ++ tailWord_7161847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161847).length < 2 ^ (prefixWord ++ tailWord_7161847).sum := by decide
  have hdescent : baseEnd_7161847 < baseStart_7161847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161867 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 5]
def baseStart_7161867 : Nat := 118140960795 + 7161867 * 2 ^ 59
def prefixEnd_7161867 : Nat := 4983230072969 + 3 ^ 40 * 7161867 * 2
def baseEnd_7161867 : Nat := 3677480154574035896125679

theorem tailTrace_7161867 : CollatzResearch.WordTrace tailWord_7161867 prefixEnd_7161867 3677480154574035896125679 := by
  unfold tailWord_7161867
  simp only [CollatzResearch.WordTrace]
  refine ⟨261214749144786483348803855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174143166096524322232535903 261214749144786483348803855)
  ·
    refine ⟨391822123717179725023205783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261214749144786483348803855 391822123717179725023205783)
    ·
      refine ⟨587733185575769587534808675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391822123717179725023205783 587733185575769587534808675)
      ·
        refine ⟨881599778363654381302213013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587733185575769587534808675 881599778363654381302213013)
        ·
          refine ⟨41324989610796299123541235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 881599778363654381302213013 41324989610796299123541235)
          ·
            refine ⟨61987484416194448685311853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41324989610796299123541235 61987484416194448685311853)
            ·
              refine ⟨23245306656072918256991945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61987484416194448685311853 23245306656072918256991945)
              ·
                refine ⟨17433979992054688692743959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23245306656072918256991945 17433979992054688692743959)
                ·
                  refine ⟨26150969988082033039115939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17433979992054688692743959 26150969988082033039115939)
                  ·
                    refine ⟨39226454982123049558673909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26150969988082033039115939 39226454982123049558673909)
                    ·
                      refine ⟨3677480154574035896125679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39226454982123049558673909 3677480154574035896125679)
                      ·
                        rfl

theorem cell23_7161867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 5].length) (baseStart_7161867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161867 prefixEnd_7161867 := by exact prefixLift 7161867
  have htrace : WordTrace (prefixWord ++ tailWord_7161867) baseStart_7161867 baseEnd_7161867 := by
    simpa [prefixWord, tailWord_7161867, baseEnd_7161867] using wordTrace_append hprefix tailTrace_7161867
  have hstable : (prefixWord ++ tailWord_7161867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161867).length < 2 ^ (prefixWord ++ tailWord_7161867).sum := by decide
  have hdescent : baseEnd_7161867 < baseStart_7161867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161892 : List Nat := [2, 3, 1, 4, 3, 1, 1, 3, 1, 1, 3]
def baseStart_7161892 : Nat := 118140960795 + 7161892 * 2 ^ 59
def prefixEnd_7161892 : Nat := 4983230072969 + 3 ^ 40 * 7161892 * 2
def baseEnd_7161892 : Nat := 3677492991590398298313065

theorem tailTrace_7161892 : CollatzResearch.WordTrace tailWord_7161892 prefixEnd_7161892 3677492991590398298313065 := by
  unfold tailWord_7161892
  simp only [CollatzResearch.WordTrace]
  refine ⟨130607830484847956309231965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174143773979797275078975953 130607830484847956309231965)
  ·
    refine ⟨48977936431817983615961987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130607830484847956309231965 48977936431817983615961987)
    ·
      refine ⟨73466904647726975423942981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48977936431817983615961987 73466904647726975423942981)
      ·
        refine ⟨13775044621448807891989309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73466904647726975423942981 13775044621448807891989309)
        ·
          refine ⟨5165641733043302959495991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13775044621448807891989309 5165641733043302959495991)
          ·
            refine ⟨7748462599564954439243987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165641733043302959495991 7748462599564954439243987)
            ·
              refine ⟨11622693899347431658865981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748462599564954439243987 11622693899347431658865981)
              ·
                refine ⟨4358510212255286872074743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11622693899347431658865981 4358510212255286872074743)
                ·
                  refine ⟨6537765318382930308112115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358510212255286872074743 6537765318382930308112115)
                  ·
                    refine ⟨9806647977574395462168173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6537765318382930308112115 9806647977574395462168173)
                    ·
                      refine ⟨3677492991590398298313065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9806647977574395462168173 3677492991590398298313065)
                      ·
                        rfl

theorem cell23_7161892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_7161892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161892 prefixEnd_7161892 := by exact prefixLift 7161892
  have htrace : WordTrace (prefixWord ++ tailWord_7161892) baseStart_7161892 baseEnd_7161892 := by
    simpa [prefixWord, tailWord_7161892, baseEnd_7161892] using wordTrace_append hprefix tailTrace_7161892
  have hstable : (prefixWord ++ tailWord_7161892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161892).length < 2 ^ (prefixWord ++ tailWord_7161892).sum := by decide
  have hdescent : baseEnd_7161892 < baseStart_7161892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161917 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_7161917 : Nat := 118140960795 + 7161917 * 2 ^ 59
def prefixEnd_7161917 : Nat := 4983230072969 + 3 ^ 40 * 7161917 * 2
def baseEnd_7161917 : Nat := 1225835276202253566833483

theorem tailTrace_7161917 : CollatzResearch.WordTrace tailWord_7161917 prefixEnd_7161917 1225835276202253566833483 := by
  unfold tailWord_7161917
  simp only [CollatzResearch.WordTrace]
  refine ⟨261216572794605341888124005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174144381863070227925416003 261216572794605341888124005)
  ·
    refine ⟨48978107398988501604023251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261216572794605341888124005 48978107398988501604023251)
    ·
      refine ⟨73467161098482752406034877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48978107398988501604023251 73467161098482752406034877)
      ·
        refine ⟨27550185411931032152263079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73467161098482752406034877 27550185411931032152263079)
        ·
          refine ⟨41325278117896548228394619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27550185411931032152263079 41325278117896548228394619)
          ·
            refine ⟨61987917176844822342591929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41325278117896548228394619 61987917176844822342591929)
            ·
              refine ⟨46490937882633616756943947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61987917176844822342591929 46490937882633616756943947)
              ·
                refine ⟨69736406823950425135415921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46490937882633616756943947 69736406823950425135415921)
                ·
                  refine ⟨52302305117962818851561941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69736406823950425135415921 52302305117962818851561941)
                  ·
                    refine ⟨1225835276202253566833483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52302305117962818851561941 1225835276202253566833483)
                    ·
                      rfl

theorem cell23_7161917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_7161917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161917 prefixEnd_7161917 := by exact prefixLift 7161917
  have htrace : WordTrace (prefixWord ++ tailWord_7161917) baseStart_7161917 baseEnd_7161917 := by
    simpa [prefixWord, tailWord_7161917, baseEnd_7161917] using wordTrace_append hprefix tailTrace_7161917
  have hstable : (prefixWord ++ tailWord_7161917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161917).length < 2 ^ (prefixWord ++ tailWord_7161917).sum := by decide
  have hdescent : baseEnd_7161917 < baseStart_7161917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161941 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 3, 3, 2]
def baseStart_7161941 : Nat := 118140960795 + 7161941 * 2 ^ 59
def prefixEnd_7161941 : Nat := 4983230072969 + 3 ^ 40 * 7161941 * 2
def baseEnd_7161941 : Nat := 3677518152142468606600339

theorem tailTrace_7161941 : CollatzResearch.WordTrace tailWord_7161941 prefixEnd_7161941 3677518152142468606600339 := by
  unfold tailWord_7161941
  simp only [CollatzResearch.WordTrace]
  refine ⟨261217448146518393986997677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174144965431012262657998451 261217448146518393986997677)
  ·
    refine ⟨97956543054944397745124129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261217448146518393986997677 97956543054944397745124129)
    ·
      refine ⟨73467407291208298308843097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97956543054944397745124129 73467407291208298308843097)
      ·
        refine ⟨55100555468406223731632323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73467407291208298308843097 55100555468406223731632323)
        ·
          refine ⟨82650833202609335597448485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55100555468406223731632323 82650833202609335597448485)
          ·
            refine ⟨15497031225489250424521591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82650833202609335597448485 15497031225489250424521591)
            ·
              refine ⟨23245546838233875636782387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15497031225489250424521591 23245546838233875636782387)
              ·
                refine ⟨34868320257350813455173581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23245546838233875636782387 34868320257350813455173581)
                ·
                  refine ⟨13075620096506555045690093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34868320257350813455173581 13075620096506555045690093)
                  ·
                    refine ⟨4903357536189958142133785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13075620096506555045690093 4903357536189958142133785)
                    ·
                      refine ⟨3677518152142468606600339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903357536189958142133785 3677518152142468606600339)
                      ·
                        rfl

theorem cell23_7161941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_7161941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161941 prefixEnd_7161941 := by exact prefixLift 7161941
  have htrace : WordTrace (prefixWord ++ tailWord_7161941) baseStart_7161941 baseEnd_7161941 := by
    simpa [prefixWord, tailWord_7161941, baseEnd_7161941] using wordTrace_append hprefix tailTrace_7161941
  have hstable : (prefixWord ++ tailWord_7161941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161941).length < 2 ^ (prefixWord ++ tailWord_7161941).sum := by decide
  have hdescent : baseEnd_7161941 < baseStart_7161941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161988 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_7161988 : Nat := 118140960795 + 7161988 * 2 ^ 59
def prefixEnd_7161988 : Nat := 4983230072969 + 3 ^ 40 * 7161988 * 2
def baseEnd_7161988 : Nat := 3677542285733229922712623

theorem tailTrace_7161988 : CollatzResearch.WordTrace tailWord_7161988 prefixEnd_7161988 3677542285733229922712623 := by
  unfold tailWord_7161988
  simp only [CollatzResearch.WordTrace]
  refine ⟨130609581188674060506979309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174146108251565414009305745 130609581188674060506979309)
  ·
    refine ⟨48978592945752772690117241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130609581188674060506979309 48978592945752772690117241)
    ·
      refine ⟨36733944709314579517587931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48978592945752772690117241 36733944709314579517587931)
      ·
        refine ⟨55100917063971869276381897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36733944709314579517587931 55100917063971869276381897)
        ·
          refine ⟨41325687797978901957286423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55100917063971869276381897 41325687797978901957286423)
          ·
            refine ⟨61988531696968352935929635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41325687797978901957286423 61988531696968352935929635)
            ·
              refine ⟨92982797545452529403894453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61988531696968352935929635 92982797545452529403894453)
              ·
                refine ⟨8717137269886174631615105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92982797545452529403894453 8717137269886174631615105)
                ·
                  refine ⟨6537852952414630973711329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8717137269886174631615105 6537852952414630973711329)
                  ·
                    refine ⟨4903389714310973230283497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6537852952414630973711329 4903389714310973230283497)
                    ·
                      refine ⟨3677542285733229922712623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903389714310973230283497 3677542285733229922712623)
                      ·
                        rfl

theorem cell23_7161988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_7161988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161988 prefixEnd_7161988 := by exact prefixLift 7161988
  have htrace : WordTrace (prefixWord ++ tailWord_7161988) baseStart_7161988 baseEnd_7161988 := by
    simpa [prefixWord, tailWord_7161988, baseEnd_7161988] using wordTrace_append hprefix tailTrace_7161988
  have hstable : (prefixWord ++ tailWord_7161988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161988).length < 2 ^ (prefixWord ++ tailWord_7161988).sum := by decide
  have hdescent : baseEnd_7161988 < baseStart_7161988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7161994 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 7]
def baseStart_7161994 : Nat := 118140960795 + 7161994 * 2 ^ 59
def prefixEnd_7161994 : Nat := 4983230072969 + 3 ^ 40 * 7161994 * 2
def baseEnd_7161994 : Nat := 408616151846350766581955

theorem tailTrace_7161994 : CollatzResearch.WordTrace tailWord_7161994 prefixEnd_7161994 408616151846350766581955 := by
  unfold tailWord_7161994
  simp only [CollatzResearch.WordTrace]
  refine ⟨65304845303831596009669259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174146254143550922692451357 65304845303831596009669259)
  ·
    refine ⟨97957267955747394014503889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65304845303831596009669259 97957267955747394014503889)
    ·
      refine ⟨73467950966810545510877917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97957267955747394014503889 73467950966810545510877917)
      ·
        refine ⟨27550481612553954566579219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73467950966810545510877917 27550481612553954566579219)
        ·
          refine ⟨41325722418830931849868829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27550481612553954566579219 41325722418830931849868829)
          ·
            refine ⟨15497145907061599443700811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41325722418830931849868829 15497145907061599443700811)
            ·
              refine ⟨23245718860592399165551217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15497145907061599443700811 23245718860592399165551217)
              ·
                refine ⟨17434289145444299374163413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23245718860592399165551217 17434289145444299374163413)
                ·
                  refine ⟨408616151846350766581955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17434289145444299374163413 408616151846350766581955)
                  ·
                    rfl

theorem cell23_7161994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_7161994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7161994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7161994 prefixEnd_7161994 := by exact prefixLift 7161994
  have htrace : WordTrace (prefixWord ++ tailWord_7161994) baseStart_7161994 baseEnd_7161994 := by
    simpa [prefixWord, tailWord_7161994, baseEnd_7161994] using wordTrace_append hprefix tailTrace_7161994
  have hstable : (prefixWord ++ tailWord_7161994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7161994).length < 2 ^ (prefixWord ++ tailWord_7161994).sum := by decide
  have hdescent : baseEnd_7161994 < baseStart_7161994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7161994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162057 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_7162057 : Nat := 118140960795 + 7162057 * 2 ^ 59
def prefixEnd_7162057 : Nat := 4983230072969 + 3 ^ 40 * 7162057 * 2
def baseEnd_7162057 : Nat := 3677577715898390152749805

theorem tailTrace_7162057 : CollatzResearch.WordTrace tailWord_7162057 prefixEnd_7162057 3677577715898390152749805 := by
  unfold tailWord_7162057
  simp only [CollatzResearch.WordTrace]
  refine ⟨261221679014098145798220425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174147786009398763865480283 261221679014098145798220425)
  ·
    refine ⟨195916259260573609348665319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261221679014098145798220425 195916259260573609348665319)
    ·
      refine ⟨293874388890860414022997979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195916259260573609348665319 293874388890860414022997979)
      ·
        refine ⟨440811583336290621034496969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293874388890860414022997979 440811583336290621034496969)
        ·
          refine ⟨330608687502217965775872727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440811583336290621034496969 330608687502217965775872727)
          ·
            refine ⟨495913031253326948663809091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330608687502217965775872727 495913031253326948663809091)
            ·
              refine ⟨743869546879990422995713637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495913031253326948663809091 743869546879990422995713637)
              ·
                refine ⟨139475540039998204311696307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 743869546879990422995713637 139475540039998204311696307)
                ·
                  refine ⟨209213310059997306467544461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139475540039998204311696307 209213310059997306467544461)
                  ·
                    refine ⟨78454991272498989925329173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209213310059997306467544461 78454991272498989925329173)
                    ·
                      refine ⟨3677577715898390152749805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78454991272498989925329173 3677577715898390152749805)
                      ·
                        rfl

theorem cell23_7162057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_7162057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162057 prefixEnd_7162057 := by exact prefixLift 7162057
  have htrace : WordTrace (prefixWord ++ tailWord_7162057) baseStart_7162057 baseEnd_7162057 := by
    simpa [prefixWord, tailWord_7162057, baseEnd_7162057] using wordTrace_append hprefix tailTrace_7162057
  have hstable : (prefixWord ++ tailWord_7162057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162057).length < 2 ^ (prefixWord ++ tailWord_7162057).sum := by decide
  have hdescent : baseEnd_7162057 < baseStart_7162057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162064 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 3]
def baseStart_7162064 : Nat := 118140960795 + 7162064 * 2 ^ 59
def prefixEnd_7162064 : Nat := 4983230072969 + 3 ^ 40 * 7162064 * 2
def baseEnd_7162064 : Nat := 3677581310262971625362273

theorem tailTrace_7162064 : CollatzResearch.WordTrace tailWord_7162064 prefixEnd_7162064 3677581310262971625362273 := by
  unfold tailWord_7162064
  simp only [CollatzResearch.WordTrace]
  refine ⟨130610967162536392996862623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174147956216715190662483497 130610967162536392996862623)
  ·
    refine ⟨195916450743804589495293935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130610967162536392996862623 195916450743804589495293935)
    ·
      refine ⟨293874676115706884242940903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195916450743804589495293935 293874676115706884242940903)
      ·
        refine ⟨440812014173560326364411355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293874676115706884242940903 440812014173560326364411355)
        ·
          refine ⟨661218021260340489546617033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440812014173560326364411355 661218021260340489546617033)
          ·
            refine ⟨495913515945255367159962775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661218021260340489546617033 495913515945255367159962775)
            ·
              refine ⟨743870273917883050739944163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495913515945255367159962775 743870273917883050739944163)
              ·
                refine ⟨1115805410876824576109916245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743870273917883050739944163 1115805410876824576109916245)
                ·
                  refine ⟨13075844658712788001288081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1115805410876824576109916245 13075844658712788001288081)
                  ·
                    refine ⟨9806883494034591000966061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13075844658712788001288081 9806883494034591000966061)
                    ·
                      refine ⟨3677581310262971625362273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9806883494034591000966061 3677581310262971625362273)
                      ·
                        rfl

theorem cell23_7162064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 3].length) (baseStart_7162064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162064 prefixEnd_7162064 := by exact prefixLift 7162064
  have htrace : WordTrace (prefixWord ++ tailWord_7162064) baseStart_7162064 baseEnd_7162064 := by
    simpa [prefixWord, tailWord_7162064, baseEnd_7162064] using wordTrace_append hprefix tailTrace_7162064
  have hstable : (prefixWord ++ tailWord_7162064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162064).length < 2 ^ (prefixWord ++ tailWord_7162064).sum := by decide
  have hdescent : baseEnd_7162064 < baseStart_7162064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162081 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_7162081 : Nat := 118140960795 + 7162081 * 2 ^ 59
def prefixEnd_7162081 : Nat := 4983230072969 + 3 ^ 40 * 7162081 * 2
def baseEnd_7162081 : Nat := 3677590039434098058849695

theorem tailTrace_7162081 : CollatzResearch.WordTrace tailWord_7162081 prefixEnd_7162081 3677590039434098058849695 := by
  unfold tailWord_7162081
  simp only [CollatzResearch.WordTrace]
  refine ⟨261222554366011197897094097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174148369577340798598062731 261222554366011197897094097)
  ·
    refine ⟨195916915774508398422820573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261222554366011197897094097 195916915774508398422820573)
    ·
      refine ⟨73468843415440649408557715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195916915774508398422820573 73468843415440649408557715)
      ·
        refine ⟨110203265123160974112836573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73468843415440649408557715 110203265123160974112836573)
        ·
          refine ⟨41326224421185365292313715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110203265123160974112836573 41326224421185365292313715)
          ·
            refine ⟨61989336631778047938470573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41326224421185365292313715 61989336631778047938470573)
            ·
              refine ⟨23246001236916767976926465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61989336631778047938470573 23246001236916767976926465)
              ·
                refine ⟨17434500927687575982694849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23246001236916767976926465 17434500927687575982694849)
                ·
                  refine ⟨13075875695765681987021137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17434500927687575982694849 13075875695765681987021137)
                  ·
                    refine ⟨9806906771824261490265853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13075875695765681987021137 9806906771824261490265853)
                    ·
                      refine ⟨3677590039434098058849695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9806906771824261490265853 3677590039434098058849695)
                      ·
                        rfl

theorem cell23_7162081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_7162081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162081 prefixEnd_7162081 := by exact prefixLift 7162081
  have htrace : WordTrace (prefixWord ++ tailWord_7162081) baseStart_7162081 baseEnd_7162081 := by
    simpa [prefixWord, tailWord_7162081, baseEnd_7162081] using wordTrace_append hprefix tailTrace_7162081
  have hstable : (prefixWord ++ tailWord_7162081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162081).length < 2 ^ (prefixWord ++ tailWord_7162081).sum := by decide
  have hdescent : baseEnd_7162081 < baseStart_7162081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162084 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 6]
def baseStart_7162084 : Nat := 118140960795 + 7162084 * 2 ^ 59
def prefixEnd_7162084 : Nat := 4983230072969 + 3 ^ 40 * 7162084 * 2
def baseEnd_7162084 : Nat := 408621286652895727456909

theorem tailTrace_7162084 : CollatzResearch.WordTrace tailWord_7162084 prefixEnd_7162084 408621286652895727456909 := by
  unfold tailWord_7162084
  simp only [CollatzResearch.WordTrace]
  refine ⟨130611331892500164704726653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174148442523333552939635537 130611331892500164704726653)
  ·
    refine ⟨48979249459687561764272495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130611331892500164704726653 48979249459687561764272495)
    ·
      refine ⟨73468874189531342646408743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48979249459687561764272495 73468874189531342646408743)
      ·
        refine ⟨110203311284297013969613115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73468874189531342646408743 110203311284297013969613115)
        ·
          refine ⟨165304966926445520954419673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110203311284297013969613115 165304966926445520954419673)
          ·
            refine ⟨123978725194834140715814755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165304966926445520954419673 123978725194834140715814755)
            ·
              refine ⟨185968087792251211073722133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123978725194834140715814755 185968087792251211073722133)
              ·
                refine ⟨8717254115261775519080725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185968087792251211073722133 8717254115261775519080725)
                ·
                  refine ⟨408621286652895727456909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8717254115261775519080725 408621286652895727456909)
                  ·
                    rfl

theorem cell23_7162084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_7162084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162084 prefixEnd_7162084 := by exact prefixLift 7162084
  have htrace : WordTrace (prefixWord ++ tailWord_7162084) baseStart_7162084 baseEnd_7162084 := by
    simpa [prefixWord, tailWord_7162084, baseEnd_7162084] using wordTrace_append hprefix tailTrace_7162084
  have hstable : (prefixWord ++ tailWord_7162084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162084).length < 2 ^ (prefixWord ++ tailWord_7162084).sum := by decide
  have hdescent : baseEnd_7162084 < baseStart_7162084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162088 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 3, 4]
def baseStart_7162088 : Nat := 118140960795 + 7162088 * 2 ^ 59
def prefixEnd_7162088 : Nat := 4983230072969 + 3 ^ 40 * 7162088 * 2
def baseEnd_7162088 : Nat := 1225864544599559843820721

theorem tailTrace_7162088 : CollatzResearch.WordTrace tailWord_7162088 prefixEnd_7162088 1225864544599559843820721 := by
  unfold tailWord_7162088
  simp only [CollatzResearch.WordTrace]
  refine ⟨130611404838492919046299459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174148539784657225395065945 130611404838492919046299459)
  ·
    refine ⟨195917107257739378569449189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130611404838492919046299459 195917107257739378569449189)
    ·
      refine ⟨36734457610826133481771723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195917107257739378569449189 36734457610826133481771723)
      ·
        refine ⟨55101686416239200222657585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36734457610826133481771723 55101686416239200222657585)
        ·
          refine ⟨41326264812179400166993189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55101686416239200222657585 41326264812179400166993189)
          ·
            refine ⟨7748674652283637531311223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41326264812179400166993189 7748674652283637531311223)
            ·
              refine ⟨11623011978425456296966835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748674652283637531311223 11623011978425456296966835)
              ·
                refine ⟨17434517967638184445450253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11623011978425456296966835 17434517967638184445450253)
                ·
                  refine ⟨6537944237864319167043845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17434517967638184445450253 6537944237864319167043845)
                  ·
                    refine ⟨1225864544599559843820721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6537944237864319167043845 1225864544599559843820721)
                    ·
                      rfl

theorem cell23_7162088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_7162088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162088 prefixEnd_7162088 := by exact prefixLift 7162088
  have htrace : WordTrace (prefixWord ++ tailWord_7162088) baseStart_7162088 baseEnd_7162088 := by
    simpa [prefixWord, tailWord_7162088, baseEnd_7162088] using wordTrace_append hprefix tailTrace_7162088
  have hstable : (prefixWord ++ tailWord_7162088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162088).length < 2 ^ (prefixWord ++ tailWord_7162088).sum := by decide
  have hdescent : baseEnd_7162088 < baseStart_7162088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
