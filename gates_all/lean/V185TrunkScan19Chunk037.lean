import V185TrunkScan19Chunk036

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_371189 : List Nat := [1, 3, 5, 1, 3, 1, 5]
def baseStart_371189 : Nat := 118140960795 + 371189 * 2 ^ 59
def prefixEnd_371189 : Nat := 4983230072969 + 3 ^ 40 * 371189 * 2
def baseEnd_371189 : Nat := 37649060871477225685025

theorem tailTrace_371189 : CollatzResearch.WordTrace tailWord_371189 prefixEnd_371189 37649060871477225685025 := by
  unfold tailWord_371189
  simp only [CollatzResearch.WordTrace]
  refine ⟨13538375052253121879252621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9025583368168747919501747 13538375052253121879252621)
  ·
    refine ⟨5076890644594920704719733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13538375052253121879252621 5076890644594920704719733)
    ·
      refine ⟨475958497930773816067475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5076890644594920704719733 475958497930773816067475)
      ·
        refine ⟨713937746896160724101213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475958497930773816067475 713937746896160724101213)
        ·
          refine ⟨267726655086060271537955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 713937746896160724101213 267726655086060271537955)
          ·
            refine ⟨401589982629090407306933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267726655086060271537955 401589982629090407306933)
            ·
              refine ⟨37649060871477225685025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 401589982629090407306933 37649060871477225685025)
              ·
                rfl

theorem cell19_371189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 5].length) (baseStart_371189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371189 prefixEnd_371189 := by exact prefixLift 371189
  have htrace : WordTrace (prefixWord ++ tailWord_371189) baseStart_371189 baseEnd_371189 := by
    simpa [prefixWord, tailWord_371189, baseEnd_371189] using wordTrace_append hprefix tailTrace_371189
  have hstable : (prefixWord ++ tailWord_371189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371189).length < 2 ^ (prefixWord ++ tailWord_371189).sum := by decide
  have hdescent : baseEnd_371189 < baseStart_371189 := by decide
  rcases family_descends (prefixWord ++ tailWord_371189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371206 : List Nat := [6, 2, 1, 1, 1, 2, 2, 4]
def baseStart_371206 : Nat := 118140960795 + 371206 * 2 ^ 59
def prefixEnd_371206 : Nat := 4983230072969 + 3 ^ 40 * 371206 * 2
def baseEnd_371206 : Nat := 112952355456580674677251

theorem tailTrace_371206 : CollatzResearch.WordTrace tailWord_371206 prefixEnd_371206 112952355456580674677251 := by
  unfold tailWord_371206
  simp only [CollatzResearch.WordTrace]
  refine ⟨423093596662235430706921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9025996728794355855080981 423093596662235430706921)
  ·
    refine ⟨317320197496676573030191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 423093596662235430706921 317320197496676573030191)
    ·
      refine ⟨475980296245014859545287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317320197496676573030191 475980296245014859545287)
      ·
        refine ⟨713970444367522289317931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475980296245014859545287 713970444367522289317931)
        ·
          refine ⟨1070955666551283433976897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713970444367522289317931 1070955666551283433976897)
          ·
            refine ⟨803216749913462575482673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070955666551283433976897 803216749913462575482673)
            ·
              refine ⟨602412562435096931612005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803216749913462575482673 602412562435096931612005)
              ·
                refine ⟨112952355456580674677251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 602412562435096931612005 112952355456580674677251)
                ·
                  rfl

theorem cell19_371206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_371206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371206 prefixEnd_371206 := by exact prefixLift 371206
  have htrace : WordTrace (prefixWord ++ tailWord_371206) baseStart_371206 baseEnd_371206 := by
    simpa [prefixWord, tailWord_371206, baseEnd_371206] using wordTrace_append hprefix tailTrace_371206
  have hstable : (prefixWord ++ tailWord_371206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371206).length < 2 ^ (prefixWord ++ tailWord_371206).sum := by decide
  have hdescent : baseEnd_371206 < baseStart_371206 := by decide
  rcases family_descends (prefixWord ++ tailWord_371206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371212 : List Nat := [2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_371212 : Nat := 118140960795 + 371212 * 2 ^ 59
def prefixEnd_371212 : Nat := 4983230072969 + 3 ^ 40 * 371212 * 2
def baseEnd_371212 : Nat := 112954181165574438543901

theorem tailTrace_371212 : CollatzResearch.WordTrace tailWord_371212 prefixEnd_371212 112954181165574438543901 := by
  unfold tailWord_371212
  simp only [CollatzResearch.WordTrace]
  refine ⟨6769606965584898403669945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9026142620779864538226593 6769606965584898403669945)
  ·
    refine ⟨5077205224188673802752459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6769606965584898403669945 5077205224188673802752459)
    ·
      refine ⟨7615807836283010704128689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5077205224188673802752459 7615807836283010704128689)
      ·
        refine ⟨5711855877212258028096517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7615807836283010704128689 5711855877212258028096517)
        ·
          refine ⟨1070972976977298380268097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5711855877212258028096517 1070972976977298380268097)
          ·
            refine ⟨803229732732973785201073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070972976977298380268097 803229732732973785201073)
            ·
              refine ⟨602422299549730338900805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803229732732973785201073 602422299549730338900805)
              ·
                refine ⟨112954181165574438543901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 602422299549730338900805 112954181165574438543901)
                ·
                  rfl

theorem cell19_371212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_371212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371212 prefixEnd_371212 := by exact prefixLift 371212
  have htrace : WordTrace (prefixWord ++ tailWord_371212) baseStart_371212 baseEnd_371212 := by
    simpa [prefixWord, tailWord_371212, baseEnd_371212] using wordTrace_append hprefix tailTrace_371212
  have hstable : (prefixWord ++ tailWord_371212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371212).length < 2 ^ (prefixWord ++ tailWord_371212).sum := by decide
  have hdescent : baseEnd_371212 < baseStart_371212 := by decide
  rcases family_descends (prefixWord ++ tailWord_371212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371233 : List Nat := [1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_371233 : Nat := 118140960795 + 371233 * 2 ^ 59
def prefixEnd_371233 : Nat := 4983230072969 + 3 ^ 40 * 371233 * 2
def baseEnd_371233 : Nat := 112960571147052612077177

theorem tailTrace_371233 : CollatzResearch.WordTrace tailWord_371233 prefixEnd_371233 112960571147052612077177 := by
  unfold tailWord_371233
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539979864093717393854353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9026653242729144929236235 13539979864093717393854353)
  ·
    refine ⟨10154984898070288045390765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13539979864093717393854353 10154984898070288045390765)
    ·
      refine ⟨3808119336776358017021537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10154984898070288045390765 3808119336776358017021537)
      ·
        refine ⟨2856089502582268512766153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3808119336776358017021537 2856089502582268512766153)
        ·
          refine ⟨2142067126936701384574615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2856089502582268512766153 2142067126936701384574615)
          ·
            refine ⟨3213100690405052076861923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142067126936701384574615 3213100690405052076861923)
            ·
              refine ⟨4819651035607578115292885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213100690405052076861923 4819651035607578115292885)
              ·
                refine ⟨112960571147052612077177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4819651035607578115292885 112960571147052612077177)
                ·
                  rfl

theorem cell19_371233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_371233 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371233 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371233 prefixEnd_371233 := by exact prefixLift 371233
  have htrace : WordTrace (prefixWord ++ tailWord_371233) baseStart_371233 baseEnd_371233 := by
    simpa [prefixWord, tailWord_371233, baseEnd_371233] using wordTrace_append hprefix tailTrace_371233
  have hstable : (prefixWord ++ tailWord_371233).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371233).length < 2 ^ (prefixWord ++ tailWord_371233).sum := by decide
  have hdescent : baseEnd_371233 < baseStart_371233 := by decide
  rcases family_descends (prefixWord ++ tailWord_371233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371269 : List Nat := [1, 3, 1, 1, 1, 7, 1, 4]
def baseStart_371269 : Nat := 118140960795 + 371269 * 2 ^ 59
def prefixEnd_371269 : Nat := 4983230072969 + 3 ^ 40 * 371269 * 2
def baseEnd_371269 : Nat := 112971525401015195277079

theorem tailTrace_371269 : CollatzResearch.WordTrace tailWord_371269 prefixEnd_371269 112971525401015195277079 := by
  unfold tailWord_371269
  simp only [CollatzResearch.WordTrace]
  refine ⟨13541292891963295542164861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9027528594642197028109907 13541292891963295542164861)
  ·
    refine ⟨5077984834486235828311823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13541292891963295542164861 5077984834486235828311823)
    ·
      refine ⟨7616977251729353742467735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5077984834486235828311823 7616977251729353742467735)
      ·
        refine ⟨11425465877594030613701603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7616977251729353742467735 11425465877594030613701603)
        ·
          refine ⟨17138198816391045920552405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11425465877594030613701603 17138198816391045920552405)
          ·
            refine ⟨401676534759165138762947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17138198816391045920552405 401676534759165138762947)
            ·
              refine ⟨602514802138747708144421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401676534759165138762947 602514802138747708144421)
              ·
                refine ⟨112971525401015195277079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 602514802138747708144421 112971525401015195277079)
                ·
                  rfl

theorem cell19_371269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_371269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371269 prefixEnd_371269 := by exact prefixLift 371269
  have htrace : WordTrace (prefixWord ++ tailWord_371269) baseStart_371269 baseEnd_371269 := by
    simpa [prefixWord, tailWord_371269, baseEnd_371269] using wordTrace_append hprefix tailTrace_371269
  have hstable : (prefixWord ++ tailWord_371269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371269).length < 2 ^ (prefixWord ++ tailWord_371269).sum := by decide
  have hdescent : baseEnd_371269 < baseStart_371269 := by decide
  rcases family_descends (prefixWord ++ tailWord_371269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371383 : List Nat := [1, 1, 3, 1, 6, 1, 2, 4]
def baseStart_371383 : Nat := 118140960795 + 371383 * 2 ^ 59
def prefixEnd_371383 : Nat := 4983230072969 + 3 ^ 40 * 371383 * 2
def baseEnd_371383 : Nat := 113006213871896708743435

theorem tailTrace_371383 : CollatzResearch.WordTrace tailWord_371383 prefixEnd_371383 113006213871896708743435 := by
  unfold tailWord_371383
  simp only [CollatzResearch.WordTrace]
  refine ⟨13545450813550293011814803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9030300542366862007876535 13545450813550293011814803)
  ·
    refine ⟨20318176220325439517722205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13545450813550293011814803 20318176220325439517722205)
    ·
      refine ⟨7619316082622039819145827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20318176220325439517722205 7619316082622039819145827)
      ·
        refine ⟨11428974123933059728718741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7619316082622039819145827 11428974123933059728718741)
        ·
          refine ⟨535733162059362174783691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11428974123933059728718741 535733162059362174783691)
          ·
            refine ⟨803599743089043262175537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535733162059362174783691 803599743089043262175537)
            ·
              refine ⟨602699807316782446631653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803599743089043262175537 602699807316782446631653)
              ·
                refine ⟨113006213871896708743435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 602699807316782446631653 113006213871896708743435)
                ·
                  rfl

theorem cell19_371383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_371383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371383 prefixEnd_371383 := by exact prefixLift 371383
  have htrace : WordTrace (prefixWord ++ tailWord_371383) baseStart_371383 baseEnd_371383 := by
    simpa [prefixWord, tailWord_371383, baseEnd_371383] using wordTrace_append hprefix tailTrace_371383
  have hstable : (prefixWord ++ tailWord_371383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371383).length < 2 ^ (prefixWord ++ tailWord_371383).sum := by decide
  have hdescent : baseEnd_371383 < baseStart_371383 := by decide
  rcases family_descends (prefixWord ++ tailWord_371383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371510 : List Nat := [5, 1, 2, 2, 3, 1, 2, 3]
def baseStart_371510 : Nat := 118140960795 + 371510 * 2 ^ 59
def prefixEnd_371510 : Nat := 4983230072969 + 3 ^ 40 * 371510 * 2
def baseEnd_371510 : Nat := 113044858045598043920867

theorem tailTrace_371510 : CollatzResearch.WordTrace tailWord_371510 prefixEnd_371510 113044858045598043920867 := by
  unfold tailWord_371510
  simp only [CollatzResearch.WordTrace]
  refine ⟨846880180255637106355499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9033388589393462467791989 846880180255637106355499)
  ·
    refine ⟨1270320270383455659533249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 846880180255637106355499 1270320270383455659533249)
    ·
      refine ⟨952740202787591744649937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1270320270383455659533249 952740202787591744649937)
      ·
        refine ⟨714555152090693808487453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 952740202787591744649937 714555152090693808487453)
        ·
          refine ⟨267958182034010178182795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 714555152090693808487453 267958182034010178182795)
          ·
            refine ⟨401937273051015267274193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267958182034010178182795 401937273051015267274193)
            ·
              refine ⟨301452954788261450455645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401937273051015267274193 301452954788261450455645)
              ·
                refine ⟨113044858045598043920867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301452954788261450455645 113044858045598043920867)
                ·
                  rfl

theorem cell19_371510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_371510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371510 prefixEnd_371510 := by exact prefixLift 371510
  have htrace : WordTrace (prefixWord ++ tailWord_371510) baseStart_371510 baseEnd_371510 := by
    simpa [prefixWord, tailWord_371510, baseEnd_371510] using wordTrace_append hprefix tailTrace_371510
  have hstable : (prefixWord ++ tailWord_371510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371510).length < 2 ^ (prefixWord ++ tailWord_371510).sum := by decide
  have hdescent : baseEnd_371510 < baseStart_371510 := by decide
  rcases family_descends (prefixWord ++ tailWord_371510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371514 : List Nat := [3, 1, 1, 1, 6, 2, 2, 3]
def baseStart_371514 : Nat := 118140960795 + 371514 * 2 ^ 59
def prefixEnd_371514 : Nat := 4983230072969 + 3 ^ 40 * 371514 * 2
def baseEnd_371514 : Nat := 113046075184927219831967

theorem tailTrace_371514 : CollatzResearch.WordTrace tailWord_371514 prefixEnd_371514 113046075184927219831967 := by
  unfold tailWord_371514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3387557194018925596208399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9033485850717134923222397 3387557194018925596208399)
  ·
    refine ⟨5081335791028388394312599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3387557194018925596208399 5081335791028388394312599)
    ·
      refine ⟨7622003686542582591468899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5081335791028388394312599 7622003686542582591468899)
      ·
        refine ⟨11433005529813873887203349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7622003686542582591468899 11433005529813873887203349)
        ·
          refine ⟨535922134210025338462657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11433005529813873887203349 535922134210025338462657)
          ·
            refine ⟨401941600657519003846993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535922134210025338462657 401941600657519003846993)
            ·
              refine ⟨301456200493139252885245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401941600657519003846993 301456200493139252885245)
              ·
                refine ⟨113046075184927219831967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301456200493139252885245 113046075184927219831967)
                ·
                  rfl

theorem cell19_371514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_371514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371514 prefixEnd_371514 := by exact prefixLift 371514
  have htrace : WordTrace (prefixWord ++ tailWord_371514) baseStart_371514 baseEnd_371514 := by
    simpa [prefixWord, tailWord_371514, baseEnd_371514] using wordTrace_append hprefix tailTrace_371514
  have hstable : (prefixWord ++ tailWord_371514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371514).length < 2 ^ (prefixWord ++ tailWord_371514).sum := by decide
  have hdescent : baseEnd_371514 < baseStart_371514 := by decide
  rcases family_descends (prefixWord ++ tailWord_371514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371533 : List Nat := [1, 6, 1, 2, 2, 2, 5]
def baseStart_371533 : Nat := 118140960795 + 371533 * 2 ^ 59
def prefixEnd_371533 : Nat := 4983230072969 + 3 ^ 40 * 371533 * 2
def baseEnd_371533 : Nat := 37683952198913601803231

theorem tailTrace_371533 : CollatzResearch.WordTrace tailWord_371533 prefixEnd_371533 37683952198913601803231 := by
  unfold tailWord_371533
  simp only [CollatzResearch.WordTrace]
  refine ⟨13550921763006868629775253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9033947842004579086516835 13550921763006868629775253)
  ·
    refine ⟨635199457640946967020715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13550921763006868629775253 635199457640946967020715)
    ·
      refine ⟨952799186461420450531073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635199457640946967020715 952799186461420450531073)
      ·
        refine ⟨714599389846065337898305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 952799186461420450531073 714599389846065337898305)
        ·
          refine ⟨535949542384549003423729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 714599389846065337898305 535949542384549003423729)
          ·
            refine ⟨401962156788411752567797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535949542384549003423729 401962156788411752567797)
            ·
              refine ⟨37683952198913601803231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 401962156788411752567797 37683952198913601803231)
              ·
                rfl

theorem cell19_371533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_371533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371533 prefixEnd_371533 := by exact prefixLift 371533
  have htrace : WordTrace (prefixWord ++ tailWord_371533) baseStart_371533 baseEnd_371533 := by
    simpa [prefixWord, tailWord_371533, baseEnd_371533] using wordTrace_append hprefix tailTrace_371533
  have hstable : (prefixWord ++ tailWord_371533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371533).length < 2 ^ (prefixWord ++ tailWord_371533).sum := by decide
  have hdescent : baseEnd_371533 < baseStart_371533 := by decide
  rcases family_descends (prefixWord ++ tailWord_371533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371556 : List Nat := [2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_371556 : Nat := 118140960795 + 371556 * 2 ^ 59
def prefixEnd_371556 : Nat := 4983230072969 + 3 ^ 40 * 371556 * 2
def baseEnd_371556 : Nat := 113058855147883566898519

theorem tailTrace_371556 : CollatzResearch.WordTrace tailWord_371556 prefixEnd_371556 113058855147883566898519 := by
  unfold tailWord_371556
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775880320961771778931261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9034507094615695705241681 6775880320961771778931261)
  ·
    refine ⟨2540955120360664417099223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6775880320961771778931261 2540955120360664417099223)
    ·
      refine ⟨3811432680540996625648835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2540955120360664417099223 3811432680540996625648835)
      ·
        refine ⟨5717149020811494938473253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3811432680540996625648835 5717149020811494938473253)
        ·
          refine ⟨1071965441402155300963735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5717149020811494938473253 1071965441402155300963735)
          ·
            refine ⟨1607948162103232951445603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071965441402155300963735 1607948162103232951445603)
            ·
              refine ⟨2411922243154849427168405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607948162103232951445603 2411922243154849427168405)
              ·
                refine ⟨113058855147883566898519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2411922243154849427168405 113058855147883566898519)
                ·
                  rfl

theorem cell19_371556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_371556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371556 prefixEnd_371556 := by exact prefixLift 371556
  have htrace : WordTrace (prefixWord ++ tailWord_371556) baseStart_371556 baseEnd_371556 := by
    simpa [prefixWord, tailWord_371556, baseEnd_371556] using wordTrace_append hprefix tailTrace_371556
  have hstable : (prefixWord ++ tailWord_371556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371556).length < 2 ^ (prefixWord ++ tailWord_371556).sum := by decide
  have hdescent : baseEnd_371556 < baseStart_371556 := by decide
  rcases family_descends (prefixWord ++ tailWord_371556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371594 : List Nat := [3, 1, 2, 4, 1, 8]
def baseStart_371594 : Nat := 118140960795 + 371594 * 2 ^ 59
def prefixEnd_371594 : Nat := 4983230072969 + 3 ^ 40 * 371594 * 2
def baseEnd_371594 : Nat := 12563379774612304228219

theorem tailTrace_371594 : CollatzResearch.WordTrace tailWord_371594 prefixEnd_371594 12563379774612304228219 := by
  unfold tailWord_371594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3388286653946469011936459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9035431077190584031830557 3388286653946469011936459)
  ·
    refine ⟨5082429980919703517904689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3388286653946469011936459 5082429980919703517904689)
    ·
      refine ⟨3811822485689777638428517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5082429980919703517904689 3811822485689777638428517)
      ·
        refine ⟨714716716066833307205347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3811822485689777638428517 714716716066833307205347)
        ·
          refine ⟨1072075074100249960808021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714716716066833307205347 1072075074100249960808021)
          ·
            refine ⟨12563379774612304228219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1072075074100249960808021 12563379774612304228219)
            ·
              rfl

theorem cell19_371594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 8].length) (baseStart_371594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371594 prefixEnd_371594 := by exact prefixLift 371594
  have htrace : WordTrace (prefixWord ++ tailWord_371594) baseStart_371594 baseEnd_371594 := by
    simpa [prefixWord, tailWord_371594, baseEnd_371594] using wordTrace_append hprefix tailTrace_371594
  have hstable : (prefixWord ++ tailWord_371594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371594).length < 2 ^ (prefixWord ++ tailWord_371594).sum := by decide
  have hdescent : baseEnd_371594 < baseStart_371594 := by decide
  rcases family_descends (prefixWord ++ tailWord_371594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371687 : List Nat := [1, 1, 5, 2, 2, 1, 4, 3]
def baseStart_371687 : Nat := 118140960795 + 371687 * 2 ^ 59
def prefixEnd_371687 : Nat := 4983230072969 + 3 ^ 40 * 371687 * 2
def baseEnd_371687 : Nat := 113098716460914077987051

theorem tailTrace_371687 : CollatzResearch.WordTrace tailWord_371687 prefixEnd_371687 113098716460914077987051 := by
  unfold tailWord_371687
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556538604448952930881315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9037692402965968620587543 13556538604448952930881315)
  ·
    refine ⟨20334807906673429396321973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13556538604448952930881315 20334807906673429396321973)
    ·
      refine ⟨1906388241250634005905185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20334807906673429396321973 1906388241250634005905185)
      ·
        refine ⟨1429791180937975504428889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1906388241250634005905185 1429791180937975504428889)
        ·
          refine ⟨1072343385703481628321667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1429791180937975504428889 1072343385703481628321667)
          ·
            refine ⟨1608515078555222442482501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072343385703481628321667 1608515078555222442482501)
            ·
              refine ⟨301596577229104207965469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1608515078555222442482501 301596577229104207965469)
              ·
                refine ⟨113098716460914077987051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301596577229104207965469 113098716460914077987051)
                ·
                  rfl

theorem cell19_371687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 3].length) (baseStart_371687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371687 prefixEnd_371687 := by exact prefixLift 371687
  have htrace : WordTrace (prefixWord ++ tailWord_371687) baseStart_371687 baseEnd_371687 := by
    simpa [prefixWord, tailWord_371687, baseEnd_371687] using wordTrace_append hprefix tailTrace_371687
  have hstable : (prefixWord ++ tailWord_371687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371687).length < 2 ^ (prefixWord ++ tailWord_371687).sum := by decide
  have hdescent : baseEnd_371687 < baseStart_371687 := by decide
  rcases family_descends (prefixWord ++ tailWord_371687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371700 : List Nat := [2, 6, 2, 1, 1, 2, 5]
def baseStart_371700 : Nat := 118140960795 + 371700 * 2 ^ 59
def prefixEnd_371700 : Nat := 4983230072969 + 3 ^ 40 * 371700 * 2
def baseEnd_371700 : Nat := 37700890721244633232709

theorem tailTrace_371700 : CollatzResearch.WordTrace tailWord_371700 prefixEnd_371700 37700890721244633232709 := by
  unfold tailWord_371700
  simp only [CollatzResearch.WordTrace]
  refine ⟨6778506376700928075552277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9038008502267904100736369 6778506376700928075552277)
  ·
    refine ⟨317742486407856003541513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6778506376700928075552277 317742486407856003541513)
    ·
      refine ⟨238306864805892002656135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317742486407856003541513 238306864805892002656135)
      ·
        refine ⟨357460297208838003984203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238306864805892002656135 357460297208838003984203)
        ·
          refine ⟨536190445813257005976305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357460297208838003984203 536190445813257005976305)
          ·
            refine ⟨402142834359942754482229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536190445813257005976305 402142834359942754482229)
            ·
              refine ⟨37700890721244633232709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 402142834359942754482229 37700890721244633232709)
              ·
                rfl

theorem cell19_371700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 5].length) (baseStart_371700 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371700 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371700 prefixEnd_371700 := by exact prefixLift 371700
  have htrace : WordTrace (prefixWord ++ tailWord_371700) baseStart_371700 baseEnd_371700 := by
    simpa [prefixWord, tailWord_371700, baseEnd_371700] using wordTrace_append hprefix tailTrace_371700
  have hstable : (prefixWord ++ tailWord_371700).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371700).length < 2 ^ (prefixWord ++ tailWord_371700).sum := by decide
  have hdescent : baseEnd_371700 < baseStart_371700 := by decide
  rcases family_descends (prefixWord ++ tailWord_371700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371708 : List Nat := [2, 2, 2, 1, 2, 5, 5]
def baseStart_371708 : Nat := 118140960795 + 371708 * 2 ^ 59
def prefixEnd_371708 : Nat := 4983230072969 + 3 ^ 40 * 371708 * 2
def baseEnd_371708 : Nat := 37701702147464083840109

theorem tailTrace_371708 : CollatzResearch.WordTrace tailWord_371708 prefixEnd_371708 37701702147464083840109 := by
  unfold tailWord_371708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6778652268686436758697889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9038203024915249011597185 6778652268686436758697889)
  ·
    refine ⟨5083989201514827569023417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6778652268686436758697889 5083989201514827569023417)
    ·
      refine ⟨3812991901136120676767563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5083989201514827569023417 3812991901136120676767563)
      ·
        refine ⟨5719487851704181015151345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812991901136120676767563 5719487851704181015151345)
        ·
          refine ⟨4289615888778135761363509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5719487851704181015151345 4289615888778135761363509)
          ·
            refine ⟨402151489572950227627829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4289615888778135761363509 402151489572950227627829)
            ·
              refine ⟨37701702147464083840109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 402151489572950227627829 37701702147464083840109)
              ·
                rfl

theorem cell19_371708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_371708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371708 prefixEnd_371708 := by exact prefixLift 371708
  have htrace : WordTrace (prefixWord ++ tailWord_371708) baseStart_371708 baseEnd_371708 := by
    simpa [prefixWord, tailWord_371708, baseEnd_371708] using wordTrace_append hprefix tailTrace_371708
  have hstable : (prefixWord ++ tailWord_371708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371708).length < 2 ^ (prefixWord ++ tailWord_371708).sum := by decide
  have hdescent : baseEnd_371708 < baseStart_371708 := by decide
  rcases family_descends (prefixWord ++ tailWord_371708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371746 : List Nat := [3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_371746 : Nat := 118140960795 + 371746 * 2 ^ 59
def prefixEnd_371746 : Nat := 4983230072969 + 3 ^ 40 * 371746 * 2
def baseEnd_371746 : Nat := 113116669266019422675779

theorem tailTrace_371746 : CollatzResearch.WordTrace tailWord_371746 prefixEnd_371746 113116669266019422675779 := by
  unfold tailWord_371746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389672627808801501819773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9039127007490137338186061 3389672627808801501819773)
  ·
    refine ⟨1271127235428300563182415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3389672627808801501819773 1271127235428300563182415)
    ·
      refine ⟨1906690853142450844773623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1271127235428300563182415 1906690853142450844773623)
      ·
        refine ⟨2860036279713676267160435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906690853142450844773623 2860036279713676267160435)
        ·
          refine ⟨4290054419570514400740653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860036279713676267160435 4290054419570514400740653)
          ·
            refine ⟨1608770407338942900277745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4290054419570514400740653 1608770407338942900277745)
            ·
              refine ⟨1206577805504207175208309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608770407338942900277745 1206577805504207175208309)
              ·
                refine ⟨113116669266019422675779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1206577805504207175208309 113116669266019422675779)
                ·
                  rfl

theorem cell19_371746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_371746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371746 prefixEnd_371746 := by exact prefixLift 371746
  have htrace : WordTrace (prefixWord ++ tailWord_371746) baseStart_371746 baseEnd_371746 := by
    simpa [prefixWord, tailWord_371746, baseEnd_371746] using wordTrace_append hprefix tailTrace_371746
  have hstable : (prefixWord ++ tailWord_371746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371746).length < 2 ^ (prefixWord ++ tailWord_371746).sum := by decide
  have hdescent : baseEnd_371746 < baseStart_371746 := by decide
  rcases family_descends (prefixWord ++ tailWord_371746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371822 : List Nat := [4, 1, 2, 2, 1, 3, 6]
def baseStart_371822 : Nat := 118140960795 + 371822 * 2 ^ 59
def prefixEnd_371822 : Nat := 4983230072969 + 3 ^ 40 * 371822 * 2
def baseEnd_371822 : Nat := 37713264971091254995561

theorem tailTrace_371822 : CollatzResearch.WordTrace tailWord_371822 prefixEnd_371822 37713264971091254995561 := by
  unfold tailWord_371822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695182807369983873380715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9040974972639913991363813 1695182807369983873380715)
  ·
    refine ⟨2542774211054975810071073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1695182807369983873380715 2542774211054975810071073)
    ·
      refine ⟨1907080658291231857553305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2542774211054975810071073 1907080658291231857553305)
      ·
        refine ⟨1430310493718423893164979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1907080658291231857553305 1430310493718423893164979)
        ·
          refine ⟨2145465740577635839747469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430310493718423893164979 2145465740577635839747469)
          ·
            refine ⟨804549652716613439905301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2145465740577635839747469 804549652716613439905301)
            ·
              refine ⟨37713264971091254995561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 804549652716613439905301 37713264971091254995561)
              ·
                rfl

theorem cell19_371822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_371822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371822 prefixEnd_371822 := by exact prefixLift 371822
  have htrace : WordTrace (prefixWord ++ tailWord_371822) baseStart_371822 baseEnd_371822 := by
    simpa [prefixWord, tailWord_371822, baseEnd_371822] using wordTrace_append hprefix tailTrace_371822
  have hstable : (prefixWord ++ tailWord_371822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371822).length < 2 ^ (prefixWord ++ tailWord_371822).sum := by decide
  have hdescent : baseEnd_371822 < baseStart_371822 := by decide
  rcases family_descends (prefixWord ++ tailWord_371822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371824 : List Nat := [2, 1, 1, 1, 5, 1, 8]
def baseStart_371824 : Nat := 118140960795 + 371824 * 2 ^ 59
def prefixEnd_371824 : Nat := 4983230072969 + 3 ^ 40 * 371824 * 2
def baseEnd_371824 : Nat := 37713467827646117647411

theorem tailTrace_371824 : CollatzResearch.WordTrace tailWord_371824 prefixEnd_371824 37713467827646117647411 := by
  unfold tailWord_371824
  simp only [CollatzResearch.WordTrace]
  refine ⟨6780767702476312664309263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9041023603301750219079017 6780767702476312664309263)
  ·
    refine ⟨10171151553714468996463895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6780767702476312664309263 10171151553714468996463895)
    ·
      refine ⟨15256727330571703494695843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10171151553714468996463895 15256727330571703494695843)
      ·
        refine ⟨22885090995857555242043765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15256727330571703494695843 22885090995857555242043765)
        ·
          refine ⟨2145477280861645803941603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22885090995857555242043765 2145477280861645803941603)
          ·
            refine ⟨3218215921292468705912405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145477280861645803941603 3218215921292468705912405)
            ·
              refine ⟨37713467827646117647411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3218215921292468705912405 37713467827646117647411)
              ·
                rfl

theorem cell19_371824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_371824 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371824 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371824 prefixEnd_371824 := by exact prefixLift 371824
  have htrace : WordTrace (prefixWord ++ tailWord_371824) baseStart_371824 baseEnd_371824 := by
    simpa [prefixWord, tailWord_371824, baseEnd_371824] using wordTrace_append hprefix tailTrace_371824
  have hstable : (prefixWord ++ tailWord_371824).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371824).length < 2 ^ (prefixWord ++ tailWord_371824).sum := by decide
  have hdescent : baseEnd_371824 < baseStart_371824 := by decide
  rcases family_descends (prefixWord ++ tailWord_371824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371843 : List Nat := [1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_371843 : Nat := 118140960795 + 371843 * 2 ^ 59
def prefixEnd_371843 : Nat := 4983230072969 + 3 ^ 40 * 371843 * 2
def baseEnd_371843 : Nat := 113146184894751938519959

theorem tailTrace_371843 : CollatzResearch.WordTrace tailWord_371843 prefixEnd_371843 113146184894751938519959 := by
  unfold tailWord_371843
  simp only [CollatzResearch.WordTrace]
  refine ⟨13562228391883791573560183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9041485594589194382373455 13562228391883791573560183)
  ·
    refine ⟨20343342587825687360340275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13562228391883791573560183 20343342587825687360340275)
    ·
      refine ⟨30515013881738531040510413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20343342587825687360340275 30515013881738531040510413)
      ·
        refine ⟨11443130205651949140191405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30515013881738531040510413 11443130205651949140191405)
        ·
          refine ⟨4291173827119480927571777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11443130205651949140191405 4291173827119480927571777)
          ·
            refine ⟨3218380370339610695678833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4291173827119480927571777 3218380370339610695678833)
            ·
              refine ⟨2413785277754708021759125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3218380370339610695678833 2413785277754708021759125)
              ·
                refine ⟨113146184894751938519959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2413785277754708021759125 113146184894751938519959)
                ·
                  rfl

theorem cell19_371843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_371843 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371843 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371843 prefixEnd_371843 := by exact prefixLift 371843
  have htrace : WordTrace (prefixWord ++ tailWord_371843) baseStart_371843 baseEnd_371843 := by
    simpa [prefixWord, tailWord_371843, baseEnd_371843] using wordTrace_append hprefix tailTrace_371843
  have hstable : (prefixWord ++ tailWord_371843).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371843).length < 2 ^ (prefixWord ++ tailWord_371843).sum := by decide
  have hdescent : baseEnd_371843 < baseStart_371843 := by decide
  rcases family_descends (prefixWord ++ tailWord_371843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371858 : List Nat := [3, 2, 3, 1, 1, 2, 4, 3]
def baseStart_371858 : Nat := 118140960795 + 371858 * 2 ^ 59
def prefixEnd_371858 : Nat := 4983230072969 + 3 ^ 40 * 371858 * 2
def baseEnd_371858 : Nat := 113150749167236348186585

theorem tailTrace_371858 : CollatzResearch.WordTrace tailWord_371858 prefixEnd_371858 113150749167236348186585 := by
  unfold tailWord_371858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390693871707362283839057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9041850324552966090237485 3390693871707362283839057)
  ·
    refine ⟨2543020403780521712879293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3390693871707362283839057 2543020403780521712879293)
    ·
      refine ⟨953632651417695642329735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2543020403780521712879293 953632651417695642329735)
      ·
        refine ⟨1430448977126543463494603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953632651417695642329735 1430448977126543463494603)
        ·
          refine ⟨2145673465689815195241905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430448977126543463494603 2145673465689815195241905)
          ·
            refine ⟨1609255099267361396431429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145673465689815195241905 1609255099267361396431429)
            ·
              refine ⟨301735331112630261830893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1609255099267361396431429 301735331112630261830893)
              ·
                refine ⟨113150749167236348186585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301735331112630261830893 113150749167236348186585)
                ·
                  rfl

theorem cell19_371858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_371858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371858 prefixEnd_371858 := by exact prefixLift 371858
  have htrace : WordTrace (prefixWord ++ tailWord_371858) baseStart_371858 baseEnd_371858 := by
    simpa [prefixWord, tailWord_371858, baseEnd_371858] using wordTrace_append hprefix tailTrace_371858
  have hstable : (prefixWord ++ tailWord_371858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371858).length < 2 ^ (prefixWord ++ tailWord_371858).sum := by decide
  have hdescent : baseEnd_371858 < baseStart_371858 := by decide
  rcases family_descends (prefixWord ++ tailWord_371858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371879 : List Nat := [1, 1, 6, 2, 1, 1, 7]
def baseStart_371879 : Nat := 118140960795 + 371879 * 2 ^ 59
def prefixEnd_371879 : Nat := 4983230072969 + 3 ^ 40 * 371879 * 2
def baseEnd_371879 : Nat := 37719046382904840573287

theorem tailTrace_371879 : CollatzResearch.WordTrace tailWord_371879 prefixEnd_371879 37719046382904840573287 := by
  unfold tailWord_371879
  simp only [CollatzResearch.WordTrace]
  refine ⟨13563541419753369721870691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9042360946502246481247127 13563541419753369721870691)
  ·
    refine ⟨20345312129630054582806037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13563541419753369721870691 20345312129630054582806037)
    ·
      refine ⟨953686506076408808569033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20345312129630054582806037 953686506076408808569033)
      ·
        refine ⟨715264879557306606426775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 953686506076408808569033 715264879557306606426775)
        ·
          refine ⟨1072897319335959909640163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715264879557306606426775 1072897319335959909640163)
          ·
            refine ⟨1609345979003939864460245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072897319335959909640163 1609345979003939864460245)
            ·
              refine ⟨37719046382904840573287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1609345979003939864460245 37719046382904840573287)
              ·
                rfl

theorem cell19_371879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_371879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371879 prefixEnd_371879 := by exact prefixLift 371879
  have htrace : WordTrace (prefixWord ++ tailWord_371879) baseStart_371879 baseEnd_371879 := by
    simpa [prefixWord, tailWord_371879, baseEnd_371879] using wordTrace_append hprefix tailTrace_371879
  have hstable : (prefixWord ++ tailWord_371879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371879).length < 2 ^ (prefixWord ++ tailWord_371879).sum := by decide
  have hdescent : baseEnd_371879 < baseStart_371879 := by decide
  rcases family_descends (prefixWord ++ tailWord_371879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371955 : List Nat := [1, 1, 1, 2, 2, 7, 1, 4]
def baseStart_371955 : Nat := 118140960795 + 371955 * 2 ^ 59
def prefixEnd_371955 : Nat := 4983230072969 + 3 ^ 40 * 371955 * 2
def baseEnd_371955 : Nat := 113180264795968864030765

theorem tailTrace_371955 : CollatzResearch.WordTrace tailWord_371955 prefixEnd_371955 113180264795968864030765 := by
  unfold tailWord_371955
  simp only [CollatzResearch.WordTrace]
  refine ⟨13566313367478034701637319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9044208911652023134424879 13566313367478034701637319)
  ·
    refine ⟨20349470051217052052455979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13566313367478034701637319 20349470051217052052455979)
    ·
      refine ⟨30524205076825578078683969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20349470051217052052455979 30524205076825578078683969)
      ·
        refine ⟨22893153807619183559012977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30524205076825578078683969 22893153807619183559012977)
        ·
          refine ⟨17169865355714387669259733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22893153807619183559012977 17169865355714387669259733)
          ·
            refine ⟨402418719274555960998275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17169865355714387669259733 402418719274555960998275)
            ·
              refine ⟨603628078911833941497413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402418719274555960998275 603628078911833941497413)
              ·
                refine ⟨113180264795968864030765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 603628078911833941497413 113180264795968864030765)
                ·
                  rfl

theorem cell19_371955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_371955 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371955 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371955 prefixEnd_371955 := by exact prefixLift 371955
  have htrace : WordTrace (prefixWord ++ tailWord_371955) baseStart_371955 baseEnd_371955 := by
    simpa [prefixWord, tailWord_371955, baseEnd_371955] using wordTrace_append hprefix tailTrace_371955
  have hstable : (prefixWord ++ tailWord_371955).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371955).length < 2 ^ (prefixWord ++ tailWord_371955).sum := by decide
  have hdescent : baseEnd_371955 < baseStart_371955 := by decide
  rcases family_descends (prefixWord ++ tailWord_371955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371970 : List Nat := [3, 4, 1, 1, 3, 1, 3, 3]
def baseStart_371970 : Nat := 118140960795 + 371970 * 2 ^ 59
def prefixEnd_371970 : Nat := 4983230072969 + 3 ^ 40 * 371970 * 2
def baseEnd_371970 : Nat := 113184829068453273697391

theorem tailTrace_371970 : CollatzResearch.WordTrace tailWord_371970 prefixEnd_371970 113184829068453273697391 := by
  unfold tailWord_371970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3391715115605923065858341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9044573641615794842288909 3391715115605923065858341)
  ·
    refine ⟨635946584176110574848439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3391715115605923065858341 635946584176110574848439)
    ·
      refine ⟨953919876264165862272659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635946584176110574848439 953919876264165862272659)
      ·
        refine ⟨1430879814396248793408989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953919876264165862272659 1430879814396248793408989)
        ·
          refine ⟨536579930398593297528371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1430879814396248793408989 536579930398593297528371)
          ·
            refine ⟨804869895597889946292557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536579930398593297528371 804869895597889946292557)
            ·
              refine ⟨301826210849208729859709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 804869895597889946292557 301826210849208729859709)
              ·
                refine ⟨113184829068453273697391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301826210849208729859709 113184829068453273697391)
                ·
                  rfl

theorem cell19_371970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_371970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371970 prefixEnd_371970 := by exact prefixLift 371970
  have htrace : WordTrace (prefixWord ++ tailWord_371970) baseStart_371970 baseEnd_371970 := by
    simpa [prefixWord, tailWord_371970, baseEnd_371970] using wordTrace_append hprefix tailTrace_371970
  have hstable : (prefixWord ++ tailWord_371970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371970).length < 2 ^ (prefixWord ++ tailWord_371970).sum := by decide
  have hdescent : baseEnd_371970 < baseStart_371970 := by decide
  rcases family_descends (prefixWord ++ tailWord_371970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371972 : List Nat := [2, 3, 2, 2, 2, 2, 3, 3]
def baseStart_371972 : Nat := 118140960795 + 371972 * 2 ^ 59
def prefixEnd_371972 : Nat := 4983230072969 + 3 ^ 40 * 371972 * 2
def baseEnd_371972 : Nat := 113185437638117861652941

theorem tailTrace_371972 : CollatzResearch.WordTrace tailWord_371972 prefixEnd_371972 113185437638117861652941 := by
  unfold tailWord_371972
  simp only [CollatzResearch.WordTrace]
  refine ⟨6783466704208223302503085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9044622272277631070004113 6783466704208223302503085)
  ·
    refine ⟨2543800014078083738438657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6783466704208223302503085 2543800014078083738438657)
    ·
      refine ⟨1907850010558562803828993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2543800014078083738438657 1907850010558562803828993)
      ·
        refine ⟨1430887507918922102871745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1907850010558562803828993 1430887507918922102871745)
        ·
          refine ⟨1073165630939191577153809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430887507918922102871745 1073165630939191577153809)
          ·
            refine ⟨804874223204393682865357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073165630939191577153809 804874223204393682865357)
            ·
              refine ⟨301827833701647631074509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 804874223204393682865357 301827833701647631074509)
              ·
                refine ⟨113185437638117861652941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301827833701647631074509 113185437638117861652941)
                ·
                  rfl

theorem cell19_371972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_371972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371972 prefixEnd_371972 := by exact prefixLift 371972
  have htrace : WordTrace (prefixWord ++ tailWord_371972) baseStart_371972 baseEnd_371972 := by
    simpa [prefixWord, tailWord_371972, baseEnd_371972] using wordTrace_append hprefix tailTrace_371972
  have hstable : (prefixWord ++ tailWord_371972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371972).length < 2 ^ (prefixWord ++ tailWord_371972).sum := by decide
  have hdescent : baseEnd_371972 < baseStart_371972 := by decide
  rcases family_descends (prefixWord ++ tailWord_371972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372029 : List Nat := [1, 4, 1, 5, 1, 1, 1, 5]
def baseStart_372029 : Nat := 118140960795 + 372029 * 2 ^ 59
def prefixEnd_372029 : Nat := 4983230072969 + 3 ^ 40 * 372029 * 2
def baseEnd_372029 : Nat := 113202781873558618386119

theorem tailTrace_372029 : CollatzResearch.WordTrace tailWord_372029 prefixEnd_372029 113202781873558618386119 := by
  unfold tailWord_372029
  simp only [CollatzResearch.WordTrace]
  refine ⟨13569012369209945339831141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9046008246139963559887427 13569012369209945339831141)
  ·
    refine ⟨2544189819226864751218339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13569012369209945339831141 2544189819226864751218339)
    ·
      refine ⟨3816284728840297126827509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2544189819226864751218339 3816284728840297126827509)
      ·
        refine ⟨357776693328777855640079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3816284728840297126827509 357776693328777855640079)
        ·
          refine ⟨536665039993166783460119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357776693328777855640079 536665039993166783460119)
          ·
            refine ⟨804997559989750175190179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536665039993166783460119 804997559989750175190179)
            ·
              refine ⟨1207496339984625262785269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804997559989750175190179 1207496339984625262785269)
              ·
                refine ⟨113202781873558618386119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1207496339984625262785269 113202781873558618386119)
                ·
                  rfl

theorem cell19_372029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 5].length) (baseStart_372029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372029 prefixEnd_372029 := by exact prefixLift 372029
  have htrace : WordTrace (prefixWord ++ tailWord_372029) baseStart_372029 baseEnd_372029 := by
    simpa [prefixWord, tailWord_372029, baseEnd_372029] using wordTrace_append hprefix tailTrace_372029
  have hstable : (prefixWord ++ tailWord_372029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372029).length < 2 ^ (prefixWord ++ tailWord_372029).sum := by decide
  have hdescent : baseEnd_372029 < baseStart_372029 := by decide
  rcases family_descends (prefixWord ++ tailWord_372029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372031 : List Nat := [1, 1, 2, 2, 4, 2, 4, 3]
def baseStart_372031 : Nat := 118140960795 + 372031 * 2 ^ 59
def prefixEnd_372031 : Nat := 4983230072969 + 3 ^ 40 * 372031 * 2
def baseEnd_372031 : Nat := 113203390443223206341669

theorem tailTrace_372031 : CollatzResearch.WordTrace tailWord_372031 prefixEnd_372031 113203390443223206341669 := by
  unfold tailWord_372031
  simp only [CollatzResearch.WordTrace]
  refine ⟨13569085315202699681403947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9046056876801799787602631 13569085315202699681403947)
  ·
    refine ⟨20353627972804049522105921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13569085315202699681403947 20353627972804049522105921)
    ·
      refine ⟨15265220979603037141579441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20353627972804049522105921 15265220979603037141579441)
      ·
        refine ⟨11448915734702277856184581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15265220979603037141579441 11448915734702277856184581)
        ·
          refine ⟨2146671700256677098034609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11448915734702277856184581 2146671700256677098034609)
          ·
            refine ⟨1610003775192507823525957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2146671700256677098034609 1610003775192507823525957)
            ·
              refine ⟨301875707848595216911117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1610003775192507823525957 301875707848595216911117)
              ·
                refine ⟨113203390443223206341669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301875707848595216911117 113203390443223206341669)
                ·
                  rfl

theorem cell19_372031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 3].length) (baseStart_372031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372031 prefixEnd_372031 := by exact prefixLift 372031
  have htrace : WordTrace (prefixWord ++ tailWord_372031) baseStart_372031 baseEnd_372031 := by
    simpa [prefixWord, tailWord_372031, baseEnd_372031] using wordTrace_append hprefix tailTrace_372031
  have hstable : (prefixWord ++ tailWord_372031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372031).length < 2 ^ (prefixWord ++ tailWord_372031).sum := by decide
  have hdescent : baseEnd_372031 < baseStart_372031 := by decide
  rcases family_descends (prefixWord ++ tailWord_372031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372145 : List Nat := [1, 2, 2, 4, 1, 1, 5, 3]
def baseStart_372145 : Nat := 118140960795 + 372145 * 2 ^ 59
def prefixEnd_372145 : Nat := 4983230072969 + 3 ^ 40 * 372145 * 2
def baseEnd_372145 : Nat := 113238078914104719808025

theorem tailTrace_372145 : CollatzResearch.WordTrace tailWord_372145 prefixEnd_372145 113238078914104719808025 := by
  unfold tailWord_372145
  simp only [CollatzResearch.WordTrace]
  refine ⟨13573243236789697151053889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9048828824526464767369259 13573243236789697151053889)
  ·
    refine ⟨10179932427592272863290417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13573243236789697151053889 10179932427592272863290417)
    ·
      refine ⟨7634949320694204647467813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10179932427592272863290417 7634949320694204647467813)
      ·
        refine ⟨1431552997630163371400215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7634949320694204647467813 1431552997630163371400215)
        ·
          refine ⟨2147329496445245057100323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431552997630163371400215 2147329496445245057100323)
          ·
            refine ⟨3220994244667867585650485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147329496445245057100323 3220994244667867585650485)
            ·
              refine ⟨301968210437612586154733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3220994244667867585650485 301968210437612586154733)
              ·
                refine ⟨113238078914104719808025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301968210437612586154733 113238078914104719808025)
                ·
                  rfl

theorem cell19_372145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 3].length) (baseStart_372145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372145 prefixEnd_372145 := by exact prefixLift 372145
  have htrace : WordTrace (prefixWord ++ tailWord_372145) baseStart_372145 baseEnd_372145 := by
    simpa [prefixWord, tailWord_372145, baseEnd_372145] using wordTrace_append hprefix tailTrace_372145
  have hstable : (prefixWord ++ tailWord_372145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372145).length < 2 ^ (prefixWord ++ tailWord_372145).sum := by decide
  have hdescent : baseEnd_372145 < baseStart_372145 := by decide
  rcases family_descends (prefixWord ++ tailWord_372145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372164 : List Nat := [2, 3, 3, 2, 1, 2, 6]
def baseStart_372164 : Nat := 118140960795 + 372164 * 2 ^ 59
def prefixEnd_372164 : Nat := 4983230072969 + 3 ^ 40 * 372164 * 2
def baseEnd_372164 : Nat := 37747953441972768461917

theorem tailTrace_372164 : CollatzResearch.WordTrace tailWord_372164 prefixEnd_372164 37747953441972768461917 := by
  unfold tailWord_372164
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786968111860431697997773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9049290815813908930663697 6786968111860431697997773)
  ·
    refine ⟨2545113041947661886749165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6786968111860431697997773 2545113041947661886749165)
    ·
      refine ⟨954417390730373207530937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2545113041947661886749165 954417390730373207530937)
      ·
        refine ⟨715813043047779905648203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 954417390730373207530937 715813043047779905648203)
        ·
          refine ⟨1073719564571669858472305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715813043047779905648203 1073719564571669858472305)
          ·
            refine ⟨805289673428752393854229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073719564571669858472305 805289673428752393854229)
            ·
              refine ⟨37747953441972768461917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 805289673428752393854229 37747953441972768461917)
              ·
                rfl

theorem cell19_372164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_372164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372164 prefixEnd_372164 := by exact prefixLift 372164
  have htrace : WordTrace (prefixWord ++ tailWord_372164) baseStart_372164 baseEnd_372164 := by
    simpa [prefixWord, tailWord_372164, baseEnd_372164] using wordTrace_append hprefix tailTrace_372164
  have hstable : (prefixWord ++ tailWord_372164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372164).length < 2 ^ (prefixWord ++ tailWord_372164).sum := by decide
  have hdescent : baseEnd_372164 < baseStart_372164 := by decide
  rcases family_descends (prefixWord ++ tailWord_372164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372202 : List Nat := [3, 1, 3, 1, 4, 1, 1, 5]
def baseStart_372202 : Nat := 118140960795 + 372202 * 2 ^ 59
def prefixEnd_372202 : Nat := 4983230072969 + 3 ^ 40 * 372202 * 2
def baseEnd_372202 : Nat := 113255423149545476541203

theorem tailTrace_372202 : CollatzResearch.WordTrace tailWord_372202 prefixEnd_372202 113255423149545476541203 := by
  unfold tailWord_372202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3393830549395798971469715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9050214798388797257252573 3393830549395798971469715)
  ·
    refine ⟨5090745824093698457204573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3393830549395798971469715 5090745824093698457204573)
    ·
      refine ⟨1909029684035136921451715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5090745824093698457204573 1909029684035136921451715)
      ·
        refine ⟨2863544526052705382177573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1909029684035136921451715 2863544526052705382177573)
        ·
          refine ⟨536914598634882259158295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2863544526052705382177573 536914598634882259158295)
          ·
            refine ⟨805371897952323388737443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536914598634882259158295 805371897952323388737443)
            ·
              refine ⟨1208057846928485083106165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805371897952323388737443 1208057846928485083106165)
              ·
                refine ⟨113255423149545476541203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1208057846928485083106165 113255423149545476541203)
                ·
                  rfl

theorem cell19_372202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_372202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372202 prefixEnd_372202 := by exact prefixLift 372202
  have htrace : WordTrace (prefixWord ++ tailWord_372202) baseStart_372202 baseEnd_372202 := by
    simpa [prefixWord, tailWord_372202, baseEnd_372202] using wordTrace_append hprefix tailTrace_372202
  have hstable : (prefixWord ++ tailWord_372202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372202).length < 2 ^ (prefixWord ++ tailWord_372202).sum := by decide
  have hdescent : baseEnd_372202 < baseStart_372202 := by decide
  rcases family_descends (prefixWord ++ tailWord_372202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372278 : List Nat := [5, 1, 2, 1, 3, 7]
def baseStart_372278 : Nat := 118140960795 + 372278 * 2 ^ 59
def prefixEnd_372278 : Nat := 4983230072969 + 3 ^ 40 * 372278 * 2
def baseEnd_372278 : Nat := 12586505421866646539123

theorem tailTrace_372278 : CollatzResearch.WordTrace tailWord_372278 prefixEnd_372278 12586505421866646539123 := by
  unfold tailWord_372278
  simp only [CollatzResearch.WordTrace]
  refine ⟨848630884081741304102843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9052062763538573910430325 848630884081741304102843)
  ·
    refine ⟨1272946326122611956154265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 848630884081741304102843 1272946326122611956154265)
    ·
      refine ⟨954709744591958967115699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1272946326122611956154265 954709744591958967115699)
      ·
        refine ⟨1432064616887938450673549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 954709744591958967115699 1432064616887938450673549)
        ·
          refine ⟨537024231332976919002581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1432064616887938450673549 537024231332976919002581)
          ·
            refine ⟨12586505421866646539123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 537024231332976919002581 12586505421866646539123)
            ·
              rfl

theorem cell19_372278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 7].length) (baseStart_372278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372278 prefixEnd_372278 := by exact prefixLift 372278
  have htrace : WordTrace (prefixWord ++ tailWord_372278) baseStart_372278 baseEnd_372278 := by
    simpa [prefixWord, tailWord_372278, baseEnd_372278] using wordTrace_append hprefix tailTrace_372278
  have hstable : (prefixWord ++ tailWord_372278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372278).length < 2 ^ (prefixWord ++ tailWord_372278).sum := by decide
  have hdescent : baseEnd_372278 < baseStart_372278 := by decide
  rcases family_descends (prefixWord ++ tailWord_372278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372295 : List Nat := [1, 1, 4, 1, 6, 1, 1, 4]
def baseStart_372295 : Nat := 118140960795 + 372295 * 2 ^ 59
def prefixEnd_372295 : Nat := 4983230072969 + 3 ^ 40 * 372295 * 2
def baseEnd_372295 : Nat := 113283721638948816474283

theorem tailTrace_372295 : CollatzResearch.WordTrace tailWord_372295 prefixEnd_372295 113283721638948816474283 := by
  unfold tailWord_372295
  simp only [CollatzResearch.WordTrace]
  refine ⟨13578714186246272769014339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9052476124164181846009559 13578714186246272769014339)
  ·
    refine ⟨20368071279369409153521509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13578714186246272769014339 20368071279369409153521509)
    ·
      refine ⟨3819013364881764216285283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20368071279369409153521509 3819013364881764216285283)
      ·
        refine ⟨5728520047322646324427925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3819013364881764216285283 5728520047322646324427925)
        ·
          refine ⟨268524377218249046457559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5728520047322646324427925 268524377218249046457559)
          ·
            refine ⟨402786565827373569686339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268524377218249046457559 402786565827373569686339)
            ·
              refine ⟨604179848741060354529509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402786565827373569686339 604179848741060354529509)
              ·
                refine ⟨113283721638948816474283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 604179848741060354529509 113283721638948816474283)
                ·
                  rfl

theorem cell19_372295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 4].length) (baseStart_372295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372295 prefixEnd_372295 := by exact prefixLift 372295
  have htrace : WordTrace (prefixWord ++ tailWord_372295) baseStart_372295 baseEnd_372295 := by
    simpa [prefixWord, tailWord_372295, baseEnd_372295] using wordTrace_append hprefix tailTrace_372295
  have hstable : (prefixWord ++ tailWord_372295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372295).length < 2 ^ (prefixWord ++ tailWord_372295).sum := by decide
  have hdescent : baseEnd_372295 < baseStart_372295 := by decide
  rcases family_descends (prefixWord ++ tailWord_372295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372310 : List Nat := [5, 2, 2, 2, 1, 1, 3, 3]
def baseStart_372310 : Nat := 118140960795 + 372310 * 2 ^ 59
def prefixEnd_372310 : Nat := 4983230072969 + 3 ^ 40 * 372310 * 2
def baseEnd_372310 : Nat := 113288285911433226140909

theorem tailTrace_372310 : CollatzResearch.WordTrace tailWord_372310 prefixEnd_372310 113288285911433226140909 := by
  unfold tailWord_372310
  simp only [CollatzResearch.WordTrace]
  refine ⟨848703830074495645675649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9052840854127953553873589 848703830074495645675649)
  ·
    refine ⟨636527872555871734256737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 848703830074495645675649 636527872555871734256737)
    ·
      refine ⟨477395904416903800692553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 636527872555871734256737 477395904416903800692553)
      ·
        refine ⟨358046928312677850519415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477395904416903800692553 358046928312677850519415)
        ·
          refine ⟨537070392469016775779123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358046928312677850519415 537070392469016775779123)
          ·
            refine ⟨805605588703525163668685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537070392469016775779123 805605588703525163668685)
            ·
              refine ⟨302102095763821936375757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805605588703525163668685 302102095763821936375757)
              ·
                refine ⟨113288285911433226140909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302102095763821936375757 113288285911433226140909)
                ·
                  rfl

theorem cell19_372310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_372310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372310 prefixEnd_372310 := by exact prefixLift 372310
  have htrace : WordTrace (prefixWord ++ tailWord_372310) baseStart_372310 baseEnd_372310 := by
    simpa [prefixWord, tailWord_372310, baseEnd_372310] using wordTrace_append hprefix tailTrace_372310
  have hstable : (prefixWord ++ tailWord_372310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372310).length < 2 ^ (prefixWord ++ tailWord_372310).sum := by decide
  have hdescent : baseEnd_372310 < baseStart_372310 := by decide
  rcases family_descends (prefixWord ++ tailWord_372310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372375 : List Nat := [1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_372375 : Nat := 118140960795 + 372375 * 2 ^ 59
def prefixEnd_372375 : Nat := 4983230072969 + 3 ^ 40 * 372375 * 2
def baseEnd_372375 : Nat := 113308064425532334696287

theorem tailTrace_372375 : CollatzResearch.WordTrace tailWord_372375 prefixEnd_372375 113308064425532334696287 := by
  unfold tailWord_372375
  simp only [CollatzResearch.WordTrace]
  refine ⟨13581632025956446431926579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9054421350637630954617719 13581632025956446431926579)
  ·
    refine ⟨20372448038934669647889869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13581632025956446431926579 20372448038934669647889869)
    ·
      refine ⟨7639668014600501117958701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20372448038934669647889869 7639668014600501117958701)
      ·
        refine ⟨2864875505475187919234513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7639668014600501117958701 2864875505475187919234513)
        ·
          refine ⟨2148656629106390939425885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2864875505475187919234513 2148656629106390939425885)
          ·
            refine ⟨805746235914896602284707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2148656629106390939425885 805746235914896602284707)
            ·
              refine ⟨1208619353872344903427061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805746235914896602284707 1208619353872344903427061)
              ·
                refine ⟨113308064425532334696287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1208619353872344903427061 113308064425532334696287)
                ·
                  rfl

theorem cell19_372375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_372375 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372375 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372375 prefixEnd_372375 := by exact prefixLift 372375
  have htrace : WordTrace (prefixWord ++ tailWord_372375) baseStart_372375 baseEnd_372375 := by
    simpa [prefixWord, tailWord_372375, baseEnd_372375] using wordTrace_append hprefix tailTrace_372375
  have hstable : (prefixWord ++ tailWord_372375).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372375).length < 2 ^ (prefixWord ++ tailWord_372375).sum := by decide
  have hdescent : baseEnd_372375 < baseStart_372375 := by decide
  rcases family_descends (prefixWord ++ tailWord_372375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372413 : List Nat := [1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_372413 : Nat := 118140960795 + 372413 * 2 ^ 59
def prefixEnd_372413 : Nat := 4983230072969 + 3 ^ 40 * 372413 * 2
def baseEnd_372413 : Nat := 113319627249159505851739

theorem tailTrace_372413 : CollatzResearch.WordTrace tailWord_372413 prefixEnd_372413 113319627249159505851739 := by
  unfold tailWord_372413
  simp only [CollatzResearch.WordTrace]
  refine ⟨13583017999818778921809893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9055345333212519281206595 13583017999818778921809893)
  ·
    refine ⟨2546815874966021047839355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13583017999818778921809893 2546815874966021047839355)
    ·
      refine ⟨3820223812449031571759033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2546815874966021047839355 3820223812449031571759033)
      ·
        refine ⟨2865167859336773678819275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3820223812449031571759033 2865167859336773678819275)
        ·
          refine ⟨4297751789005160518228913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865167859336773678819275 4297751789005160518228913)
          ·
            refine ⟨3223313841753870388671685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4297751789005160518228913 3223313841753870388671685)
            ·
              refine ⟨604371345328850697875941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3223313841753870388671685 604371345328850697875941)
              ·
                refine ⟨113319627249159505851739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 604371345328850697875941 113319627249159505851739)
                ·
                  rfl

theorem cell19_372413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_372413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372413 prefixEnd_372413 := by exact prefixLift 372413
  have htrace : WordTrace (prefixWord ++ tailWord_372413) baseStart_372413 baseEnd_372413 := by
    simpa [prefixWord, tailWord_372413, baseEnd_372413] using wordTrace_append hprefix tailTrace_372413
  have hstable : (prefixWord ++ tailWord_372413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372413).length < 2 ^ (prefixWord ++ tailWord_372413).sum := by decide
  have hdescent : baseEnd_372413 < baseStart_372413 := by decide
  rcases family_descends (prefixWord ++ tailWord_372413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372451 : List Nat := [1, 1, 1, 7, 2, 7]
def baseStart_372451 : Nat := 118140960795 + 372451 * 2 ^ 59
def prefixEnd_372451 : Nat := 4983230072969 + 3 ^ 40 * 372451 * 2
def baseEnd_372451 : Nat := 12592354452531853000799

theorem tailTrace_372451 : CollatzResearch.WordTrace tailWord_372451 prefixEnd_372451 12592354452531853000799 := by
  unfold tailWord_372451
  simp only [CollatzResearch.WordTrace]
  refine ⟨13584403973681111411693207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9056269315787407607795471 13584403973681111411693207)
  ·
    refine ⟨20376605960521667117539811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13584403973681111411693207 20376605960521667117539811)
    ·
      refine ⟨30564908940782500676309717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20376605960521667117539811 30564908940782500676309717)
      ·
        refine ⟨716365053299589859601009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 30564908940782500676309717 716365053299589859601009)
        ·
          refine ⟨537273789974692394700757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716365053299589859601009 537273789974692394700757)
          ·
            refine ⟨12592354452531853000799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 537273789974692394700757 12592354452531853000799)
            ·
              rfl

theorem cell19_372451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 7].length) (baseStart_372451 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372451 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372451 prefixEnd_372451 := by exact prefixLift 372451
  have htrace : WordTrace (prefixWord ++ tailWord_372451) baseStart_372451 baseEnd_372451 := by
    simpa [prefixWord, tailWord_372451, baseEnd_372451] using wordTrace_append hprefix tailTrace_372451
  have hstable : (prefixWord ++ tailWord_372451).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372451).length < 2 ^ (prefixWord ++ tailWord_372451).sum := by decide
  have hdescent : baseEnd_372451 < baseStart_372451 := by decide
  rcases family_descends (prefixWord ++ tailWord_372451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372472 : List Nat := [2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_372472 : Nat := 118140960795 + 372472 * 2 ^ 59
def prefixEnd_372472 : Nat := 4983230072969 + 3 ^ 40 * 372472 * 2
def baseEnd_372472 : Nat := 113337580054264850540467

theorem tailTrace_372472 : CollatzResearch.WordTrace tailWord_372472 prefixEnd_372472 113337580054264850540467 := by
  unfold tailWord_372472
  simp only [CollatzResearch.WordTrace]
  refine ⟨6792584953302515999103835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9056779937736687998805113 6792584953302515999103835)
  ·
    refine ⟨10188877429953773998655753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6792584953302515999103835 10188877429953773998655753)
    ·
      refine ⟨7641658072465330498991815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10188877429953773998655753 7641658072465330498991815)
      ·
        refine ⟨11462487108697995748487723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7641658072465330498991815 11462487108697995748487723)
        ·
          refine ⟨17193730663046993622731585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11462487108697995748487723 17193730663046993622731585)
          ·
            refine ⟨12895297997285245217048689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17193730663046993622731585 12895297997285245217048689)
            ·
              refine ⟨9671473497963933912786517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12895297997285245217048689 9671473497963933912786517)
              ·
                refine ⟨113337580054264850540467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9671473497963933912786517 113337580054264850540467)
                ·
                  rfl

theorem cell19_372472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_372472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372472 prefixEnd_372472 := by exact prefixLift 372472
  have htrace : WordTrace (prefixWord ++ tailWord_372472) baseStart_372472 baseEnd_372472 := by
    simpa [prefixWord, tailWord_372472, baseEnd_372472] using wordTrace_append hprefix tailTrace_372472
  have hstable : (prefixWord ++ tailWord_372472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372472).length < 2 ^ (prefixWord ++ tailWord_372472).sum := by decide
  have hdescent : baseEnd_372472 < baseStart_372472 := by decide
  rcases family_descends (prefixWord ++ tailWord_372472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372491 : List Nat := [1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_372491 : Nat := 118140960795 + 372491 * 2 ^ 59
def prefixEnd_372491 : Nat := 4983230072969 + 3 ^ 40 * 372491 * 2
def baseEnd_372491 : Nat := 113343361466078436118193

theorem tailTrace_372491 : CollatzResearch.WordTrace tailWord_372491 prefixEnd_372491 113343361466078436118193 := by
  unfold tailWord_372491
  simp only [CollatzResearch.WordTrace]
  refine ⟨13585862893536198243149327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9057241929024132162099551 13585862893536198243149327)
  ·
    refine ⟨20378794340304297364723991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13585862893536198243149327 20378794340304297364723991)
    ·
      refine ⟨30568191510456446047085987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20378794340304297364723991 30568191510456446047085987)
      ·
        refine ⟨45852287265684669070628981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30568191510456446047085987 45852287265684669070628981)
        ·
          refine ⟨4298651931157937725371467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45852287265684669070628981 4298651931157937725371467)
          ·
            refine ⟨6447977896736906588057201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298651931157937725371467 6447977896736906588057201)
            ·
              refine ⟨4835983422552679941042901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6447977896736906588057201 4835983422552679941042901)
              ·
                refine ⟨113343361466078436118193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4835983422552679941042901 113343361466078436118193)
                ·
                  rfl

theorem cell19_372491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_372491 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372491 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372491 prefixEnd_372491 := by exact prefixLift 372491
  have htrace : WordTrace (prefixWord ++ tailWord_372491) baseStart_372491 baseEnd_372491 := by
    simpa [prefixWord, tailWord_372491, baseEnd_372491] using wordTrace_append hprefix tailTrace_372491
  have hstable : (prefixWord ++ tailWord_372491).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372491).length < 2 ^ (prefixWord ++ tailWord_372491).sum := by decide
  have hdescent : baseEnd_372491 < baseStart_372491 := by decide
  rcases family_descends (prefixWord ++ tailWord_372491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372542 : List Nat := [4, 2, 1, 2, 2, 3, 2, 3]
def baseStart_372542 : Nat := 118140960795 + 372542 * 2 ^ 59
def prefixEnd_372542 : Nat := 4983230072969 + 3 ^ 40 * 372542 * 2
def baseEnd_372542 : Nat := 113358879992525428984721

theorem tailTrace_372542 : CollatzResearch.WordTrace tailWord_372542 prefixEnd_372542 113358879992525428984721 := by
  unfold tailWord_372542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698465377043929244156985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9058482010900955968837253 1698465377043929244156985)
  ·
    refine ⟨1273849032782946933117739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1698465377043929244156985 1273849032782946933117739)
    ·
      refine ⟨1910773549174420399676609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1273849032782946933117739 1910773549174420399676609)
      ·
        refine ⟨1433080161880815299757457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1910773549174420399676609 1433080161880815299757457)
        ·
          refine ⟨1074810121410611474818093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1433080161880815299757457 1074810121410611474818093)
          ·
            refine ⟨403053795528979303056785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1074810121410611474818093 403053795528979303056785)
            ·
              refine ⟨302290346646734477292589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403053795528979303056785 302290346646734477292589)
              ·
                refine ⟨113358879992525428984721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302290346646734477292589 113358879992525428984721)
                ·
                  rfl

theorem cell19_372542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_372542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372542 prefixEnd_372542 := by exact prefixLift 372542
  have htrace : WordTrace (prefixWord ++ tailWord_372542) baseStart_372542 baseEnd_372542 := by
    simpa [prefixWord, tailWord_372542, baseEnd_372542] using wordTrace_append hprefix tailTrace_372542
  have hstable : (prefixWord ++ tailWord_372542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372542).length < 2 ^ (prefixWord ++ tailWord_372542).sum := by decide
  have hdescent : baseEnd_372542 < baseStart_372542 := by decide
  rcases family_descends (prefixWord ++ tailWord_372542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372565 : List Nat := [1, 3, 2, 2, 2, 4, 5]
def baseStart_372565 : Nat := 118140960795 + 372565 * 2 ^ 59
def prefixEnd_372565 : Nat := 4983230072969 + 3 ^ 40 * 372565 * 2
def baseEnd_372565 : Nat := 37788626181222730157849

theorem tailTrace_372565 : CollatzResearch.WordTrace tailWord_372565 prefixEnd_372565 37788626181222730157849 := by
  unfold tailWord_372565
  simp only [CollatzResearch.WordTrace]
  refine ⟨13588561895268108881343149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9059041263512072587562099 13588561895268108881343149)
  ·
    refine ⟨5095710710725540830503681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13588561895268108881343149 5095710710725540830503681)
    ·
      refine ⟨3821783033044155622877761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5095710710725540830503681 3821783033044155622877761)
      ·
        refine ⟨2866337274783116717158321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3821783033044155622877761 2866337274783116717158321)
        ·
          refine ⟨2149752956087337537868741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2866337274783116717158321 2149752956087337537868741)
          ·
            refine ⟨403078679266375788350389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2149752956087337537868741 403078679266375788350389)
            ·
              refine ⟨37788626181222730157849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 403078679266375788350389 37788626181222730157849)
              ·
                rfl

theorem cell19_372565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_372565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372565 prefixEnd_372565 := by exact prefixLift 372565
  have htrace : WordTrace (prefixWord ++ tailWord_372565) baseStart_372565 baseEnd_372565 := by
    simpa [prefixWord, tailWord_372565, baseEnd_372565] using wordTrace_append hprefix tailTrace_372565
  have hstable : (prefixWord ++ tailWord_372565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372565).length < 2 ^ (prefixWord ++ tailWord_372565).sum := by decide
  have hdescent : baseEnd_372565 < baseStart_372565 := by decide
  rcases family_descends (prefixWord ++ tailWord_372565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372584 : List Nat := [2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_372584 : Nat := 118140960795 + 372584 * 2 ^ 59
def prefixEnd_372584 : Nat := 4983230072969 + 3 ^ 40 * 372584 * 2
def baseEnd_372584 : Nat := 113371659955481776051273

theorem tailTrace_372584 : CollatzResearch.WordTrace tailWord_372584 prefixEnd_372584 113371659955481776051273 := by
  unfold tailWord_372584
  simp only [CollatzResearch.WordTrace]
  refine ⟨6794627441099637563142403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9059503254799516750856537 6794627441099637563142403)
  ·
    refine ⟨10191941161649456344713605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6794627441099637563142403 10191941161649456344713605)
    ·
      refine ⟨1910988967809273064633801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10191941161649456344713605 1910988967809273064633801)
      ·
        refine ⟨1433241725856954798475351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1910988967809273064633801 1433241725856954798475351)
        ·
          refine ⟨2149862588785432197713027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433241725856954798475351 2149862588785432197713027)
          ·
            refine ⟨3224793883178148296569541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149862588785432197713027 3224793883178148296569541)
            ·
              refine ⟨604648853095902805606789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3224793883178148296569541 604648853095902805606789)
              ·
                refine ⟨113371659955481776051273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 604648853095902805606789 113371659955481776051273)
                ·
                  rfl

theorem cell19_372584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_372584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372584 prefixEnd_372584 := by exact prefixLift 372584
  have htrace : WordTrace (prefixWord ++ tailWord_372584) baseStart_372584 baseEnd_372584 := by
    simpa [prefixWord, tailWord_372584, baseEnd_372584] using wordTrace_append hprefix tailTrace_372584
  have hstable : (prefixWord ++ tailWord_372584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372584).length < 2 ^ (prefixWord ++ tailWord_372584).sum := by decide
  have hdescent : baseEnd_372584 < baseStart_372584 := by decide
  rcases family_descends (prefixWord ++ tailWord_372584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372622 : List Nat := [4, 1, 1, 5, 8]
def baseStart_372622 : Nat := 118140960795 + 372622 * 2 ^ 59
def prefixEnd_372622 : Nat := 4983230072969 + 3 ^ 40 * 372622 * 2
def baseEnd_372622 : Nat := 4199378621448479526175

theorem tailTrace_372622 : CollatzResearch.WordTrace tailWord_372622 prefixEnd_372622 4199378621448479526175 := by
  unfold tailWord_372622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698830107007700952021015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9060427237374405077445413 1698830107007700952021015)
  ·
    refine ⟨2548245160511551428031523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1698830107007700952021015 2548245160511551428031523)
    ·
      refine ⟨3822367740767327142047285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2548245160511551428031523 3822367740767327142047285)
      ·
        refine ⟨358346975696936919566933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3822367740767327142047285 358346975696936919566933)
        ·
          refine ⟨4199378621448479526175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 358346975696936919566933 4199378621448479526175)
          ·
            rfl

theorem cell19_372622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 8].length) (baseStart_372622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372622 prefixEnd_372622 := by exact prefixLift 372622
  have htrace : WordTrace (prefixWord ++ tailWord_372622) baseStart_372622 baseEnd_372622 := by
    simpa [prefixWord, tailWord_372622, baseEnd_372622] using wordTrace_append hprefix tailTrace_372622
  have hstable : (prefixWord ++ tailWord_372622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372622).length < 2 ^ (prefixWord ++ tailWord_372622).sum := by decide
  have hdescent : baseEnd_372622 < baseStart_372622 := by decide
  rcases family_descends (prefixWord ++ tailWord_372622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372639 : List Nat := [1, 1, 2, 5, 3, 2, 1, 4]
def baseStart_372639 : Nat := 118140960795 + 372639 * 2 ^ 59
def prefixEnd_372639 : Nat := 4983230072969 + 3 ^ 40 * 372639 * 2
def baseEnd_372639 : Nat := 113388395621257944828901

theorem tailTrace_372639 : CollatzResearch.WordTrace tailWord_372639 prefixEnd_372639 113388395621257944828901 := by
  unfold tailWord_372639
  simp only [CollatzResearch.WordTrace]
  refine ⟨13591260897000019519536971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9060840598000013013024647 13591260897000019519536971)
  ·
    refine ⟨20386891345500029279305457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13591260897000019519536971 20386891345500029279305457)
    ·
      refine ⟨15290168509125021959479093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20386891345500029279305457 15290168509125021959479093)
      ·
        refine ⟨1433453297730470808701165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15290168509125021959479093 1433453297730470808701165)
        ·
          refine ⟨537544986648926553262937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1433453297730470808701165 537544986648926553262937)
          ·
            refine ⟨403158739986694914947203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537544986648926553262937 403158739986694914947203)
            ·
              refine ⟨604738109980042372420805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403158739986694914947203 604738109980042372420805)
              ·
                refine ⟨113388395621257944828901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 604738109980042372420805 113388395621257944828901)
                ·
                  rfl

theorem cell19_372639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_372639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372639 prefixEnd_372639 := by exact prefixLift 372639
  have htrace : WordTrace (prefixWord ++ tailWord_372639) baseStart_372639 baseEnd_372639 := by
    simpa [prefixWord, tailWord_372639, baseEnd_372639] using wordTrace_append hprefix tailTrace_372639
  have hstable : (prefixWord ++ tailWord_372639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372639).length < 2 ^ (prefixWord ++ tailWord_372639).sum := by decide
  have hdescent : baseEnd_372639 < baseStart_372639 := by decide
  rcases family_descends (prefixWord ++ tailWord_372639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372719 : List Nat := [1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_372719 : Nat := 118140960795 + 372719 * 2 ^ 59
def prefixEnd_372719 : Nat := 4983230072969 + 3 ^ 40 * 372719 * 2
def baseEnd_372719 : Nat := 113412738407841463050905

theorem tailTrace_372719 : CollatzResearch.WordTrace tailWord_372719 prefixEnd_372719 113412738407841463050905 := by
  unfold tailWord_372719
  simp only [CollatzResearch.WordTrace]
  refine ⟨13594178736710193182449211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9062785824473462121632807 13594178736710193182449211)
  ·
    refine ⟨20391268105065289773673817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13594178736710193182449211 20391268105065289773673817)
    ·
      refine ⟨15293451078798967330255363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20391268105065289773673817 15293451078798967330255363)
      ·
        refine ⟨22940176618198450995383045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15293451078798967330255363 22940176618198450995383045)
        ·
          refine ⟨4301283115912209561634321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22940176618198450995383045 4301283115912209561634321)
          ·
            refine ⟨3225962336934157171225741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4301283115912209561634321 3225962336934157171225741)
            ·
              refine ⟨1209735876350308939209653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3225962336934157171225741 1209735876350308939209653)
              ·
                refine ⟨113412738407841463050905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1209735876350308939209653 113412738407841463050905)
                ·
                  rfl

theorem cell19_372719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_372719 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372719 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372719 prefixEnd_372719 := by exact prefixLift 372719
  have htrace : WordTrace (prefixWord ++ tailWord_372719) baseStart_372719 baseEnd_372719 := by
    simpa [prefixWord, tailWord_372719, baseEnd_372719] using wordTrace_append hprefix tailTrace_372719
  have hstable : (prefixWord ++ tailWord_372719).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372719).length < 2 ^ (prefixWord ++ tailWord_372719).sum := by decide
  have hdescent : baseEnd_372719 < baseStart_372719 := by decide
  rcases family_descends (prefixWord ++ tailWord_372719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372734 : List Nat := [4, 2, 2, 2, 1, 3, 5]
def baseStart_372734 : Nat := 118140960795 + 372734 * 2 ^ 59
def prefixEnd_372734 : Nat := 4983230072969 + 3 ^ 40 * 372734 * 2
def baseEnd_372734 : Nat := 37805767560108624239177

theorem tailTrace_372734 : CollatzResearch.WordTrace tailWord_372734 prefixEnd_372734 37805767560108624239177 := by
  unfold tailWord_372734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699340728956981343030657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9063150554437233829496837 1699340728956981343030657)
  ·
    refine ⟨1274505546717736007272993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1699340728956981343030657 1274505546717736007272993)
    ·
      refine ⟨955879160038302005454745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1274505546717736007272993 955879160038302005454745)
      ·
        refine ⟨716909370028726504091059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 955879160038302005454745 716909370028726504091059)
        ·
          refine ⟨1075364055043089756136589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716909370028726504091059 1075364055043089756136589)
          ·
            refine ⟨403261520641158658551221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1075364055043089756136589 403261520641158658551221)
            ·
              refine ⟨37805767560108624239177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 403261520641158658551221 37805767560108624239177)
              ·
                rfl

theorem cell19_372734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_372734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372734 prefixEnd_372734 := by exact prefixLift 372734
  have htrace : WordTrace (prefixWord ++ tailWord_372734) baseStart_372734 baseEnd_372734 := by
    simpa [prefixWord, tailWord_372734, baseEnd_372734] using wordTrace_append hprefix tailTrace_372734
  have hstable : (prefixWord ++ tailWord_372734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372734).length < 2 ^ (prefixWord ++ tailWord_372734).sum := by decide
  have hdescent : baseEnd_372734 < baseStart_372734 := by decide
  rcases family_descends (prefixWord ++ tailWord_372734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372749 : List Nat := [1, 7, 1, 2, 1, 1, 2, 4]
def baseStart_372749 : Nat := 118140960795 + 372749 * 2 ^ 59
def prefixEnd_372749 : Nat := 4983230072969 + 3 ^ 40 * 372749 * 2
def baseEnd_372749 : Nat := 113421866952810282384157

theorem tailTrace_372749 : CollatzResearch.WordTrace tailWord_372749 prefixEnd_372749 113421866952810282384157 := by
  unfold tailWord_372749
  simp only [CollatzResearch.WordTrace]
  refine ⟨13595272926601508306041301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9063515284401005537360867 13595272926601508306041301)
  ·
    refine ⟨318639209217222850922843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13595272926601508306041301 318639209217222850922843)
    ·
      refine ⟨477958813825834276384265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318639209217222850922843 477958813825834276384265)
      ·
        refine ⟨358469110369375707288199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477958813825834276384265 358469110369375707288199)
        ·
          refine ⟨537703665554063560932299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358469110369375707288199 537703665554063560932299)
          ·
            refine ⟨806555498331095341398449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537703665554063560932299 806555498331095341398449)
            ·
              refine ⟨604916623748321506048837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806555498331095341398449 604916623748321506048837)
              ·
                refine ⟨113421866952810282384157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 604916623748321506048837 113421866952810282384157)
                ·
                  rfl

theorem cell19_372749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 4].length) (baseStart_372749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372749 prefixEnd_372749 := by exact prefixLift 372749
  have htrace : WordTrace (prefixWord ++ tailWord_372749) baseStart_372749 baseEnd_372749 := by
    simpa [prefixWord, tailWord_372749, baseEnd_372749] using wordTrace_append hprefix tailTrace_372749
  have hstable : (prefixWord ++ tailWord_372749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372749).length < 2 ^ (prefixWord ++ tailWord_372749).sum := by decide
  have hdescent : baseEnd_372749 < baseStart_372749 := by decide
  rcases family_descends (prefixWord ++ tailWord_372749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372793 : List Nat := [1, 2, 1, 5, 4, 6]
def baseStart_372793 : Nat := 118140960795 + 372793 * 2 ^ 59
def prefixEnd_372793 : Nat := 4983230072969 + 3 ^ 40 * 372793 * 2
def baseEnd_372793 : Nat := 12603917276159024156251

theorem tailTrace_372793 : CollatzResearch.WordTrace tailWord_372793 prefixEnd_372793 12603917276159024156251 := by
  unfold tailWord_372793
  simp only [CollatzResearch.WordTrace]
  refine ⟨13596877738442103820643033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9064585158961402547095355 13596877738442103820643033)
  ·
    refine ⟨10197658303831577865482275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13596877738442103820643033 10197658303831577865482275)
    ·
      refine ⟨15296487455747366798223413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10197658303831577865482275 15296487455747366798223413)
      ·
        refine ⟨1434045698976315637333445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15296487455747366798223413 1434045698976315637333445)
        ·
          refine ⟨268883568558059182000021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1434045698976315637333445 268883568558059182000021)
          ·
            refine ⟨12603917276159024156251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 268883568558059182000021 12603917276159024156251)
            ·
              rfl

theorem cell19_372793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 6].length) (baseStart_372793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372793 prefixEnd_372793 := by exact prefixLift 372793
  have htrace : WordTrace (prefixWord ++ tailWord_372793) baseStart_372793 baseEnd_372793 := by
    simpa [prefixWord, tailWord_372793, baseEnd_372793] using wordTrace_append hprefix tailTrace_372793
  have hstable : (prefixWord ++ tailWord_372793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372793).length < 2 ^ (prefixWord ++ tailWord_372793).sum := by decide
  have hdescent : baseEnd_372793 < baseStart_372793 := by decide
  rcases family_descends (prefixWord ++ tailWord_372793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372888 : List Nat := [2, 1, 2, 4, 3, 1, 1, 5]
def baseStart_372888 : Nat := 118140960795 + 372888 * 2 ^ 59
def prefixEnd_372888 : Nat := 4983230072969 + 3 ^ 40 * 372888 * 2
def baseEnd_372888 : Nat := 113464162544499145294889

theorem tailTrace_372888 : CollatzResearch.WordTrace tailWord_372888 prefixEnd_372888 113464162544499145294889 := by
  unfold tailWord_372888
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800171336548967522675659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9066895115398623363567545 6800171336548967522675659)
  ·
    refine ⟨10200257004823451284013489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6800171336548967522675659 10200257004823451284013489)
    ·
      refine ⟨7650192753617588463010117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10200257004823451284013489 7650192753617588463010117)
      ·
        refine ⟨1434411141303297836814397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7650192753617588463010117 1434411141303297836814397)
        ·
          refine ⟨537904177988736688805399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1434411141303297836814397 537904177988736688805399)
          ·
            refine ⟨806856266983105033208099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537904177988736688805399 806856266983105033208099)
            ·
              refine ⟨1210284400474657549812149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806856266983105033208099 1210284400474657549812149)
              ·
                refine ⟨113464162544499145294889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1210284400474657549812149 113464162544499145294889)
                ·
                  rfl

theorem cell19_372888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_372888 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372888 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372888 prefixEnd_372888 := by exact prefixLift 372888
  have htrace : WordTrace (prefixWord ++ tailWord_372888) baseStart_372888 baseEnd_372888 := by
    simpa [prefixWord, tailWord_372888, baseEnd_372888] using wordTrace_append hprefix tailTrace_372888
  have hstable : (prefixWord ++ tailWord_372888).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372888).length < 2 ^ (prefixWord ++ tailWord_372888).sum := by decide
  have hdescent : baseEnd_372888 < baseStart_372888 := by decide
  rcases family_descends (prefixWord ++ tailWord_372888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372928 : List Nat := [2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_372928 : Nat := 118140960795 + 372928 * 2 ^ 59
def prefixEnd_372928 : Nat := 4983230072969 + 3 ^ 40 * 372928 * 2
def baseEnd_372928 : Nat := 113476333937790904405891

theorem tailTrace_372928 : CollatzResearch.WordTrace tailWord_372928 prefixEnd_372928 113476333937790904405891 := by
  unfold tailWord_372928
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800900796476510938403719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9067867728635347917871625 6800900796476510938403719)
  ·
    refine ⟨10201351194714766407605579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6800900796476510938403719 10201351194714766407605579)
    ·
      refine ⟨15302026792072149611408369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10201351194714766407605579 15302026792072149611408369)
      ·
        refine ⟨11476520094054112208556277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15302026792072149611408369 11476520094054112208556277)
        ·
          refine ⟨1075923758817573019552151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11476520094054112208556277 1075923758817573019552151)
          ·
            refine ⟨1613885638226359529328227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075923758817573019552151 1613885638226359529328227)
            ·
              refine ⟨2420828457339539293992341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613885638226359529328227 2420828457339539293992341)
              ·
                refine ⟨113476333937790904405891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2420828457339539293992341 113476333937790904405891)
                ·
                  rfl

theorem cell19_372928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_372928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372928 prefixEnd_372928 := by exact prefixLift 372928
  have htrace : WordTrace (prefixWord ++ tailWord_372928) baseStart_372928 baseEnd_372928 := by
    simpa [prefixWord, tailWord_372928, baseEnd_372928] using wordTrace_append hprefix tailTrace_372928
  have hstable : (prefixWord ++ tailWord_372928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372928).length < 2 ^ (prefixWord ++ tailWord_372928).sum := by decide
  have hdescent : baseEnd_372928 < baseStart_372928 := by decide
  rcases family_descends (prefixWord ++ tailWord_372928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372962 : List Nat := [3, 3, 4, 1, 8]
def baseStart_372962 : Nat := 118140960795 + 372962 * 2 ^ 59
def prefixEnd_372962 : Nat := 4983230072969 + 3 ^ 40 * 372962 * 2
def baseEnd_372962 : Nat := 4203210356373662950009

theorem tailTrace_372962 : CollatzResearch.WordTrace tailWord_372962 prefixEnd_372962 4203210356373662950009 := by
  unfold tailWord_372962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400760418707461420886285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9068694449886563789030093 3400760418707461420886285)
  ·
    refine ⟨1275285157015298032832357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3400760418707461420886285 1275285157015298032832357)
    ·
      refine ⟨239115966940368381156067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1275285157015298032832357 239115966940368381156067)
      ·
        refine ⟨358673950410552571734101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239115966940368381156067 358673950410552571734101)
        ·
          refine ⟨4203210356373662950009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 358673950410552571734101 4203210356373662950009)
          ·
            rfl

theorem cell19_372962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 8].length) (baseStart_372962 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_372962 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_372962 prefixEnd_372962 := by exact prefixLift 372962
  have htrace : WordTrace (prefixWord ++ tailWord_372962) baseStart_372962 baseEnd_372962 := by
    simpa [prefixWord, tailWord_372962, baseEnd_372962] using wordTrace_append hprefix tailTrace_372962
  have hstable : (prefixWord ++ tailWord_372962).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372962).length < 2 ^ (prefixWord ++ tailWord_372962).sum := by decide
  have hdescent : baseEnd_372962 < baseStart_372962 := by decide
  rcases family_descends (prefixWord ++ tailWord_372962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373021 : List Nat := [1, 4, 2, 3, 2, 1, 6]
def baseStart_373021 : Nat := 118140960795 + 373021 * 2 ^ 59
def prefixEnd_373021 : Nat := 4983230072969 + 3 ^ 40 * 373021 * 2
def baseEnd_373021 : Nat := 37834877475731414779657

theorem tailTrace_373021 : CollatzResearch.WordTrace tailWord_373021 prefixEnd_373021 37834877475731414779657 := by
  unfold tailWord_373021
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605193581616098759942917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9070129054410732506628611 13605193581616098759942917)
  ·
    refine ⟨2550973796553018517489297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13605193581616098759942917 2550973796553018517489297)
    ·
      refine ⟨1913230347414763888116973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2550973796553018517489297 1913230347414763888116973)
      ·
        refine ⟨717461380280536458043865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1913230347414763888116973 717461380280536458043865)
        ·
          refine ⟨538096035210402343532899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717461380280536458043865 538096035210402343532899)
          ·
            refine ⟨807144052815603515299349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538096035210402343532899 807144052815603515299349)
            ·
              refine ⟨37834877475731414779657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 807144052815603515299349 37834877475731414779657)
              ·
                rfl

theorem cell19_373021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_373021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373021 prefixEnd_373021 := by exact prefixLift 373021
  have htrace : WordTrace (prefixWord ++ tailWord_373021) baseStart_373021 baseEnd_373021 := by
    simpa [prefixWord, tailWord_373021, baseEnd_373021] using wordTrace_append hprefix tailTrace_373021
  have hstable : (prefixWord ++ tailWord_373021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373021).length < 2 ^ (prefixWord ++ tailWord_373021).sum := by decide
  have hdescent : baseEnd_373021 < baseStart_373021 := by decide
  rcases family_descends (prefixWord ++ tailWord_373021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373023 : List Nat := [1, 1, 2, 4, 3, 2, 6]
def baseStart_373023 : Nat := 118140960795 + 373023 * 2 ^ 59
def prefixEnd_373023 : Nat := 4983230072969 + 3 ^ 40 * 373023 * 2
def baseEnd_373023 : Nat := 37835080332286277431507

theorem tailTrace_373023 : CollatzResearch.WordTrace tailWord_373023 prefixEnd_373023 37835080332286277431507 := by
  unfold tailWord_373023
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605266527608853101515723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9070177685072568734343815 13605266527608853101515723)
  ·
    refine ⟨20407899791413279652273585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13605266527608853101515723 20407899791413279652273585)
    ·
      refine ⟨15305924843559959739205189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20407899791413279652273585 15305924843559959739205189)
      ·
        refine ⟨2869860908167492451100973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15305924843559959739205189 2869860908167492451100973)
        ·
          refine ⟨1076197840562809669162865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2869860908167492451100973 1076197840562809669162865)
          ·
            refine ⟨807148380422107251872149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1076197840562809669162865 807148380422107251872149)
            ·
              refine ⟨37835080332286277431507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 807148380422107251872149 37835080332286277431507)
              ·
                rfl

theorem cell19_373023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_373023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373023 prefixEnd_373023 := by exact prefixLift 373023
  have htrace : WordTrace (prefixWord ++ tailWord_373023) baseStart_373023 baseEnd_373023 := by
    simpa [prefixWord, tailWord_373023, baseEnd_373023] using wordTrace_append hprefix tailTrace_373023
  have hstable : (prefixWord ++ tailWord_373023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373023).length < 2 ^ (prefixWord ++ tailWord_373023).sum := by decide
  have hdescent : baseEnd_373023 < baseStart_373023 := by decide
  rcases family_descends (prefixWord ++ tailWord_373023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373156 : List Nat := [2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_373156 : Nat := 118140960795 + 373156 * 2 ^ 59
def prefixEnd_373156 : Nat := 4983230072969 + 3 ^ 40 * 373156 * 2
def baseEnd_373156 : Nat := 113545710879553931338603

theorem tailTrace_373156 : CollatzResearch.WordTrace tailWord_373156 prefixEnd_373156 113545710879553931338603 := by
  unfold tailWord_373156
  simp only [CollatzResearch.WordTrace]
  refine ⟨6805058718063508408053661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9073411624084677877404881 6805058718063508408053661)
  ·
    refine ⟨2551897019273815653020123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6805058718063508408053661 2551897019273815653020123)
    ·
      refine ⟨3827845528910723479530185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551897019273815653020123 3827845528910723479530185)
      ·
        refine ⟨2870884146683042609647639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3827845528910723479530185 2870884146683042609647639)
        ·
          refine ⟨4306326220024563914471459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870884146683042609647639 4306326220024563914471459)
          ·
            refine ⟨6459489330036845871707189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4306326220024563914471459 6459489330036845871707189)
            ·
              refine ⟨605577124690954300472549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6459489330036845871707189 605577124690954300472549)
              ·
                refine ⟨113545710879553931338603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 605577124690954300472549 113545710879553931338603)
                ·
                  rfl

theorem cell19_373156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_373156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373156 prefixEnd_373156 := by exact prefixLift 373156
  have htrace : WordTrace (prefixWord ++ tailWord_373156) baseStart_373156 baseEnd_373156 := by
    simpa [prefixWord, tailWord_373156, baseEnd_373156] using wordTrace_append hprefix tailTrace_373156
  have hstable : (prefixWord ++ tailWord_373156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373156).length < 2 ^ (prefixWord ++ tailWord_373156).sum := by decide
  have hdescent : baseEnd_373156 < baseStart_373156 := by decide
  rcases family_descends (prefixWord ++ tailWord_373156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373213 : List Nat := [1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_373213 : Nat := 118140960795 + 373213 * 2 ^ 59
def prefixEnd_373213 : Nat := 4983230072969 + 3 ^ 40 * 373213 * 2
def baseEnd_373213 : Nat := 113563055114994688071781

theorem tailTrace_373213 : CollatzResearch.WordTrace tailWord_373213 prefixEnd_373213 113563055114994688071781 := by
  unfold tailWord_373213
  simp only [CollatzResearch.WordTrace]
  refine ⟨13612196396920515550932293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9074797597947010367288195 13612196396920515550932293)
  ·
    refine ⟨2552286824422596665799805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13612196396920515550932293 2552286824422596665799805)
    ·
      refine ⟨957107559158473749674927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2552286824422596665799805 957107559158473749674927)
      ·
        refine ⟨1435661338737710624512391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957107559158473749674927 1435661338737710624512391)
        ·
          refine ⟨2153492008106565936768587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435661338737710624512391 2153492008106565936768587)
          ·
            refine ⟨3230238012159848905152881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153492008106565936768587 3230238012159848905152881)
            ·
              refine ⟨2422678509119886678864661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3230238012159848905152881 2422678509119886678864661)
              ·
                refine ⟨113563055114994688071781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2422678509119886678864661 113563055114994688071781)
                ·
                  rfl

theorem cell19_373213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_373213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373213 prefixEnd_373213 := by exact prefixLift 373213
  have htrace : WordTrace (prefixWord ++ tailWord_373213) baseStart_373213 baseEnd_373213 := by
    simpa [prefixWord, tailWord_373213, baseEnd_373213] using wordTrace_append hprefix tailTrace_373213
  have hstable : (prefixWord ++ tailWord_373213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373213).length < 2 ^ (prefixWord ++ tailWord_373213).sum := by decide
  have hdescent : baseEnd_373213 < baseStart_373213 := by decide
  rcases family_descends (prefixWord ++ tailWord_373213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373230 : List Nat := [4, 1, 2, 1, 2, 2, 4, 3]
def baseStart_373230 : Nat := 118140960795 + 373230 * 2 ^ 59
def prefixEnd_373230 : Nat := 4983230072969 + 3 ^ 40 * 373230 * 2
def baseEnd_373230 : Nat := 113568227957143685693957

theorem tailTrace_373230 : CollatzResearch.WordTrace tailWord_373230 prefixEnd_373230 113568227957143685693957 := by
  unfold tailWord_373230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701602054732365931787643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9075210958572618302867429 1701602054732365931787643)
  ·
    refine ⟨2552403082098548897681465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1701602054732365931787643 2552403082098548897681465)
    ·
      refine ⟨1914302311573911673261099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2552403082098548897681465 1914302311573911673261099)
      ·
        refine ⟨2871453467360867509891649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914302311573911673261099 2871453467360867509891649)
        ·
          refine ⟨2153590100520650632418737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2871453467360867509891649 2153590100520650632418737)
          ·
            refine ⟨1615192575390487974314053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153590100520650632418737 1615192575390487974314053)
            ·
              refine ⟨302848607885716495183885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1615192575390487974314053 302848607885716495183885)
              ·
                refine ⟨113568227957143685693957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302848607885716495183885 113568227957143685693957)
                ·
                  rfl

theorem cell19_373230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_373230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373230 prefixEnd_373230 := by exact prefixLift 373230
  have htrace : WordTrace (prefixWord ++ tailWord_373230) baseStart_373230 baseEnd_373230 := by
    simpa [prefixWord, tailWord_373230, baseEnd_373230] using wordTrace_append hprefix tailTrace_373230
  have hstable : (prefixWord ++ tailWord_373230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373230).length < 2 ^ (prefixWord ++ tailWord_373230).sum := by decide
  have hdescent : baseEnd_373230 < baseStart_373230 := by decide
  rcases family_descends (prefixWord ++ tailWord_373230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373253 : List Nat := [1, 3, 1, 1, 2, 2, 9]
def baseStart_373253 : Nat := 118140960795 + 373253 * 2 ^ 59
def prefixEnd_373253 : Nat := 4983230072969 + 3 ^ 40 * 373253 * 2
def baseEnd_373253 : Nat := 37858408836095482394261

theorem tailTrace_373253 : CollatzResearch.WordTrace tailWord_373253 prefixEnd_373253 37858408836095482394261 := by
  unfold tailWord_373253
  simp only [CollatzResearch.WordTrace]
  refine ⟨13613655316775602382388413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9075770211183734921592275 13613655316775602382388413)
  ·
    refine ⟨5105120743790850893395655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13613655316775602382388413 5105120743790850893395655)
    ·
      refine ⟨7657681115686276340093483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5105120743790850893395655 7657681115686276340093483)
      ·
        refine ⟨11486521673529414510140225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7657681115686276340093483 11486521673529414510140225)
        ·
          refine ⟨8614891255147060882605169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11486521673529414510140225 8614891255147060882605169)
          ·
            refine ⟨6461168441360295661953877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8614891255147060882605169 6461168441360295661953877)
            ·
              refine ⟨37858408836095482394261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6461168441360295661953877 37858408836095482394261)
              ·
                rfl

theorem cell19_373253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_373253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373253 prefixEnd_373253 := by exact prefixLift 373253
  have htrace : WordTrace (prefixWord ++ tailWord_373253) baseStart_373253 baseEnd_373253 := by
    simpa [prefixWord, tailWord_373253, baseEnd_373253] using wordTrace_append hprefix tailTrace_373253
  have hstable : (prefixWord ++ tailWord_373253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373253).length < 2 ^ (prefixWord ++ tailWord_373253).sum := by decide
  have hdescent : baseEnd_373253 < baseStart_373253 := by decide
  rcases family_descends (prefixWord ++ tailWord_373253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373268 : List Nat := [2, 4, 3, 1, 1, 1, 1, 6]
def baseStart_373268 : Nat := 118140960795 + 373268 * 2 ^ 59
def prefixEnd_373268 : Nat := 4983230072969 + 3 ^ 40 * 373268 * 2
def baseEnd_373268 : Nat := 113579790780770856849409

theorem tailTrace_373268 : CollatzResearch.WordTrace tailWord_373268 prefixEnd_373268 113579790780770856849409 := by
  unfold tailWord_373268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6807101205860629972092229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9076134941147506629456305 6807101205860629972092229)
  ·
    refine ⟨1276331476098868119767293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6807101205860629972092229 1276331476098868119767293)
    ·
      refine ⟨478624303537075544912735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1276331476098868119767293 478624303537075544912735)
      ·
        refine ⟨717936455305613317369103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478624303537075544912735 717936455305613317369103)
        ·
          refine ⟨1076904682958419976053655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717936455305613317369103 1076904682958419976053655)
          ·
            refine ⟨1615357024437629964080483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076904682958419976053655 1615357024437629964080483)
            ·
              refine ⟨2423035536656444946120725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615357024437629964080483 2423035536656444946120725)
              ·
                refine ⟨113579790780770856849409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2423035536656444946120725 113579790780770856849409)
                ·
                  rfl

theorem cell19_373268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_373268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373268 prefixEnd_373268 := by exact prefixLift 373268
  have htrace : WordTrace (prefixWord ++ tailWord_373268) baseStart_373268 baseEnd_373268 := by
    simpa [prefixWord, tailWord_373268, baseEnd_373268] using wordTrace_append hprefix tailTrace_373268
  have hstable : (prefixWord ++ tailWord_373268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373268).length < 2 ^ (prefixWord ++ tailWord_373268).sum := by decide
  have hdescent : baseEnd_373268 < baseStart_373268 := by decide
  rcases family_descends (prefixWord ++ tailWord_373268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373325 : List Nat := [1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_373325 : Nat := 118140960795 + 373325 * 2 ^ 59
def prefixEnd_373325 : Nat := 4983230072969 + 3 ^ 40 * 373325 * 2
def baseEnd_373325 : Nat := 113597135016211613582587

theorem tailTrace_373325 : CollatzResearch.WordTrace tailWord_373325 prefixEnd_373325 113597135016211613582587 := by
  unfold tailWord_373325
  simp only [CollatzResearch.WordTrace]
  refine ⟨13616281372514758679009429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9077520915009839119339619 13616281372514758679009429)
  ·
    refine ⟨638263189336629313078567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13616281372514758679009429 638263189336629313078567)
    ·
      refine ⟨957394784004943969617851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638263189336629313078567 957394784004943969617851)
      ·
        refine ⟨1436092176007415954426777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957394784004943969617851 1436092176007415954426777)
        ·
          refine ⟨1077069132005561965820083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1436092176007415954426777 1077069132005561965820083)
          ·
            refine ⟨1615603698008342948730125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077069132005561965820083 1615603698008342948730125)
            ·
              refine ⟨605851386753128605773797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1615603698008342948730125 605851386753128605773797)
              ·
                refine ⟨113597135016211613582587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 605851386753128605773797 113597135016211613582587)
                ·
                  rfl

theorem cell19_373325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_373325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373325 prefixEnd_373325 := by exact prefixLift 373325
  have htrace : WordTrace (prefixWord ++ tailWord_373325) baseStart_373325 baseEnd_373325 := by
    simpa [prefixWord, tailWord_373325, baseEnd_373325] using wordTrace_append hprefix tailTrace_373325
  have hstable : (prefixWord ++ tailWord_373325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373325).length < 2 ^ (prefixWord ++ tailWord_373325).sum := by decide
  have hdescent : baseEnd_373325 < baseStart_373325 := by decide
  rcases family_descends (prefixWord ++ tailWord_373325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373418 : List Nat := [3, 1, 5, 2, 1, 2, 5]
def baseStart_373418 : Nat := 118140960795 + 373418 * 2 ^ 59
def prefixEnd_373418 : Nat := 4983230072969 + 3 ^ 40 * 373418 * 2
def baseEnd_373418 : Nat := 37875144501871651171889

theorem tailTrace_373418 : CollatzResearch.WordTrace tailWord_373418 prefixEnd_373418 37875144501871651171889 := by
  unfold tailWord_373418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3404918340294458890536227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9079782240785223708096605 3404918340294458890536227)
  ·
    refine ⟨5107377510441688335804341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3404918340294458890536227 5107377510441688335804341)
    ·
      refine ⟨478816641603908281481657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5107377510441688335804341 478816641603908281481657)
      ·
        refine ⟨359112481202931211111243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478816641603908281481657 359112481202931211111243)
        ·
          refine ⟨538668721804396816666865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359112481202931211111243 538668721804396816666865)
          ·
            refine ⟨404001541353297612500149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538668721804396816666865 404001541353297612500149)
            ·
              refine ⟨37875144501871651171889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 404001541353297612500149 37875144501871651171889)
              ·
                rfl

theorem cell19_373418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 5].length) (baseStart_373418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373418 prefixEnd_373418 := by exact prefixLift 373418
  have htrace : WordTrace (prefixWord ++ tailWord_373418) baseStart_373418 baseEnd_373418 := by
    simpa [prefixWord, tailWord_373418, baseEnd_373418] using wordTrace_append hprefix tailTrace_373418
  have hstable : (prefixWord ++ tailWord_373418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373418).length < 2 ^ (prefixWord ++ tailWord_373418).sum := by decide
  have hdescent : baseEnd_373418 < baseStart_373418 := by decide
  rcases family_descends (prefixWord ++ tailWord_373418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373492 : List Nat := [2, 6, 1, 1, 2, 2, 1, 4]
def baseStart_373492 : Nat := 118140960795 + 373492 * 2 ^ 59
def prefixEnd_373492 : Nat := 4983230072969 + 3 ^ 40 * 373492 * 2
def baseEnd_373492 : Nat := 113647950583204707871021

theorem tailTrace_373492 : CollatzResearch.WordTrace tailWord_373492 prefixEnd_373492 113647950583204707871021 := by
  unfold tailWord_373492
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811186181454873100169365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9081581575273164133559153 6811186181454873100169365)
  ·
    refine ⟨319274352255697176570439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6811186181454873100169365 319274352255697176570439)
    ·
      refine ⟨478911528383545764855659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319274352255697176570439 478911528383545764855659)
      ·
        refine ⟨718367292575318647283489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478911528383545764855659 718367292575318647283489)
        ·
          refine ⟨538775469431488985462617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718367292575318647283489 538775469431488985462617)
          ·
            refine ⟨404081602073616739096963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538775469431488985462617 404081602073616739096963)
            ·
              refine ⟨606122403110425108645445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404081602073616739096963 606122403110425108645445)
              ·
                refine ⟨113647950583204707871021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606122403110425108645445 113647950583204707871021)
                ·
                  rfl

theorem cell19_373492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_373492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373492 prefixEnd_373492 := by exact prefixLift 373492
  have htrace : WordTrace (prefixWord ++ tailWord_373492) baseStart_373492 baseEnd_373492 := by
    simpa [prefixWord, tailWord_373492, baseEnd_373492] using wordTrace_append hprefix tailTrace_373492
  have hstable : (prefixWord ++ tailWord_373492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373492).length < 2 ^ (prefixWord ++ tailWord_373492).sum := by decide
  have hdescent : baseEnd_373492 < baseStart_373492 := by decide
  rcases family_descends (prefixWord ++ tailWord_373492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373576 : List Nat := [2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_373576 : Nat := 118140960795 + 373576 * 2 ^ 59
def prefixEnd_373576 : Nat := 4983230072969 + 3 ^ 40 * 373576 * 2
def baseEnd_373576 : Nat := 113673510509117402004125

theorem tailTrace_373576 : CollatzResearch.WordTrace tailWord_373576 prefixEnd_373576 113673510509117402004125 := by
  unfold tailWord_373576
  simp only [CollatzResearch.WordTrace]
  refine ⟨6812718047302714273198291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9083624063070285697597721 6812718047302714273198291)
  ·
    refine ⟨10219077070954071409797437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6812718047302714273198291 10219077070954071409797437)
    ·
      refine ⟨3832153901607776778674039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10219077070954071409797437 3832153901607776778674039)
      ·
        refine ⟨5748230852411665168011059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3832153901607776778674039 5748230852411665168011059)
        ·
          refine ⟨8622346278617497752016589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5748230852411665168011059 8622346278617497752016589)
          ·
            refine ⟨3233379854481561657006221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8622346278617497752016589 3233379854481561657006221)
            ·
              refine ⟨1212517445430585621377333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3233379854481561657006221 1212517445430585621377333)
              ·
                refine ⟨113673510509117402004125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1212517445430585621377333 113673510509117402004125)
                ·
                  rfl

theorem cell19_373576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_373576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373576 prefixEnd_373576 := by exact prefixLift 373576
  have htrace : WordTrace (prefixWord ++ tailWord_373576) baseStart_373576 baseEnd_373576 := by
    simpa [prefixWord, tailWord_373576, baseEnd_373576] using wordTrace_append hprefix tailTrace_373576
  have hstable : (prefixWord ++ tailWord_373576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373576).length < 2 ^ (prefixWord ++ tailWord_373576).sum := by decide
  have hdescent : baseEnd_373576 < baseStart_373576 := by decide
  rcases family_descends (prefixWord ++ tailWord_373576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373650 : List Nat := [3, 2, 3, 2, 2, 7]
def baseStart_373650 : Nat := 118140960795 + 373650 * 2 ^ 59
def prefixEnd_373650 : Nat := 4983230072969 + 3 ^ 40 * 373650 * 2
def baseEnd_373650 : Nat := 12632891954078572928831

theorem tailTrace_373650 : CollatzResearch.WordTrace tailWord_373650 prefixEnd_373650 12632891954078572928831 := by
  unfold tailWord_373650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3407033774084334796147601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9085423397558226123060269 3407033774084334796147601)
  ·
    refine ⟨2555275330563251097110701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3407033774084334796147601 2555275330563251097110701)
    ·
      refine ⟨958228248961219161416513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2555275330563251097110701 958228248961219161416513)
      ·
        refine ⟨718671186720914371062385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 958228248961219161416513 718671186720914371062385)
        ·
          refine ⟨539003390040685778296789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718671186720914371062385 539003390040685778296789)
          ·
            refine ⟨12632891954078572928831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 539003390040685778296789 12632891954078572928831)
            ·
              rfl

theorem cell19_373650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 7].length) (baseStart_373650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373650 prefixEnd_373650 := by exact prefixLift 373650
  have htrace : WordTrace (prefixWord ++ tailWord_373650) baseStart_373650 baseEnd_373650 := by
    simpa [prefixWord, tailWord_373650, baseEnd_373650] using wordTrace_append hprefix tailTrace_373650
  have hstable : (prefixWord ++ tailWord_373650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373650).length < 2 ^ (prefixWord ++ tailWord_373650).sum := by decide
  have hdescent : baseEnd_373650 < baseStart_373650 := by decide
  rcases family_descends (prefixWord ++ tailWord_373650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373684 : List Nat := [2, 5, 2, 1, 1, 2, 3, 3]
def baseStart_373684 : Nat := 118140960795 + 373684 * 2 ^ 59
def prefixEnd_373684 : Nat := 4983230072969 + 3 ^ 40 * 373684 * 2
def baseEnd_373684 : Nat := 113706373271005151603831

theorem tailTrace_373684 : CollatzResearch.WordTrace tailWord_373684 prefixEnd_373684 113706373271005151603831 := by
  unfold tailWord_373684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6814687589107081495664053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9086250118809441994218737 6814687589107081495664053)
  ·
    refine ⟨638876961478788890218505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6814687589107081495664053 638876961478788890218505)
    ·
      refine ⟨479157721109091667663879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 638876961478788890218505 479157721109091667663879)
      ·
        refine ⟨718736581663637501495819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479157721109091667663879 718736581663637501495819)
        ·
          refine ⟨1078104872495456252243729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718736581663637501495819 1078104872495456252243729)
          ·
            refine ⟨808578654371592189182797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1078104872495456252243729 808578654371592189182797)
            ·
              refine ⟨303216995389347070943549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 808578654371592189182797 303216995389347070943549)
              ·
                refine ⟨113706373271005151603831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303216995389347070943549 113706373271005151603831)
                ·
                  rfl

theorem cell19_373684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_373684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373684 prefixEnd_373684 := by exact prefixLift 373684
  have htrace : WordTrace (prefixWord ++ tailWord_373684) baseStart_373684 baseEnd_373684 := by
    simpa [prefixWord, tailWord_373684, baseEnd_373684] using wordTrace_append hprefix tailTrace_373684
  have hstable : (prefixWord ++ tailWord_373684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373684).length < 2 ^ (prefixWord ++ tailWord_373684).sum := by decide
  have hdescent : baseEnd_373684 < baseStart_373684 := by decide
  rcases family_descends (prefixWord ++ tailWord_373684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373688 : List Nat := [2, 1, 2, 1, 2, 5, 3, 3]
def baseStart_373688 : Nat := 118140960795 + 373688 * 2 ^ 59
def prefixEnd_373688 : Nat := 4983230072969 + 3 ^ 40 * 373688 * 2
def baseEnd_373688 : Nat := 113707590410334327514931

theorem tailTrace_373688 : CollatzResearch.WordTrace tailWord_373688 prefixEnd_373688 113707590410334327514931 := by
  unfold tailWord_373688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6814760535099835837236859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9086347380133114449649145 6814760535099835837236859)
  ·
    refine ⟨10222140802649753755855289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6814760535099835837236859 10222140802649753755855289)
    ·
      refine ⟨7666605601987315316891467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10222140802649753755855289 7666605601987315316891467)
      ·
        refine ⟨11499908402980972975337201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7666605601987315316891467 11499908402980972975337201)
        ·
          refine ⟨8624931302235729731502901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11499908402980972975337201 8624931302235729731502901)
          ·
            refine ⟨808587309584599662328397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8624931302235729731502901 808587309584599662328397)
            ·
              refine ⟨303220241094224873373149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 808587309584599662328397 303220241094224873373149)
              ·
                refine ⟨113707590410334327514931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303220241094224873373149 113707590410334327514931)
                ·
                  rfl

theorem cell19_373688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_373688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373688 prefixEnd_373688 := by exact prefixLift 373688
  have htrace : WordTrace (prefixWord ++ tailWord_373688) baseStart_373688 baseEnd_373688 := by
    simpa [prefixWord, tailWord_373688, baseEnd_373688] using wordTrace_append hprefix tailTrace_373688
  have hstable : (prefixWord ++ tailWord_373688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373688).length < 2 ^ (prefixWord ++ tailWord_373688).sum := by decide
  have hdescent : baseEnd_373688 < baseStart_373688 := by decide
  rcases family_descends (prefixWord ++ tailWord_373688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373745 : List Nat := [1, 2, 2, 2, 4, 1, 4, 3]
def baseStart_373745 : Nat := 118140960795 + 373745 * 2 ^ 59
def prefixEnd_373745 : Nat := 4983230072969 + 3 ^ 40 * 373745 * 2
def baseEnd_373745 : Nat := 113724934645775084248109

theorem tailTrace_373745 : CollatzResearch.WordTrace tailWord_373745 prefixEnd_373745 113724934645775084248109 := by
  unfold tailWord_373745
  simp only [CollatzResearch.WordTrace]
  refine ⟨13631600030993170409298689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9087733353995446939532459 13631600030993170409298689)
  ·
    refine ⟨10223700023244877806974017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13631600030993170409298689 10223700023244877806974017)
    ·
      refine ⟨7667775017433658355230513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10223700023244877806974017 7667775017433658355230513)
      ·
        refine ⟨5750831263075243766422885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7667775017433658355230513 5750831263075243766422885)
        ·
          refine ⟨1078280861826608206204291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5750831263075243766422885 1078280861826608206204291)
          ·
            refine ⟨1617421292739912309306437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078280861826608206204291 1617421292739912309306437)
            ·
              refine ⟨303266492388733557994957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1617421292739912309306437 303266492388733557994957)
              ·
                refine ⟨113724934645775084248109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303266492388733557994957 113724934645775084248109)
                ·
                  rfl

theorem cell19_373745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 3].length) (baseStart_373745 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373745 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373745 prefixEnd_373745 := by exact prefixLift 373745
  have htrace : WordTrace (prefixWord ++ tailWord_373745) baseStart_373745 baseEnd_373745 := by
    simpa [prefixWord, tailWord_373745, baseEnd_373745] using wordTrace_append hprefix tailTrace_373745
  have hstable : (prefixWord ++ tailWord_373745).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373745).length < 2 ^ (prefixWord ++ tailWord_373745).sum := by decide
  have hdescent : baseEnd_373745 < baseStart_373745 := by decide
  rcases family_descends (prefixWord ++ tailWord_373745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373783 : List Nat := [1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_373783 : Nat := 118140960795 + 373783 * 2 ^ 59
def prefixEnd_373783 : Nat := 4983230072969 + 3 ^ 40 * 373783 * 2
def baseEnd_373783 : Nat := 113736497469402255403561

theorem tailTrace_373783 : CollatzResearch.WordTrace tailWord_373783 prefixEnd_373783 113736497469402255403561 := by
  unfold tailWord_373783
  simp only [CollatzResearch.WordTrace]
  refine ⟨13632986004855502899182003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9088657336570335266121335 13632986004855502899182003)
  ·
    refine ⟨20449479007283254348773005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13632986004855502899182003 20449479007283254348773005)
    ·
      refine ⟨7668554627731220380789877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20449479007283254348773005 7668554627731220380789877)
      ·
        refine ⟨718926996349801910699051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7668554627731220380789877 718926996349801910699051)
        ·
          refine ⟨1078390494524702866048577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718926996349801910699051 1078390494524702866048577)
          ·
            refine ⟨808792870893527149536433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1078390494524702866048577 808792870893527149536433)
            ·
              refine ⟨606594653170145362152325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808792870893527149536433 606594653170145362152325)
              ·
                refine ⟨113736497469402255403561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606594653170145362152325 113736497469402255403561)
                ·
                  rfl

theorem cell19_373783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_373783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373783 prefixEnd_373783 := by exact prefixLift 373783
  have htrace : WordTrace (prefixWord ++ tailWord_373783) baseStart_373783 baseEnd_373783 := by
    simpa [prefixWord, tailWord_373783, baseEnd_373783] using wordTrace_append hprefix tailTrace_373783
  have hstable : (prefixWord ++ tailWord_373783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373783).length < 2 ^ (prefixWord ++ tailWord_373783).sum := by decide
  have hdescent : baseEnd_373783 < baseStart_373783 := by decide
  rcases family_descends (prefixWord ++ tailWord_373783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373914 : List Nat := [3, 1, 1, 5, 1, 3, 2, 3]
def baseStart_373914 : Nat := 118140960795 + 373914 * 2 ^ 59
def prefixEnd_373914 : Nat := 4983230072969 + 3 ^ 40 * 373914 * 2
def baseEnd_373914 : Nat := 113776358782432766492093

theorem tailTrace_373914 : CollatzResearch.WordTrace tailWord_373914 prefixEnd_373914 113776358782432766492093 := by
  unfold tailWord_373914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3409440991845228068050199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9091842644920608181467197 3409440991845228068050199)
  ·
    refine ⟨5114161487767842102075299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3409440991845228068050199 5114161487767842102075299)
    ·
      refine ⟨7671242231651763153112949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5114161487767842102075299 7671242231651763153112949)
      ·
        refine ⟨719178959217352795604339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7671242231651763153112949 719178959217352795604339)
        ·
          refine ⟨1078768438826029193406509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719178959217352795604339 1078768438826029193406509)
          ·
            refine ⟨404538164559760947527441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1078768438826029193406509 404538164559760947527441)
            ·
              refine ⟨303403623419820710645581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404538164559760947527441 303403623419820710645581)
              ·
                refine ⟨113776358782432766492093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303403623419820710645581 113776358782432766492093)
                ·
                  rfl

theorem cell19_373914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_373914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373914 prefixEnd_373914 := by exact prefixLift 373914
  have htrace : WordTrace (prefixWord ++ tailWord_373914) baseStart_373914 baseEnd_373914 := by
    simpa [prefixWord, tailWord_373914, baseEnd_373914] using wordTrace_append hprefix tailTrace_373914
  have hstable : (prefixWord ++ tailWord_373914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373914).length < 2 ^ (prefixWord ++ tailWord_373914).sum := by decide
  have hdescent : baseEnd_373914 < baseStart_373914 := by decide
  rcases family_descends (prefixWord ++ tailWord_373914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373916 : List Nat := [2, 2, 3, 2, 1, 2, 4, 3]
def baseStart_373916 : Nat := 118140960795 + 373916 * 2 ^ 59
def prefixEnd_373916 : Nat := 4983230072969 + 3 ^ 40 * 373916 * 2
def baseEnd_373916 : Nat := 113776967352097354447643

theorem tailTrace_373916 : CollatzResearch.WordTrace tailWord_373916 prefixEnd_373916 113776967352097354447643 := by
  unfold tailWord_373916
  simp only [CollatzResearch.WordTrace]
  refine ⟨6818918456686833306886801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9091891275582444409182401 6818918456686833306886801)
  ·
    refine ⟨5114188842515124980165101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6818918456686833306886801 5114188842515124980165101)
    ·
      refine ⟨1917820815943171867561913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5114188842515124980165101 1917820815943171867561913)
      ·
        refine ⟨1438365611957378900671435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1917820815943171867561913 1438365611957378900671435)
        ·
          refine ⟨2157548417936068351007153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438365611957378900671435 2157548417936068351007153)
          ·
            refine ⟨1618161313452051263255365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2157548417936068351007153 1618161313452051263255365)
            ·
              refine ⟨303405246272259611860381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1618161313452051263255365 303405246272259611860381)
              ·
                refine ⟨113776967352097354447643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303405246272259611860381 113776967352097354447643)
                ·
                  rfl

theorem cell19_373916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_373916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373916 prefixEnd_373916 := by exact prefixLift 373916
  have htrace : WordTrace (prefixWord ++ tailWord_373916) baseStart_373916 baseEnd_373916 := by
    simpa [prefixWord, tailWord_373916, baseEnd_373916] using wordTrace_append hprefix tailTrace_373916
  have hstable : (prefixWord ++ tailWord_373916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373916).length < 2 ^ (prefixWord ++ tailWord_373916).sum := by decide
  have hdescent : baseEnd_373916 < baseStart_373916 := by decide
  rcases family_descends (prefixWord ++ tailWord_373916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373933 : List Nat := [1, 5, 2, 1, 4, 1, 5]
def baseStart_373933 : Nat := 118140960795 + 373933 * 2 ^ 59
def prefixEnd_373933 : Nat := 4983230072969 + 3 ^ 40 * 373933 * 2
def baseEnd_373933 : Nat := 37927380064748784023273

theorem tailTrace_373933 : CollatzResearch.WordTrace tailWord_373933 prefixEnd_373933 37927380064748784023273 := by
  unfold tailWord_373933
  simp only [CollatzResearch.WordTrace]
  refine ⟨13638456954312078517142453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9092304636208052344761635 13638456954312078517142453)
  ·
    refine ⟨1278605339466757360982105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13638456954312078517142453 1278605339466757360982105)
    ·
      refine ⟨958954004600068020736579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1278605339466757360982105 958954004600068020736579)
      ·
        refine ⟨1438431006900102031104869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958954004600068020736579 1438431006900102031104869)
        ·
          refine ⟨269705813793769130832163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1438431006900102031104869 269705813793769130832163)
          ·
            refine ⟨404558720690653696248245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269705813793769130832163 404558720690653696248245)
            ·
              refine ⟨37927380064748784023273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 404558720690653696248245 37927380064748784023273)
              ·
                rfl

theorem cell19_373933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 5].length) (baseStart_373933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373933 prefixEnd_373933 := by exact prefixLift 373933
  have htrace : WordTrace (prefixWord ++ tailWord_373933) baseStart_373933 baseEnd_373933 := by
    simpa [prefixWord, tailWord_373933, baseEnd_373933] using wordTrace_append hprefix tailTrace_373933
  have hstable : (prefixWord ++ tailWord_373933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373933).length < 2 ^ (prefixWord ++ tailWord_373933).sum := by decide
  have hdescent : baseEnd_373933 < baseStart_373933 := by decide
  rcases family_descends (prefixWord ++ tailWord_373933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373937 : List Nat := [1, 2, 2, 5, 1, 1, 7]
def baseStart_373937 : Nat := 118140960795 + 373937 * 2 ^ 59
def prefixEnd_373937 : Nat := 4983230072969 + 3 ^ 40 * 373937 * 2
def baseEnd_373937 : Nat := 37927785777858509326973

theorem tailTrace_373937 : CollatzResearch.WordTrace tailWord_373937 prefixEnd_373937 37927785777858509326973 := by
  unfold tailWord_373937
  simp only [CollatzResearch.WordTrace]
  refine ⟨13638602846297587200288065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9092401897531724800192043 13638602846297587200288065)
  ·
    refine ⟨10228952134723190400216049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13638602846297587200288065 10228952134723190400216049)
    ·
      refine ⟨7671714101042392800162037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10228952134723190400216049 7671714101042392800162037)
      ·
        refine ⟨719223196972724325015191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7671714101042392800162037 719223196972724325015191)
        ·
          refine ⟨1078834795459086487522787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719223196972724325015191 1078834795459086487522787)
          ·
            refine ⟨1618252193188629731284181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078834795459086487522787 1618252193188629731284181)
            ·
              refine ⟨37927785777858509326973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1618252193188629731284181 37927785777858509326973)
              ·
                rfl

theorem cell19_373937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_373937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373937 prefixEnd_373937 := by exact prefixLift 373937
  have htrace : WordTrace (prefixWord ++ tailWord_373937) baseStart_373937 baseEnd_373937 := by
    simpa [prefixWord, tailWord_373937, baseEnd_373937] using wordTrace_append hprefix tailTrace_373937
  have hstable : (prefixWord ++ tailWord_373937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373937).length < 2 ^ (prefixWord ++ tailWord_373937).sum := by decide
  have hdescent : baseEnd_373937 < baseStart_373937 := by decide
  rcases family_descends (prefixWord ++ tailWord_373937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373939 : List Nat := [1, 1, 1, 2, 3, 2, 9]
def baseStart_373939 : Nat := 118140960795 + 373939 * 2 ^ 59
def prefixEnd_373939 : Nat := 4983230072969 + 3 ^ 40 * 373939 * 2
def baseEnd_373939 : Nat := 37927988634413371978823

theorem tailTrace_373939 : CollatzResearch.WordTrace tailWord_373939 prefixEnd_373939 37927988634413371978823 := by
  unfold tailWord_373939
  simp only [CollatzResearch.WordTrace]
  refine ⟨13638675792290341541860871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9092450528193561027907247 13638675792290341541860871)
  ·
    refine ⟨20458013688435512312791307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13638675792290341541860871 20458013688435512312791307)
    ·
      refine ⟨30687020532653268469186961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20458013688435512312791307 30687020532653268469186961)
      ·
        refine ⟨23015265399489951351890221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30687020532653268469186961 23015265399489951351890221)
        ·
          refine ⟨8630724524808731756958833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23015265399489951351890221 8630724524808731756958833)
          ·
            refine ⟨6473043393606548817719125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8630724524808731756958833 6473043393606548817719125)
            ·
              refine ⟨37927988634413371978823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6473043393606548817719125 37927988634413371978823)
              ·
                rfl

theorem cell19_373939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_373939 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373939 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373939 prefixEnd_373939 := by exact prefixLift 373939
  have htrace : WordTrace (prefixWord ++ tailWord_373939) baseStart_373939 baseEnd_373939 := by
    simpa [prefixWord, tailWord_373939, baseEnd_373939] using wordTrace_append hprefix tailTrace_373939
  have hstable : (prefixWord ++ tailWord_373939).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373939).length < 2 ^ (prefixWord ++ tailWord_373939).sum := by decide
  have hdescent : baseEnd_373939 < baseStart_373939 := by decide
  rcases family_descends (prefixWord ++ tailWord_373939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373996 : List Nat := [2, 2, 1, 1, 2, 11]
def baseStart_373996 : Nat := 118140960795 + 373996 * 2 ^ 59
def prefixEnd_373996 : Nat := 4983230072969 + 3 ^ 40 * 373996 * 2
def baseEnd_373996 : Nat := 12644590015408985852183

theorem tailTrace_373996 : CollatzResearch.WordTrace tailWord_373996 prefixEnd_373996 12644590015408985852183 := by
  unfold tailWord_373996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820377376541920138342921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9093836502055893517790561 6820377376541920138342921)
  ·
    refine ⟨5115283032406440103757191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6820377376541920138342921 5115283032406440103757191)
    ·
      refine ⟨7672924548609660155635787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5115283032406440103757191 7672924548609660155635787)
      ·
        refine ⟨11509386822914490233453681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7672924548609660155635787 11509386822914490233453681)
        ·
          refine ⟨8632040117185867675090261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11509386822914490233453681 8632040117185867675090261)
          ·
            refine ⟨12644590015408985852183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8632040117185867675090261 12644590015408985852183)
            ·
              rfl

theorem cell19_373996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 11].length) (baseStart_373996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_373996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_373996 prefixEnd_373996 := by exact prefixLift 373996
  have htrace : WordTrace (prefixWord ++ tailWord_373996) baseStart_373996 baseEnd_373996 := by
    simpa [prefixWord, tailWord_373996, baseEnd_373996] using wordTrace_append hprefix tailTrace_373996
  have hstable : (prefixWord ++ tailWord_373996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373996).length < 2 ^ (prefixWord ++ tailWord_373996).sum := by decide
  have hdescent : baseEnd_373996 < baseStart_373996 := by decide
  rcases family_descends (prefixWord ++ tailWord_373996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374030 : List Nat := [4, 1, 1, 2, 1, 4, 3, 3]
def baseStart_374030 : Nat := 118140960795 + 374030 * 2 ^ 59
def prefixEnd_374030 : Nat := 4983230072969 + 3 ^ 40 * 374030 * 2
def baseEnd_374030 : Nat := 113811655822978867913999

theorem tailTrace_374030 : CollatzResearch.WordTrace tailWord_374030 prefixEnd_374030 113811655822978867913999 := by
  unfold tailWord_374030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1705249354370083010427943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9094663223307109388949029 1705249354370083010427943)
  ·
    refine ⟨2557874031555124515641915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1705249354370083010427943 2557874031555124515641915)
    ·
      refine ⟨3836811047332686773462873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557874031555124515641915 3836811047332686773462873)
      ·
        refine ⟨2877608285499515080097155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3836811047332686773462873 2877608285499515080097155)
        ·
          refine ⟨4316412428249272620145733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877608285499515080097155 4316412428249272620145733)
          ·
            refine ⟨809327330296738616277325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4316412428249272620145733 809327330296738616277325)
            ·
              refine ⟨303497748861276981103997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 809327330296738616277325 303497748861276981103997)
              ·
                refine ⟨113811655822978867913999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303497748861276981103997 113811655822978867913999)
                ·
                  rfl

theorem cell19_374030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_374030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374030 prefixEnd_374030 := by exact prefixLift 374030
  have htrace : WordTrace (prefixWord ++ tailWord_374030) baseStart_374030 baseEnd_374030 := by
    simpa [prefixWord, tailWord_374030, baseEnd_374030] using wordTrace_append hprefix tailTrace_374030
  have hstable : (prefixWord ++ tailWord_374030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374030).length < 2 ^ (prefixWord ++ tailWord_374030).sum := by decide
  have hdescent : baseEnd_374030 < baseStart_374030 := by decide
  rcases family_descends (prefixWord ++ tailWord_374030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374072 : List Nat := [2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_374072 : Nat := 118140960795 + 374072 * 2 ^ 59
def prefixEnd_374072 : Nat := 4983230072969 + 3 ^ 40 * 374072 * 2
def baseEnd_374072 : Nat := 113824435785935214980551

theorem tailTrace_374072 : CollatzResearch.WordTrace tailWord_374072 prefixEnd_374072 113824435785935214980551 := by
  unfold tailWord_374072
  simp only [CollatzResearch.WordTrace]
  refine ⟨6821763350404252628226235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9095684467205670170968313 6821763350404252628226235)
  ·
    refine ⟨10232645025606378942339353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6821763350404252628226235 10232645025606378942339353)
    ·
      refine ⟨7674483769204784206754515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10232645025606378942339353 7674483769204784206754515)
      ·
        refine ⟨11511725653807176310131773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7674483769204784206754515 11511725653807176310131773)
        ·
          refine ⟨4316897120177691116299415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11511725653807176310131773 4316897120177691116299415)
          ·
            refine ⟨6475345680266536674449123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316897120177691116299415 6475345680266536674449123)
            ·
              refine ⟨9713018520399805011673685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6475345680266536674449123 9713018520399805011673685)
              ·
                refine ⟨113824435785935214980551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9713018520399805011673685 113824435785935214980551)
                ·
                  rfl

theorem cell19_374072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_374072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374072 prefixEnd_374072 := by exact prefixLift 374072
  have htrace : WordTrace (prefixWord ++ tailWord_374072) baseStart_374072 baseEnd_374072 := by
    simpa [prefixWord, tailWord_374072, baseEnd_374072] using wordTrace_append hprefix tailTrace_374072
  have hstable : (prefixWord ++ tailWord_374072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374072).length < 2 ^ (prefixWord ++ tailWord_374072).sum := by decide
  have hdescent : baseEnd_374072 < baseStart_374072 := by decide
  rcases family_descends (prefixWord ++ tailWord_374072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374087 : List Nat := [1, 1, 4, 1, 2, 5, 2, 3]
def baseStart_374087 : Nat := 118140960795 + 374087 * 2 ^ 59
def prefixEnd_374087 : Nat := 4983230072969 + 3 ^ 40 * 374087 * 2
def baseEnd_374087 : Nat := 113829000058419624647177

theorem tailTrace_374087 : CollatzResearch.WordTrace tailWord_374087 prefixEnd_374087 113829000058419624647177 := by
  unfold tailWord_374087
  simp only [CollatzResearch.WordTrace]
  refine ⟨13644073795754162818248515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9096049197169441878832343 13644073795754162818248515)
  ·
    refine ⟨20466110693631244227372773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13644073795754162818248515 20466110693631244227372773)
    ·
      refine ⟨3837395755055858292632395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20466110693631244227372773 3837395755055858292632395)
      ·
        refine ⟨5756093632583787438948593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3837395755055858292632395 5756093632583787438948593)
        ·
          refine ⟨4317070224437840579211445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5756093632583787438948593 4317070224437840579211445)
          ·
            refine ⟨404725333541047554301073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4317070224437840579211445 404725333541047554301073)
            ·
              refine ⟨303544000155785665725805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404725333541047554301073 303544000155785665725805)
              ·
                refine ⟨113829000058419624647177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303544000155785665725805 113829000058419624647177)
                ·
                  rfl

theorem cell19_374087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 3].length) (baseStart_374087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374087 prefixEnd_374087 := by exact prefixLift 374087
  have htrace : WordTrace (prefixWord ++ tailWord_374087) baseStart_374087 baseEnd_374087 := by
    simpa [prefixWord, tailWord_374087, baseEnd_374087] using wordTrace_append hprefix tailTrace_374087
  have hstable : (prefixWord ++ tailWord_374087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374087).length < 2 ^ (prefixWord ++ tailWord_374087).sum := by decide
  have hdescent : baseEnd_374087 < baseStart_374087 := by decide
  rcases family_descends (prefixWord ++ tailWord_374087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374089 : List Nat := [1, 2, 1, 1, 2, 3, 6, 3]
def baseStart_374089 : Nat := 118140960795 + 374089 * 2 ^ 59
def prefixEnd_374089 : Nat := 4983230072969 + 3 ^ 40 * 374089 * 2
def baseEnd_374089 : Nat := 113829608628084212602727

theorem tailTrace_374089 : CollatzResearch.WordTrace tailWord_374089 prefixEnd_374089 113829608628084212602727 := by
  unfold tailWord_374089
  simp only [CollatzResearch.WordTrace]
  refine ⟨13644146741746917159821321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9096097827831278106547547 13644146741746917159821321)
  ·
    refine ⟨10233110056310187869865991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13644146741746917159821321 10233110056310187869865991)
    ·
      refine ⟨15349665084465281804798987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10233110056310187869865991 15349665084465281804798987)
      ·
        refine ⟨23024497626697922707198481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15349665084465281804798987 23024497626697922707198481)
        ·
          refine ⟨17268373220023442030398861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23024497626697922707198481 17268373220023442030398861)
          ·
            refine ⟨6475639957508790761399573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17268373220023442030398861 6475639957508790761399573)
            ·
              refine ⟨303545623008224566940605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6475639957508790761399573 303545623008224566940605)
              ·
                refine ⟨113829608628084212602727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303545623008224566940605 113829608628084212602727)
                ·
                  rfl

theorem cell19_374089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 3].length) (baseStart_374089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374089 prefixEnd_374089 := by exact prefixLift 374089
  have htrace : WordTrace (prefixWord ++ tailWord_374089) baseStart_374089 baseEnd_374089 := by
    simpa [prefixWord, tailWord_374089, baseEnd_374089] using wordTrace_append hprefix tailTrace_374089
  have hstable : (prefixWord ++ tailWord_374089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374089).length < 2 ^ (prefixWord ++ tailWord_374089).sum := by decide
  have hdescent : baseEnd_374089 < baseStart_374089 := by decide
  rcases family_descends (prefixWord ++ tailWord_374089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374129 : List Nat := [1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_374129 : Nat := 118140960795 + 374129 * 2 ^ 59
def prefixEnd_374129 : Nat := 4983230072969 + 3 ^ 40 * 374129 * 2
def baseEnd_374129 : Nat := 113841780021375971713729

theorem tailTrace_374129 : CollatzResearch.WordTrace tailWord_374129 prefixEnd_374129 113841780021375971713729 := by
  unfold tailWord_374129
  simp only [CollatzResearch.WordTrace]
  refine ⟨13645605661602003991277441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9097070441068002660851627 13645605661602003991277441)
  ·
    refine ⟨10234204246201502993458081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13645605661602003991277441 10234204246201502993458081)
    ·
      refine ⟨7675653184651127245093561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10234204246201502993458081 7675653184651127245093561)
      ·
        refine ⟨5756739888488345433820171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7675653184651127245093561 5756739888488345433820171)
        ·
          refine ⟨8635109832732518150730257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5756739888488345433820171 8635109832732518150730257)
          ·
            refine ⟨6476332374549388613047693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8635109832732518150730257 6476332374549388613047693)
            ·
              refine ⟨2428624640456020729892885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6476332374549388613047693 2428624640456020729892885)
              ·
                refine ⟨113841780021375971713729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2428624640456020729892885 113841780021375971713729)
                ·
                  rfl

theorem cell19_374129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_374129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374129 prefixEnd_374129 := by exact prefixLift 374129
  have htrace : WordTrace (prefixWord ++ tailWord_374129) baseStart_374129 baseEnd_374129 := by
    simpa [prefixWord, tailWord_374129, baseEnd_374129] using wordTrace_append hprefix tailTrace_374129
  have hstable : (prefixWord ++ tailWord_374129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374129).length < 2 ^ (prefixWord ++ tailWord_374129).sum := by decide
  have hdescent : baseEnd_374129 < baseStart_374129 := by decide
  rcases family_descends (prefixWord ++ tailWord_374129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374201 : List Nat := [1, 2, 1, 4, 4, 1, 3, 3]
def baseStart_374201 : Nat := 118140960795 + 374201 * 2 ^ 59
def prefixEnd_374201 : Nat := 4983230072969 + 3 ^ 40 * 374201 * 2
def baseEnd_374201 : Nat := 113863688529301138113533

theorem tailTrace_374201 : CollatzResearch.WordTrace tailWord_374201 prefixEnd_374201 113863688529301138113533 := by
  unfold tailWord_374201
  simp only [CollatzResearch.WordTrace]
  refine ⟨13648231717341160287898457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9098821144894106858598971 13648231717341160287898457)
  ·
    refine ⟨10236173788005870215923843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13648231717341160287898457 10236173788005870215923843)
    ·
      refine ⟨15354260682008805323885765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10236173788005870215923843 15354260682008805323885765)
      ·
        refine ⟨2878923877876650998228581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15354260682008805323885765 2878923877876650998228581)
        ·
          refine ⟨539798227101872062167859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2878923877876650998228581 539798227101872062167859)
          ·
            refine ⟨809697340652808093251789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539798227101872062167859 809697340652808093251789)
            ·
              refine ⟨303636502744803034969421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 809697340652808093251789 303636502744803034969421)
              ·
                refine ⟨113863688529301138113533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303636502744803034969421 113863688529301138113533)
                ·
                  rfl

theorem cell19_374201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 3].length) (baseStart_374201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374201 prefixEnd_374201 := by exact prefixLift 374201
  have htrace : WordTrace (prefixWord ++ tailWord_374201) baseStart_374201 baseEnd_374201 := by
    simpa [prefixWord, tailWord_374201, baseEnd_374201] using wordTrace_append hprefix tailTrace_374201
  have hstable : (prefixWord ++ tailWord_374201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374201).length < 2 ^ (prefixWord ++ tailWord_374201).sum := by decide
  have hdescent : baseEnd_374201 < baseStart_374201 := by decide
  rcases family_descends (prefixWord ++ tailWord_374201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374258 : List Nat := [3, 2, 1, 4, 1, 1, 4, 3]
def baseStart_374258 : Nat := 118140960795 + 374258 * 2 ^ 59
def prefixEnd_374258 : Nat := 4983230072969 + 3 ^ 40 * 374258 * 2
def baseEnd_374258 : Nat := 113881032764741894846711

theorem tailTrace_374258 : CollatzResearch.WordTrace tailWord_374258 prefixEnd_374258 113881032764741894846711 := by
  unfold tailWord_374258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3412577669533664755680857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9100207118756439348482285 3412577669533664755680857)
  ·
    refine ⟨2559433252150248566760643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3412577669533664755680857 2559433252150248566760643)
    ·
      refine ⟨3839149878225372850140965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2559433252150248566760643 3839149878225372850140965)
      ·
        refine ⟨719840602167257409401431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3839149878225372850140965 719840602167257409401431)
        ·
          refine ⟨1079760903250886114102147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719840602167257409401431 1079760903250886114102147)
          ·
            refine ⟨1619641354876329171153221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079760903250886114102147 1619641354876329171153221)
            ·
              refine ⟨303682754039311719591229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1619641354876329171153221 303682754039311719591229)
              ·
                refine ⟨113881032764741894846711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303682754039311719591229 113881032764741894846711)
                ·
                  rfl

theorem cell19_374258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_374258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374258 prefixEnd_374258 := by exact prefixLift 374258
  have htrace : WordTrace (prefixWord ++ tailWord_374258) baseStart_374258 baseEnd_374258 := by
    simpa [prefixWord, tailWord_374258, baseEnd_374258] using wordTrace_append hprefix tailTrace_374258
  have hstable : (prefixWord ++ tailWord_374258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374258).length < 2 ^ (prefixWord ++ tailWord_374258).sum := by decide
  have hdescent : baseEnd_374258 < baseStart_374258 := by decide
  rcases family_descends (prefixWord ++ tailWord_374258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374279 : List Nat := [1, 1, 4, 3, 2, 3, 5]
def baseStart_374279 : Nat := 118140960795 + 374279 * 2 ^ 59
def prefixEnd_374279 : Nat := 4983230072969 + 3 ^ 40 * 374279 * 2
def baseEnd_374279 : Nat := 37962474248740022793329

theorem tailTrace_374279 : CollatzResearch.WordTrace tailWord_374279 prefixEnd_374279 37962474248740022793329 := by
  unfold tailWord_374279
  simp only [CollatzResearch.WordTrace]
  refine ⟨13651076611058579609237891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9100717740705719739491927 13651076611058579609237891)
  ·
    refine ⟨20476614916587869413856837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13651076611058579609237891 20476614916587869413856837)
    ·
      refine ⟨3839365296860225515098157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20476614916587869413856837 3839365296860225515098157)
      ·
        refine ⟨1439761986322584568161809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3839365296860225515098157 1439761986322584568161809)
        ·
          refine ⟨1079821489741938426121357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1439761986322584568161809 1079821489741938426121357)
          ·
            refine ⟨404933058653226909795509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1079821489741938426121357 404933058653226909795509)
            ·
              refine ⟨37962474248740022793329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 404933058653226909795509 37962474248740022793329)
              ·
                rfl

theorem cell19_374279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_374279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374279 prefixEnd_374279 := by exact prefixLift 374279
  have htrace : WordTrace (prefixWord ++ tailWord_374279) baseStart_374279 baseEnd_374279 := by
    simpa [prefixWord, tailWord_374279, baseEnd_374279] using wordTrace_append hprefix tailTrace_374279
  have hstable : (prefixWord ++ tailWord_374279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374279).length < 2 ^ (prefixWord ++ tailWord_374279).sum := by decide
  have hdescent : baseEnd_374279 < baseStart_374279 := by decide
  rcases family_descends (prefixWord ++ tailWord_374279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374446 : List Nat := [4, 1, 4, 1, 3, 1, 5]
def baseStart_374446 : Nat := 118140960795 + 374446 * 2 ^ 59
def prefixEnd_374446 : Nat := 4983230072969 + 3 ^ 40 * 374446 * 2
def baseEnd_374446 : Nat := 37979412771071054222807

theorem tailTrace_374446 : CollatzResearch.WordTrace tailWord_374446 prefixEnd_374446 37979412771071054222807 := by
  unfold tailWord_374446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707145950181695891320899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9104778400969044753711461 1707145950181695891320899)
  ·
    refine ⟨2560718925272543836981349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1707145950181695891320899 2560718925272543836981349)
    ·
      refine ⟨480134798488601969434003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2560718925272543836981349 480134798488601969434003)
      ·
        refine ⟨720202197732902954151005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480134798488601969434003 720202197732902954151005)
        ·
          refine ⟨270075824149838607806627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 720202197732902954151005 270075824149838607806627)
          ·
            refine ⟨405113736224757911709941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270075824149838607806627 405113736224757911709941)
            ·
              refine ⟨37979412771071054222807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 405113736224757911709941 37979412771071054222807)
              ·
                rfl

theorem cell19_374446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 5].length) (baseStart_374446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374446 prefixEnd_374446 := by exact prefixLift 374446
  have htrace : WordTrace (prefixWord ++ tailWord_374446) baseStart_374446 baseEnd_374446 := by
    simpa [prefixWord, tailWord_374446, baseEnd_374446] using wordTrace_append hprefix tailTrace_374446
  have hstable : (prefixWord ++ tailWord_374446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374446).length < 2 ^ (prefixWord ++ tailWord_374446).sum := by decide
  have hdescent : baseEnd_374446 < baseStart_374446 := by decide
  rcases family_descends (prefixWord ++ tailWord_374446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374471 : List Nat := [1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_374471 : Nat := 118140960795 + 374471 * 2 ^ 59
def prefixEnd_374471 : Nat := 4983230072969 + 3 ^ 40 * 374471 * 2
def baseEnd_374471 : Nat := 113945845434020512112797

theorem tailTrace_374471 : CollatzResearch.WordTrace tailWord_374471 prefixEnd_374471 113945845434020512112797 := by
  unfold tailWord_374471
  simp only [CollatzResearch.WordTrace]
  refine ⟨13658079426362996400227267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9105386284241997600151511 13658079426362996400227267)
  ·
    refine ⟨20487119139544494600340901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13658079426362996400227267 20487119139544494600340901)
    ·
      refine ⟨3841334838664592737563919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20487119139544494600340901 3841334838664592737563919)
      ·
        refine ⟨5762002257996889106345879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3841334838664592737563919 5762002257996889106345879)
        ·
          refine ⟨8643003386995333659518819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5762002257996889106345879 8643003386995333659518819)
          ·
            refine ⟨12964505080493000489278229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8643003386995333659518819 12964505080493000489278229)
            ·
              refine ⟨607711175648109397934917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12964505080493000489278229 607711175648109397934917)
              ·
                refine ⟨113945845434020512112797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 607711175648109397934917 113945845434020512112797)
                ·
                  rfl

theorem cell19_374471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_374471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374471 prefixEnd_374471 := by exact prefixLift 374471
  have htrace : WordTrace (prefixWord ++ tailWord_374471) baseStart_374471 baseEnd_374471 := by
    simpa [prefixWord, tailWord_374471, baseEnd_374471] using wordTrace_append hprefix tailTrace_374471
  have hstable : (prefixWord ++ tailWord_374471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374471).length < 2 ^ (prefixWord ++ tailWord_374471).sum := by decide
  have hdescent : baseEnd_374471 < baseStart_374471 := by decide
  rcases family_descends (prefixWord ++ tailWord_374471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374490 : List Nat := [3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_374490 : Nat := 118140960795 + 374490 * 2 ^ 59
def prefixEnd_374490 : Nat := 4983230072969 + 3 ^ 40 * 374490 * 2
def baseEnd_374490 : Nat := 113951626845834097690523

theorem tailTrace_374490 : CollatzResearch.WordTrace tailWord_374490 prefixEnd_374490 113951626845834097690523 := by
  unfold tailWord_374490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414693103323540661292231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9105848275529441763445949 3414693103323540661292231)
  ·
    refine ⟨5122039654985310991938347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3414693103323540661292231 5122039654985310991938347)
    ·
      refine ⟨7683059482477966487907521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5122039654985310991938347 7683059482477966487907521)
      ·
        refine ⟨5762294611858474865930641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7683059482477966487907521 5762294611858474865930641)
        ·
          refine ⟨4321720958893856149447981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5762294611858474865930641 4321720958893856149447981)
          ·
            refine ⟨1620645359585196056042993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4321720958893856149447981 1620645359585196056042993)
            ·
              refine ⟨1215484019688897042032245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620645359585196056042993 1215484019688897042032245)
              ·
                refine ⟨113951626845834097690523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1215484019688897042032245 113951626845834097690523)
                ·
                  rfl

theorem cell19_374490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_374490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374490 prefixEnd_374490 := by exact prefixLift 374490
  have htrace : WordTrace (prefixWord ++ tailWord_374490) baseStart_374490 baseEnd_374490 := by
    simpa [prefixWord, tailWord_374490, baseEnd_374490] using wordTrace_append hprefix tailTrace_374490
  have hstable : (prefixWord ++ tailWord_374490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374490).length < 2 ^ (prefixWord ++ tailWord_374490).sum := by decide
  have hdescent : baseEnd_374490 < baseStart_374490 := by decide
  rcases family_descends (prefixWord ++ tailWord_374490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374509 : List Nat := [1, 5, 1, 2, 1, 9]
def baseStart_374509 : Nat := 118140960795 + 374509 * 2 ^ 59
def prefixEnd_374509 : Nat := 4983230072969 + 3 ^ 40 * 374509 * 2
def baseEnd_374509 : Nat := 12661934250849742585361

theorem tailTrace_374509 : CollatzResearch.WordTrace tailWord_374509 prefixEnd_374509 12661934250849742585361 := by
  unfold tailWord_374509
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659465400225328890110581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9106310266816885926740387 13659465400225328890110581)
  ·
    refine ⟨1280574881271124583447867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13659465400225328890110581 1280574881271124583447867)
    ·
      refine ⟨1920862321906686875171801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280574881271124583447867 1920862321906686875171801)
      ·
        refine ⟨1440646741430015156378851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1920862321906686875171801 1440646741430015156378851)
        ·
          refine ⟨2160970112145022734568277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440646741430015156378851 2160970112145022734568277)
          ·
            refine ⟨12661934250849742585361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2160970112145022734568277 12661934250849742585361)
            ·
              rfl

theorem cell19_374509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 9].length) (baseStart_374509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374509 prefixEnd_374509 := by exact prefixLift 374509
  have htrace : WordTrace (prefixWord ++ tailWord_374509) baseStart_374509 baseEnd_374509 := by
    simpa [prefixWord, tailWord_374509, baseEnd_374509] using wordTrace_append hprefix tailTrace_374509
  have hstable : (prefixWord ++ tailWord_374509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374509).length < 2 ^ (prefixWord ++ tailWord_374509).sum := by decide
  have hdescent : baseEnd_374509 < baseStart_374509 := by decide
  rcases family_descends (prefixWord ++ tailWord_374509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374598 : List Nat := [6, 1, 1, 2, 1, 1, 4, 3]
def baseStart_374598 : Nat := 118140960795 + 374598 * 2 ^ 59
def prefixEnd_374598 : Nat := 4983230072969 + 3 ^ 40 * 374598 * 2
def baseEnd_374598 : Nat := 113984489607721847290229

theorem tailTrace_374598 : CollatzResearch.WordTrace tailWord_374598 prefixEnd_374598 113984489607721847290229 := by
  unfold tailWord_374598
  simp only [CollatzResearch.WordTrace]
  refine ⟨426959734278215534065639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9108474331268598060066965 426959734278215534065639)
  ·
    refine ⟨640439601417323301098459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 426959734278215534065639 640439601417323301098459)
    ·
      refine ⟨960659402125984951647689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640439601417323301098459 960659402125984951647689)
      ·
        refine ⟨720494551594488713735767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 960659402125984951647689 720494551594488713735767)
        ·
          refine ⟨1080741827391733070603651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720494551594488713735767 1080741827391733070603651)
          ·
            refine ⟨1621112741087599605905477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080741827391733070603651 1621112741087599605905477)
            ·
              refine ⟨303958638953924926107277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1621112741087599605905477 303958638953924926107277)
              ·
                refine ⟨113984489607721847290229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303958638953924926107277 113984489607721847290229)
                ·
                  rfl

theorem cell19_374598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_374598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374598 prefixEnd_374598 := by exact prefixLift 374598
  have htrace : WordTrace (prefixWord ++ tailWord_374598) baseStart_374598 baseEnd_374598 := by
    simpa [prefixWord, tailWord_374598, baseEnd_374598] using wordTrace_append hprefix tailTrace_374598
  have hstable : (prefixWord ++ tailWord_374598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374598).length < 2 ^ (prefixWord ++ tailWord_374598).sum := by decide
  have hdescent : baseEnd_374598 < baseStart_374598 := by decide
  rcases family_descends (prefixWord ++ tailWord_374598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374623 : List Nat := [1, 1, 2, 3, 1, 6, 5]
def baseStart_374623 : Nat := 118140960795 + 374623 * 2 ^ 59
def prefixEnd_374623 : Nat := 4983230072969 + 3 ^ 40 * 374623 * 2
def baseEnd_374623 : Nat := 37997365576176398911535

theorem tailTrace_374623 : CollatzResearch.WordTrace tailWord_374623 prefixEnd_374623 37997365576176398911535 := by
  unfold tailWord_374623
  simp only [CollatzResearch.WordTrace]
  refine ⟨13663623321812326359760523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9109082214541550906507015 13663623321812326359760523)
  ·
    refine ⟨20495434982718489539640785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13663623321812326359760523 20495434982718489539640785)
    ·
      refine ⟨15371576237038867154730589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20495434982718489539640785 15371576237038867154730589)
      ·
        refine ⟨5764341088889575183023971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15371576237038867154730589 5764341088889575183023971)
        ·
          refine ⟨8646511633334362774535957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5764341088889575183023971 8646511633334362774535957)
          ·
            refine ⟨405305232812548255056373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8646511633334362774535957 405305232812548255056373)
            ·
              refine ⟨37997365576176398911535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 405305232812548255056373 37997365576176398911535)
              ·
                rfl

theorem cell19_374623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_374623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374623 prefixEnd_374623 := by exact prefixLift 374623
  have htrace : WordTrace (prefixWord ++ tailWord_374623) baseStart_374623 baseEnd_374623 := by
    simpa [prefixWord, tailWord_374623, baseEnd_374623] using wordTrace_append hprefix tailTrace_374623
  have hstable : (prefixWord ++ tailWord_374623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374623).length < 2 ^ (prefixWord ++ tailWord_374623).sum := by decide
  have hdescent : baseEnd_374623 < baseStart_374623 := by decide
  rcases family_descends (prefixWord ++ tailWord_374623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374680 : List Nat := [2, 1, 2, 6, 8]
def baseStart_374680 : Nat := 118140960795 + 374680 * 2 ^ 59
def prefixEnd_374680 : Nat := 4983230072969 + 3 ^ 40 * 374680 * 2
def baseEnd_374680 : Nat := 4222571887554442721029

theorem tailTrace_374680 : CollatzResearch.WordTrace tailWord_374680 prefixEnd_374680 4222571887554442721029 := by
  unfold tailWord_374680
  simp only [CollatzResearch.WordTrace]
  refine ⟨6832851141302912547292747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9110468188403883396390329 6832851141302912547292747)
  ·
    refine ⟨10249276711954368820939121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6832851141302912547292747 10249276711954368820939121)
    ·
      refine ⟨7686957533965776615704341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10249276711954368820939121 7686957533965776615704341)
      ·
        refine ⟨360326134404645778861141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7686957533965776615704341 360326134404645778861141)
        ·
          refine ⟨4222571887554442721029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 360326134404645778861141 4222571887554442721029)
          ·
            rfl

theorem cell19_374680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 8].length) (baseStart_374680 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374680 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374680 prefixEnd_374680 := by exact prefixLift 374680
  have htrace : WordTrace (prefixWord ++ tailWord_374680) baseStart_374680 baseEnd_374680 := by
    simpa [prefixWord, tailWord_374680, baseEnd_374680] using wordTrace_append hprefix tailTrace_374680
  have hstable : (prefixWord ++ tailWord_374680).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374680).length < 2 ^ (prefixWord ++ tailWord_374680).sum := by decide
  have hdescent : baseEnd_374680 < baseStart_374680 := by decide
  rcases family_descends (prefixWord ++ tailWord_374680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374813 : List Nat := [1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_374813 : Nat := 118140960795 + 374813 * 2 ^ 59
def prefixEnd_374813 : Nat := 4983230072969 + 3 ^ 40 * 374813 * 2
def baseEnd_374813 : Nat := 114049910846665052511865

theorem tailTrace_374813 : CollatzResearch.WordTrace tailWord_374813 prefixEnd_374813 114049910846665052511865 := by
  unfold tailWord_374813
  simp only [CollatzResearch.WordTrace]
  refine ⟨13670553191123988809177093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9113702127415992539451395 13670553191123988809177093)
  ·
    refine ⟨2563228723335747901720705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13670553191123988809177093 2563228723335747901720705)
    ·
      refine ⟨1922421542501810926290529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2563228723335747901720705 1922421542501810926290529)
      ·
        refine ⟨1441816156876358194717897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1922421542501810926290529 1441816156876358194717897)
        ·
          refine ⟨1081362117657268646038423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1441816156876358194717897 1081362117657268646038423)
          ·
            refine ⟨1622043176485902969057635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081362117657268646038423 1622043176485902969057635)
            ·
              refine ⟨2433064764728854453586453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622043176485902969057635 2433064764728854453586453)
              ·
                refine ⟨114049910846665052511865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2433064764728854453586453 114049910846665052511865)
                ·
                  rfl

theorem cell19_374813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_374813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374813 prefixEnd_374813 := by exact prefixLift 374813
  have htrace : WordTrace (prefixWord ++ tailWord_374813) baseStart_374813 baseEnd_374813 := by
    simpa [prefixWord, tailWord_374813, baseEnd_374813] using wordTrace_append hprefix tailTrace_374813
  have hstable : (prefixWord ++ tailWord_374813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374813).length < 2 ^ (prefixWord ++ tailWord_374813).sum := by decide
  have hdescent : baseEnd_374813 < baseStart_374813 := by decide
  rcases family_descends (prefixWord ++ tailWord_374813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374866 : List Nat := [3, 2, 2, 1, 5, 1, 1, 4]
def baseStart_374866 : Nat := 118140960795 + 374866 * 2 ^ 59
def prefixEnd_374866 : Nat := 4983230072969 + 3 ^ 40 * 374866 * 2
def baseEnd_374866 : Nat := 114066037942776633333943

theorem tailTrace_374866 : CollatzResearch.WordTrace tailWord_374866 prefixEnd_374866 114066037942776633333943 := by
  unfold tailWord_374866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3418121564982994715214113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9114990839954652573904301 3418121564982994715214113)
  ·
    refine ⟨2563591173737246036410585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3418121564982994715214113 2563591173737246036410585)
    ·
      refine ⟨1922693380302934527307939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2563591173737246036410585 1922693380302934527307939)
      ·
        refine ⟨2884040070454401790961909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1922693380302934527307939 2884040070454401790961909)
        ·
          refine ⟨270378756605100167902679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2884040070454401790961909 270378756605100167902679)
          ·
            refine ⟨405568134907650251854019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270378756605100167902679 405568134907650251854019)
            ·
              refine ⟨608352202361475377781029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405568134907650251854019 608352202361475377781029)
              ·
                refine ⟨114066037942776633333943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 608352202361475377781029 114066037942776633333943)
                ·
                  rfl

theorem cell19_374866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_374866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374866 prefixEnd_374866 := by exact prefixLift 374866
  have htrace : WordTrace (prefixWord ++ tailWord_374866) baseStart_374866 baseEnd_374866 := by
    simpa [prefixWord, tailWord_374866, baseEnd_374866] using wordTrace_append hprefix tailTrace_374866
  have hstable : (prefixWord ++ tailWord_374866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374866).length < 2 ^ (prefixWord ++ tailWord_374866).sum := by decide
  have hdescent : baseEnd_374866 < baseStart_374866 := by decide
  rcases family_descends (prefixWord ++ tailWord_374866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374889 : List Nat := [1, 2, 1, 1, 1, 5, 5, 3]
def baseStart_374889 : Nat := 118140960795 + 374889 * 2 ^ 59
def prefixEnd_374889 : Nat := 4983230072969 + 3 ^ 40 * 374889 * 2
def baseEnd_374889 : Nat := 114073036493919394822769

theorem tailTrace_374889 : CollatzResearch.WordTrace tailWord_374889 prefixEnd_374889 114073036493919394822769 := by
  unfold tailWord_374889
  simp only [CollatzResearch.WordTrace]
  refine ⟨13673325138848653788943721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9115550092565769192629147 13673325138848653788943721)
  ·
    refine ⟨10254993854136490341707791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13673325138848653788943721 10254993854136490341707791)
    ·
      refine ⟨15382490781204735512561687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10254993854136490341707791 15382490781204735512561687)
      ·
        refine ⟨23073736171807103268842531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15382490781204735512561687 23073736171807103268842531)
        ·
          refine ⟨34610604257710654903263797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23073736171807103268842531 34610604257710654903263797)
          ·
            refine ⟨3244744149160373897180981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34610604257710654903263797 3244744149160373897180981)
            ·
              refine ⟨304194763983785052860717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3244744149160373897180981 304194763983785052860717)
              ·
                refine ⟨114073036493919394822769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304194763983785052860717 114073036493919394822769)
                ·
                  rfl

theorem cell19_374889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 3].length) (baseStart_374889 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374889 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374889 prefixEnd_374889 := by exact prefixLift 374889
  have htrace : WordTrace (prefixWord ++ tailWord_374889) baseStart_374889 baseEnd_374889 := by
    simpa [prefixWord, tailWord_374889, baseEnd_374889] using wordTrace_append hprefix tailTrace_374889
  have hstable : (prefixWord ++ tailWord_374889).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374889).length < 2 ^ (prefixWord ++ tailWord_374889).sum := by decide
  have hdescent : baseEnd_374889 < baseStart_374889 := by decide
  rcases family_descends (prefixWord ++ tailWord_374889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374934 : List Nat := [5, 3, 2, 1, 2, 1, 2, 3]
def baseStart_374934 : Nat := 118140960795 + 374934 * 2 ^ 59
def prefixEnd_374934 : Nat := 4983230072969 + 3 ^ 40 * 374934 * 2
def baseEnd_374934 : Nat := 114086729311372623822647

theorem tailTrace_374934 : CollatzResearch.WordTrace tailWord_374934 prefixEnd_374934 114086729311372623822647 := by
  unfold tailWord_374934
  simp only [CollatzResearch.WordTrace]
  refine ⟨854685401480351654645741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9116644282457084316221237 854685401480351654645741)
  ·
    refine ⟨320507025555131870492153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 854685401480351654645741 320507025555131870492153)
    ·
      refine ⟨240380269166348902869115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320507025555131870492153 240380269166348902869115)
      ·
        refine ⟨360570403749523354303673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240380269166348902869115 360570403749523354303673)
        ·
          refine ⟨270427802812142515727755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360570403749523354303673 270427802812142515727755)
          ·
            refine ⟨405641704218213773591633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270427802812142515727755 405641704218213773591633)
            ·
              refine ⟨304231278163660330193725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405641704218213773591633 304231278163660330193725)
              ·
                refine ⟨114086729311372623822647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304231278163660330193725 114086729311372623822647)
                ·
                  rfl

theorem cell19_374934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_374934 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374934 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374934 prefixEnd_374934 := by exact prefixLift 374934
  have htrace : WordTrace (prefixWord ++ tailWord_374934) baseStart_374934 baseEnd_374934 := by
    simpa [prefixWord, tailWord_374934, baseEnd_374934] using wordTrace_append hprefix tailTrace_374934
  have hstable : (prefixWord ++ tailWord_374934).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374934).length < 2 ^ (prefixWord ++ tailWord_374934).sum := by decide
  have hdescent : baseEnd_374934 < baseStart_374934 := by decide
  rcases family_descends (prefixWord ++ tailWord_374934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374944 : List Nat := [2, 1, 1, 4, 2, 4, 2, 3]
def baseStart_374944 : Nat := 118140960795 + 374944 * 2 ^ 59
def prefixEnd_374944 : Nat := 4983230072969 + 3 ^ 40 * 374944 * 2
def baseEnd_374944 : Nat := 114089772159695563600397

theorem tailTrace_374944 : CollatzResearch.WordTrace tailWord_374944 prefixEnd_374944 114089772159695563600397 := by
  unfold tailWord_374944
  simp only [CollatzResearch.WordTrace]
  refine ⟨6837665576824699091097943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9116887435766265454797257 6837665576824699091097943)
  ·
    refine ⟨10256498365237048636646915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6837665576824699091097943 10256498365237048636646915)
    ·
      refine ⟨15384747547855572954970373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10256498365237048636646915 15384747547855572954970373)
      ·
        refine ⟨2884640165222919929056945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15384747547855572954970373 2884640165222919929056945)
        ·
          refine ⟨2163480123917189946792709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2884640165222919929056945 2163480123917189946792709)
          ·
            refine ⟨405652523234473115023633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2163480123917189946792709 405652523234473115023633)
            ·
              refine ⟨304239392425854836267725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405652523234473115023633 304239392425854836267725)
              ·
                refine ⟨114089772159695563600397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304239392425854836267725 114089772159695563600397)
                ·
                  rfl

theorem cell19_374944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_374944 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374944 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374944 prefixEnd_374944 := by exact prefixLift 374944
  have htrace : WordTrace (prefixWord ++ tailWord_374944) baseStart_374944 baseEnd_374944 := by
    simpa [prefixWord, tailWord_374944, baseEnd_374944] using wordTrace_append hprefix tailTrace_374944
  have hstable : (prefixWord ++ tailWord_374944).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374944).length < 2 ^ (prefixWord ++ tailWord_374944).sum := by decide
  have hdescent : baseEnd_374944 < baseStart_374944 := by decide
  rcases family_descends (prefixWord ++ tailWord_374944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374967 : List Nat := [1, 1, 3, 1, 4, 2, 7]
def baseStart_374967 : Nat := 118140960795 + 374967 * 2 ^ 59
def prefixEnd_374967 : Nat := 4983230072969 + 3 ^ 40 * 374967 * 2
def baseEnd_374967 : Nat := 38032256903612775029741

theorem tailTrace_374967 : CollatzResearch.WordTrace tailWord_374967 prefixEnd_374967 38032256903612775029741 := by
  unfold tailWord_374967
  simp only [CollatzResearch.WordTrace]
  refine ⟨13676170032566073110283155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9117446688377382073522103 13676170032566073110283155)
  ·
    refine ⟨20514255048849109665424733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13676170032566073110283155 20514255048849109665424733)
    ·
      refine ⟨7692845643318416124534275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20514255048849109665424733 7692845643318416124534275)
      ·
        refine ⟨11539268464977624186801413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7692845643318416124534275 11539268464977624186801413)
        ·
          refine ⟨2163612837183304535025265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11539268464977624186801413 2163612837183304535025265)
          ·
            refine ⟨1622709627887478401268949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2163612837183304535025265 1622709627887478401268949)
            ·
              refine ⟨38032256903612775029741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1622709627887478401268949 38032256903612775029741)
              ·
                rfl

theorem cell19_374967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_374967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_374967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_374967 prefixEnd_374967 := by exact prefixLift 374967
  have htrace : WordTrace (prefixWord ++ tailWord_374967) baseStart_374967 baseEnd_374967 := by
    simpa [prefixWord, tailWord_374967, baseEnd_374967] using wordTrace_append hprefix tailTrace_374967
  have hstable : (prefixWord ++ tailWord_374967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374967).length < 2 ^ (prefixWord ++ tailWord_374967).sum := by decide
  have hdescent : baseEnd_374967 < baseStart_374967 := by decide
  rcases family_descends (prefixWord ++ tailWord_374967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375100 : List Nat := [2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_375100 : Nat := 118140960795 + 375100 * 2 ^ 59
def prefixEnd_375100 : Nat := 4983230072969 + 3 ^ 40 * 375100 * 2
def baseEnd_375100 : Nat := 114137240593533424133305

theorem tailTrace_375100 : CollatzResearch.WordTrace tailWord_375100 prefixEnd_375100 114137240593533424133305 := by
  unfold tailWord_375100
  simp only [CollatzResearch.WordTrace]
  refine ⟨6840510470542118412437377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9120680627389491216583169 6840510470542118412437377)
  ·
    refine ⟨5130382852906588809328033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6840510470542118412437377 5130382852906588809328033)
    ·
      refine ⟨3847787139679941606996025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5130382852906588809328033 3847787139679941606996025)
      ·
        refine ⟨2885840354759956205247019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3847787139679941606996025 2885840354759956205247019)
        ·
          refine ⟨4328760532139934307870529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2885840354759956205247019 4328760532139934307870529)
          ·
            refine ⟨3246570399104950730902897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4328760532139934307870529 3246570399104950730902897)
            ·
              refine ⟨2434927799328713048177173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3246570399104950730902897 2434927799328713048177173)
              ·
                refine ⟨114137240593533424133305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2434927799328713048177173 114137240593533424133305)
                ·
                  rfl

theorem cell19_375100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_375100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375100 prefixEnd_375100 := by exact prefixLift 375100
  have htrace : WordTrace (prefixWord ++ tailWord_375100) baseStart_375100 baseEnd_375100 := by
    simpa [prefixWord, tailWord_375100, baseEnd_375100] using wordTrace_append hprefix tailTrace_375100
  have hstable : (prefixWord ++ tailWord_375100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375100).length < 2 ^ (prefixWord ++ tailWord_375100).sum := by decide
  have hdescent : baseEnd_375100 < baseStart_375100 := by decide
  rcases family_descends (prefixWord ++ tailWord_375100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375132 : List Nat := [2, 2, 4, 3, 2, 1, 5]
def baseStart_375132 : Nat := 118140960795 + 375132 * 2 ^ 59
def prefixEnd_375132 : Nat := 4983230072969 + 3 ^ 40 * 375132 * 2
def baseEnd_375132 : Nat := 38048992569388943807369

theorem tailTrace_375132 : CollatzResearch.WordTrace tailWord_375132 prefixEnd_375132 38048992569388943807369 := by
  unfold tailWord_375132
  simp only [CollatzResearch.WordTrace]
  refine ⟨6841094038484153145019825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9121458717978870860026433 6841094038484153145019825)
  ·
    refine ⟨5130820528863114858764869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6841094038484153145019825 5130820528863114858764869)
    ·
      refine ⟨962028849161834036018413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5130820528863114858764869 962028849161834036018413)
      ·
        refine ⟨360760818435687763506905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 962028849161834036018413 360760818435687763506905)
        ·
          refine ⟨270570613826765822630179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360760818435687763506905 270570613826765822630179)
          ·
            refine ⟨405855920740148733945269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270570613826765822630179 405855920740148733945269)
            ·
              refine ⟨38048992569388943807369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 405855920740148733945269 38048992569388943807369)
              ·
                rfl

theorem cell19_375132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 5].length) (baseStart_375132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375132 prefixEnd_375132 := by exact prefixLift 375132
  have htrace : WordTrace (prefixWord ++ tailWord_375132) baseStart_375132 baseEnd_375132 := by
    simpa [prefixWord, tailWord_375132, baseEnd_375132] using wordTrace_append hprefix tailTrace_375132
  have hstable : (prefixWord ++ tailWord_375132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375132).length < 2 ^ (prefixWord ++ tailWord_375132).sum := by decide
  have hdescent : baseEnd_375132 < baseStart_375132 := by decide
  rcases family_descends (prefixWord ++ tailWord_375132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375136 : List Nat := [2, 1, 1, 3, 5, 2, 5]
def baseStart_375136 : Nat := 118140960795 + 375136 * 2 ^ 59
def prefixEnd_375136 : Nat := 4983230072969 + 3 ^ 40 * 375136 * 2
def baseEnd_375136 : Nat := 38049398282498669111069

theorem tailTrace_375136 : CollatzResearch.WordTrace tailWord_375136 prefixEnd_375136 38049398282498669111069 := by
  unfold tailWord_375136
  simp only [CollatzResearch.WordTrace]
  refine ⟨6841166984476907486592631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9121555979302543315456841 6841166984476907486592631)
  ·
    refine ⟨10261750476715361229888947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6841166984476907486592631 10261750476715361229888947)
    ·
      refine ⟨15392625715073041844833421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10261750476715361229888947 15392625715073041844833421)
      ·
        refine ⟨5772234643152390691812533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15392625715073041844833421 5772234643152390691812533)
        ·
          refine ⟨541146997795536627357425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5772234643152390691812533 541146997795536627357425)
          ·
            refine ⟨405860248346652470518069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541146997795536627357425 405860248346652470518069)
            ·
              refine ⟨38049398282498669111069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 405860248346652470518069 38049398282498669111069)
              ·
                rfl

theorem cell19_375136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_375136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375136 prefixEnd_375136 := by exact prefixLift 375136
  have htrace : WordTrace (prefixWord ++ tailWord_375136) baseStart_375136 baseEnd_375136 := by
    simpa [prefixWord, tailWord_375136, baseEnd_375136] using wordTrace_append hprefix tailTrace_375136
  have hstable : (prefixWord ++ tailWord_375136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375136).length < 2 ^ (prefixWord ++ tailWord_375136).sum := by decide
  have hdescent : baseEnd_375136 < baseStart_375136 := by decide
  rcases family_descends (prefixWord ++ tailWord_375136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375176 : List Nat := [2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_375176 : Nat := 118140960795 + 375176 * 2 ^ 59
def prefixEnd_375176 : Nat := 4983230072969 + 3 ^ 40 * 375176 * 2
def baseEnd_375176 : Nat := 114160366240787766444209

theorem tailTrace_375176 : CollatzResearch.WordTrace tailWord_375176 prefixEnd_375176 114160366240787766444209 := by
  unfold tailWord_375176
  simp only [CollatzResearch.WordTrace]
  refine ⟨6841896444404450902320691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9122528592539267869760921 6841896444404450902320691)
  ·
    refine ⟨10262844666606676353481037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6841896444404450902320691 10262844666606676353481037)
    ·
      refine ⟨3848566749977503632555389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10262844666606676353481037 3848566749977503632555389)
      ·
        refine ⟨1443212531241563862208271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3848566749977503632555389 1443212531241563862208271)
        ·
          refine ⟨2164818796862345793312407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443212531241563862208271 2164818796862345793312407)
          ·
            refine ⟨3247228195293518689968611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164818796862345793312407 3247228195293518689968611)
            ·
              refine ⟨4870842292940278034952917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247228195293518689968611 4870842292940278034952917)
              ·
                refine ⟨114160366240787766444209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4870842292940278034952917 114160366240787766444209)
                ·
                  rfl

theorem cell19_375176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_375176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375176 prefixEnd_375176 := by exact prefixLift 375176
  have htrace : WordTrace (prefixWord ++ tailWord_375176) baseStart_375176 baseEnd_375176 := by
    simpa [prefixWord, tailWord_375176, baseEnd_375176] using wordTrace_append hprefix tailTrace_375176
  have hstable : (prefixWord ++ tailWord_375176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375176).length < 2 ^ (prefixWord ++ tailWord_375176).sum := by decide
  have hdescent : baseEnd_375176 < baseStart_375176 := by decide
  rcases family_descends (prefixWord ++ tailWord_375176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375271 : List Nat := [1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_375271 : Nat := 118140960795 + 375271 * 2 ^ 59
def prefixEnd_375271 : Nat := 4983230072969 + 3 ^ 40 * 375271 * 2
def baseEnd_375271 : Nat := 114189273299855694332839

theorem tailTrace_375271 : CollatzResearch.WordTrace tailWord_375271 prefixEnd_375271 114189273299855694332839 := by
  unfold tailWord_375271
  simp only [CollatzResearch.WordTrace]
  refine ⟨13687257823464733029349667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9124838548976488686233111 13687257823464733029349667)
  ·
    refine ⟨20530886735197099544024501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13687257823464733029349667 20530886735197099544024501)
    ·
      refine ⟨1924770631424728082252297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20530886735197099544024501 1924770631424728082252297)
      ·
        refine ⟨1443577973568546061689223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1924770631424728082252297 1443577973568546061689223)
        ·
          refine ⟨2165366960352819092533835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443577973568546061689223 2165366960352819092533835)
          ·
            refine ⟨3248050440529228638800753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165366960352819092533835 3248050440529228638800753)
            ·
              refine ⟨2436037830396921479100565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3248050440529228638800753 2436037830396921479100565)
              ·
                refine ⟨114189273299855694332839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2436037830396921479100565 114189273299855694332839)
                ·
                  rfl

theorem cell19_375271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_375271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375271 prefixEnd_375271 := by exact prefixLift 375271
  have htrace : WordTrace (prefixWord ++ tailWord_375271) baseStart_375271 baseEnd_375271 := by
    simpa [prefixWord, tailWord_375271, baseEnd_375271] using wordTrace_append hprefix tailTrace_375271
  have hstable : (prefixWord ++ tailWord_375271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375271).length < 2 ^ (prefixWord ++ tailWord_375271).sum := by decide
  have hdescent : baseEnd_375271 < baseStart_375271 := by decide
  rcases family_descends (prefixWord ++ tailWord_375271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375400 : List Nat := [2, 1, 4, 3, 2, 1, 3, 3]
def baseStart_375400 : Nat := 118140960795 + 375400 * 2 ^ 59
def prefixEnd_375400 : Nat := 4983230072969 + 3 ^ 40 * 375400 * 2
def baseEnd_375400 : Nat := 114228526043221617465821

theorem tailTrace_375400 : CollatzResearch.WordTrace tailWord_375400 prefixEnd_375400 114228526043221617465821 := by
  unfold tailWord_375400
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845981419998694030397827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9127975226664925373863769 6845981419998694030397827)
  ·
    refine ⟨10268972129998041045596741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6845981419998694030397827 10268972129998041045596741)
    ·
      refine ⟨1925432274374632696049389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10268972129998041045596741 1925432274374632696049389)
      ·
        refine ⟨722037102890487261018521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1925432274374632696049389 722037102890487261018521)
        ·
          refine ⟨541527827167865445763891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 722037102890487261018521 541527827167865445763891)
          ·
            refine ⟨812291740751798168645837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541527827167865445763891 812291740751798168645837)
            ·
              refine ⟨304609402781924313242189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 812291740751798168645837 304609402781924313242189)
              ·
                refine ⟨114228526043221617465821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304609402781924313242189 114228526043221617465821)
                ·
                  rfl

theorem cell19_375400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_375400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375400 prefixEnd_375400 := by exact prefixLift 375400
  have htrace : WordTrace (prefixWord ++ tailWord_375400) baseStart_375400 baseEnd_375400 := by
    simpa [prefixWord, tailWord_375400, baseEnd_375400] using wordTrace_append hprefix tailTrace_375400
  have hstable : (prefixWord ++ tailWord_375400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375400).length < 2 ^ (prefixWord ++ tailWord_375400).sum := by decide
  have hdescent : baseEnd_375400 < baseStart_375400 := by decide
  rcases family_descends (prefixWord ++ tailWord_375400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375402 : List Nat := [3, 1, 3, 2, 1, 1, 5, 3]
def baseStart_375402 : Nat := 118140960795 + 375402 * 2 ^ 59
def prefixEnd_375402 : Nat := 4983230072969 + 3 ^ 40 * 375402 * 2
def baseEnd_375402 : Nat := 114229134612886205421371

theorem tailTrace_375402 : CollatzResearch.WordTrace tailWord_375402 prefixEnd_375402 114229134612886205421371 := by
  unfold tailWord_375402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423008946497535600592115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9128023857326761601578973 3423008946497535600592115)
  ·
    refine ⟨5134513419746303400888173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3423008946497535600592115 5134513419746303400888173)
    ·
      refine ⟨1925442532404863775333065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5134513419746303400888173 1925442532404863775333065)
      ·
        refine ⟨1444081899303647831499799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1925442532404863775333065 1444081899303647831499799)
        ·
          refine ⟨2166122848955471747249699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444081899303647831499799 2166122848955471747249699)
          ·
            refine ⟨3249184273433207620874549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166122848955471747249699 3249184273433207620874549)
            ·
              refine ⟨304611025634363214456989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3249184273433207620874549 304611025634363214456989)
              ·
                refine ⟨114229134612886205421371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304611025634363214456989 114229134612886205421371)
                ·
                  rfl

theorem cell19_375402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_375402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375402 prefixEnd_375402 := by exact prefixLift 375402
  have htrace : WordTrace (prefixWord ++ tailWord_375402) baseStart_375402 baseEnd_375402 := by
    simpa [prefixWord, tailWord_375402, baseEnd_375402] using wordTrace_append hprefix tailTrace_375402
  have hstable : (prefixWord ++ tailWord_375402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375402).length < 2 ^ (prefixWord ++ tailWord_375402).sum := by decide
  have hdescent : baseEnd_375402 < baseStart_375402 := by decide
  rcases family_descends (prefixWord ++ tailWord_375402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375457 : List Nat := [1, 2, 3, 3, 3, 2, 2, 3]
def baseStart_375457 : Nat := 118140960795 + 375457 * 2 ^ 59
def prefixEnd_375457 : Nat := 4983230072969 + 3 ^ 40 * 375457 * 2
def baseEnd_375457 : Nat := 114245870278662374198999

theorem tailTrace_375457 : CollatzResearch.WordTrace tailWord_375457 prefixEnd_375457 114245870278662374198999 := by
  unfold tailWord_375457
  simp only [CollatzResearch.WordTrace]
  refine ⟨13694041800790886795620625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9129361200527257863747083 13694041800790886795620625)
  ·
    refine ⟨10270531350593165096715469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13694041800790886795620625 10270531350593165096715469)
    ·
      refine ⟨3851449256472436911268301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10270531350593165096715469 3851449256472436911268301)
      ·
        refine ⟨1444293471177163841725613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3851449256472436911268301 1444293471177163841725613)
        ·
          refine ⟨541610051691436440647105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1444293471177163841725613 541610051691436440647105)
          ·
            refine ⟨406207538768577330485329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541610051691436440647105 406207538768577330485329)
            ·
              refine ⟨304655654076432997863997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406207538768577330485329 304655654076432997863997)
              ·
                refine ⟨114245870278662374198999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304655654076432997863997 114245870278662374198999)
                ·
                  rfl

theorem cell19_375457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 3].length) (baseStart_375457 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375457 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375457 prefixEnd_375457 := by exact prefixLift 375457
  have htrace : WordTrace (prefixWord ++ tailWord_375457) baseStart_375457 baseEnd_375457 := by
    simpa [prefixWord, tailWord_375457, baseEnd_375457] using wordTrace_append hprefix tailTrace_375457
  have hstable : (prefixWord ++ tailWord_375457).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375457).length < 2 ^ (prefixWord ++ tailWord_375457).sum := by decide
  have hdescent : baseEnd_375457 < baseStart_375457 := by decide
  rcases family_descends (prefixWord ++ tailWord_375457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375516 : List Nat := [2, 2, 5, 1, 1, 1, 2, 5]
def baseStart_375516 : Nat := 118140960795 + 375516 * 2 ^ 59
def prefixEnd_375516 : Nat := 4983230072969 + 3 ^ 40 * 375516 * 2
def baseEnd_375516 : Nat := 114263823083767718887727

theorem tailTrace_375516 : CollatzResearch.WordTrace tailWord_375516 prefixEnd_375516 114263823083767718887727 := by
  unfold tailWord_375516
  simp only [CollatzResearch.WordTrace]
  refine ⟨6848096853788569936009201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9130795805051426581345601 6848096853788569936009201)
  ·
    refine ⟨5136072640341427452006901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6848096853788569936009201 5136072640341427452006901)
    ·
      refine ⟨481506810032008823625647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5136072640341427452006901 481506810032008823625647)
      ·
        refine ⟨722260215048013235438471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481506810032008823625647 722260215048013235438471)
        ·
          refine ⟨1083390322572019853157707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722260215048013235438471 1083390322572019853157707)
          ·
            refine ⟨1625085483858029779736561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083390322572019853157707 1625085483858029779736561)
            ·
              refine ⟨1218814112893522334802421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625085483858029779736561 1218814112893522334802421)
              ·
                refine ⟨114263823083767718887727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1218814112893522334802421 114263823083767718887727)
                ·
                  rfl

theorem cell19_375516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_375516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375516 prefixEnd_375516 := by exact prefixLift 375516
  have htrace : WordTrace (prefixWord ++ tailWord_375516) baseStart_375516 baseEnd_375516 := by
    simpa [prefixWord, tailWord_375516, baseEnd_375516] using wordTrace_append hprefix tailTrace_375516
  have hstable : (prefixWord ++ tailWord_375516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375516).length < 2 ^ (prefixWord ++ tailWord_375516).sum := by decide
  have hdescent : baseEnd_375516 < baseStart_375516 := by decide
  rcases family_descends (prefixWord ++ tailWord_375516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375554 : List Nat := [3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_375554 : Nat := 118140960795 + 375554 * 2 ^ 59
def prefixEnd_375554 : Nat := 4983230072969 + 3 ^ 40 * 375554 * 2
def baseEnd_375554 : Nat := 114275385907394890043179

theorem tailTrace_375554 : CollatzResearch.WordTrace tailWord_375554 prefixEnd_375554 114275385907394890043179 := by
  unfold tailWord_375554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424394920359868090475429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9131719787626314907934477 3424394920359868090475429)
  ·
    refine ⟨642074047567475266964143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3424394920359868090475429 642074047567475266964143)
    ·
      refine ⟨963111071351212900446215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642074047567475266964143 963111071351212900446215)
      ·
        refine ⟨1444666607026819350669323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963111071351212900446215 1444666607026819350669323)
        ·
          refine ⟨2166999910540229026003985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444666607026819350669323 2166999910540229026003985)
          ·
            refine ⟨1625249932905171769502989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2166999910540229026003985 1625249932905171769502989)
            ·
              refine ⟨609468724839439413563621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1625249932905171769502989 609468724839439413563621)
              ·
                refine ⟨114275385907394890043179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 609468724839439413563621 114275385907394890043179)
                ·
                  rfl

theorem cell19_375554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_375554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375554 prefixEnd_375554 := by exact prefixLift 375554
  have htrace : WordTrace (prefixWord ++ tailWord_375554) baseStart_375554 baseEnd_375554 := by
    simpa [prefixWord, tailWord_375554, baseEnd_375554] using wordTrace_append hprefix tailTrace_375554
  have hstable : (prefixWord ++ tailWord_375554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375554).length < 2 ^ (prefixWord ++ tailWord_375554).sum := by decide
  have hdescent : baseEnd_375554 < baseStart_375554 := by decide
  rcases family_descends (prefixWord ++ tailWord_375554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375596 : List Nat := [2, 2, 1, 1, 1, 4, 8]
def baseStart_375596 : Nat := 118140960795 + 375596 * 2 ^ 59
def prefixEnd_375596 : Nat := 4983230072969 + 3 ^ 40 * 375596 * 2
def baseEnd_375596 : Nat := 38096055290117079036577

theorem tailTrace_375596 : CollatzResearch.WordTrace tailWord_375596 prefixEnd_375596 38096055290117079036577 := by
  unfold tailWord_375596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6849555773643656767465321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9132741031524875689953761 6849555773643656767465321)
  ·
    refine ⟨5137166830232742575598991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6849555773643656767465321 5137166830232742575598991)
    ·
      refine ⟨7705750245349113863398487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5137166830232742575598991 7705750245349113863398487)
      ·
        refine ⟨11558625368023670795097731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7705750245349113863398487 11558625368023670795097731)
        ·
          refine ⟨17337938052035506192646597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11558625368023670795097731 17337938052035506192646597)
          ·
            refine ⟨3250863384756657411121237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17337938052035506192646597 3250863384756657411121237)
            ·
              refine ⟨38096055290117079036577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3250863384756657411121237 38096055290117079036577)
              ·
                rfl

theorem cell19_375596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_375596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375596 prefixEnd_375596 := by exact prefixLift 375596
  have htrace : WordTrace (prefixWord ++ tailWord_375596) baseStart_375596 baseEnd_375596 := by
    simpa [prefixWord, tailWord_375596, baseEnd_375596] using wordTrace_append hprefix tailTrace_375596
  have hstable : (prefixWord ++ tailWord_375596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375596).length < 2 ^ (prefixWord ++ tailWord_375596).sum := by decide
  have hdescent : baseEnd_375596 < baseStart_375596 := by decide
  rcases family_descends (prefixWord ++ tailWord_375596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375632 : List Nat := [2, 1, 1, 1, 1, 4, 6, 3]
def baseStart_375632 : Nat := 118140960795 + 375632 * 2 ^ 59
def prefixEnd_375632 : Nat := 4983230072969 + 3 ^ 40 * 375632 * 2
def baseEnd_375632 : Nat := 114299120124313820309633

theorem tailTrace_375632 : CollatzResearch.WordTrace tailWord_375632 prefixEnd_375632 114299120124313820309633 := by
  unfold tailWord_375632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6850212287578445841620575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9133616383437927788827433 6850212287578445841620575)
  ·
    refine ⟨10275318431367668762430863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6850212287578445841620575 10275318431367668762430863)
    ·
      refine ⟨15412977647051503143646295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10275318431367668762430863 15412977647051503143646295)
      ·
        refine ⟨23119466470577254715469443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15412977647051503143646295 23119466470577254715469443)
        ·
          refine ⟨34679199705865882073204165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23119466470577254715469443 34679199705865882073204165)
          ·
            refine ⟨6502349944849852888725781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34679199705865882073204165 6502349944849852888725781)
            ·
              refine ⟨304797653664836854159021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6502349944849852888725781 304797653664836854159021)
              ·
                refine ⟨114299120124313820309633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304797653664836854159021 114299120124313820309633)
                ·
                  rfl

theorem cell19_375632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_375632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375632 prefixEnd_375632 := by exact prefixLift 375632
  have htrace : WordTrace (prefixWord ++ tailWord_375632) baseStart_375632 baseEnd_375632 := by
    simpa [prefixWord, tailWord_375632, baseEnd_375632] using wordTrace_append hprefix tailTrace_375632
  have hstable : (prefixWord ++ tailWord_375632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375632).length < 2 ^ (prefixWord ++ tailWord_375632).sum := by decide
  have hdescent : baseEnd_375632 < baseStart_375632 := by decide
  rcases family_descends (prefixWord ++ tailWord_375632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375651 : List Nat := [1, 1, 1, 5, 3, 3, 5]
def baseStart_375651 : Nat := 118140960795 + 375651 * 2 ^ 59
def prefixEnd_375651 : Nat := 4983230072969 + 3 ^ 40 * 375651 * 2
def baseEnd_375651 : Nat := 38101633845375801962453

theorem tailTrace_375651 : CollatzResearch.WordTrace tailWord_375651 prefixEnd_375651 38101633845375801962453 := by
  unfold tailWord_375651
  simp only [CollatzResearch.WordTrace]
  refine ⟨13701117562088057928182807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9134078374725371952121871 13701117562088057928182807)
  ·
    refine ⟨20551676343132086892274211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13701117562088057928182807 20551676343132086892274211)
    ·
      refine ⟨30827514514698130338411317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20551676343132086892274211 30827514514698130338411317)
      ·
        refine ⟨2890079485752949719226061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30827514514698130338411317 2890079485752949719226061)
        ·
          refine ⟨1083779807157356144709773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2890079485752949719226061 1083779807157356144709773)
          ·
            refine ⟨406417427684008554266165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1083779807157356144709773 406417427684008554266165)
            ·
              refine ⟨38101633845375801962453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 406417427684008554266165 38101633845375801962453)
              ·
                rfl

theorem cell19_375651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_375651 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375651 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375651 prefixEnd_375651 := by exact prefixLift 375651
  have htrace : WordTrace (prefixWord ++ tailWord_375651) baseStart_375651 baseEnd_375651 := by
    simpa [prefixWord, tailWord_375651, baseEnd_375651] using wordTrace_append hprefix tailTrace_375651
  have hstable : (prefixWord ++ tailWord_375651).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375651).length < 2 ^ (prefixWord ++ tailWord_375651).sum := by decide
  have hdescent : baseEnd_375651 < baseStart_375651 := by decide
  rcases family_descends (prefixWord ++ tailWord_375651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375653 : List Nat := [1, 3, 1, 3, 1, 1, 9]
def baseStart_375653 : Nat := 118140960795 + 375653 * 2 ^ 59
def prefixEnd_375653 : Nat := 4983230072969 + 3 ^ 40 * 375653 * 2
def baseEnd_375653 : Nat := 38101836701930664614303

theorem tailTrace_375653 : CollatzResearch.WordTrace tailWord_375653 prefixEnd_375653 38101836701930664614303 := by
  unfold tailWord_375653
  simp only [CollatzResearch.WordTrace]
  refine ⟨13701190508080812269755613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9134127005387208179837075 13701190508080812269755613)
  ·
    refine ⟨5137946440530304601158355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13701190508080812269755613 5137946440530304601158355)
    ·
      refine ⟨7706919660795456901737533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5137946440530304601158355 7706919660795456901737533)
      ·
        refine ⟨2890094872798296338151575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7706919660795456901737533 2890094872798296338151575)
        ·
          refine ⟨4335142309197444507227363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2890094872798296338151575 4335142309197444507227363)
          ·
            refine ⟨6502713463796166760841045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335142309197444507227363 6502713463796166760841045)
            ·
              refine ⟨38101836701930664614303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6502713463796166760841045 38101836701930664614303)
              ·
                rfl

theorem cell19_375653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_375653 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375653 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375653 prefixEnd_375653 := by exact prefixLift 375653
  have htrace : WordTrace (prefixWord ++ tailWord_375653) baseStart_375653 baseEnd_375653 := by
    simpa [prefixWord, tailWord_375653, baseEnd_375653] using wordTrace_append hprefix tailTrace_375653
  have hstable : (prefixWord ++ tailWord_375653).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375653).length < 2 ^ (prefixWord ++ tailWord_375653).sum := by decide
  have hdescent : baseEnd_375653 < baseStart_375653 := by decide
  rcases family_descends (prefixWord ++ tailWord_375653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375691 : List Nat := [1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_375691 : Nat := 118140960795 + 375691 * 2 ^ 59
def prefixEnd_375691 : Nat := 4983230072969 + 3 ^ 40 * 375691 * 2
def baseEnd_375691 : Nat := 114317072929419164998361

theorem tailTrace_375691 : CollatzResearch.WordTrace tailWord_375691 prefixEnd_375691 114317072929419164998361 := by
  unfold tailWord_375691
  simp only [CollatzResearch.WordTrace]
  refine ⟨13702576481943144759638927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9135050987962096506425951 13702576481943144759638927)
  ·
    refine ⟨20553864722914717139458391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13702576481943144759638927 20553864722914717139458391)
    ·
      refine ⟨30830797084372075709187587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20553864722914717139458391 30830797084372075709187587)
      ·
        refine ⟨46246195626558113563781381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30830797084372075709187587 46246195626558113563781381)
        ·
          refine ⟨8671161679979646293209009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46246195626558113563781381 8671161679979646293209009)
          ·
            refine ⟨6503371259984734719906757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8671161679979646293209009 6503371259984734719906757)
            ·
              refine ⟨1219382111247137759982517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6503371259984734719906757 1219382111247137759982517)
              ·
                refine ⟨114317072929419164998361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1219382111247137759982517 114317072929419164998361)
                ·
                  rfl

theorem cell19_375691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_375691 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375691 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375691 prefixEnd_375691 := by exact prefixLift 375691
  have htrace : WordTrace (prefixWord ++ tailWord_375691) baseStart_375691 baseEnd_375691 := by
    simpa [prefixWord, tailWord_375691, baseEnd_375691] using wordTrace_append hprefix tailTrace_375691
  have hstable : (prefixWord ++ tailWord_375691).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375691).length < 2 ^ (prefixWord ++ tailWord_375691).sum := by decide
  have hdescent : baseEnd_375691 < baseStart_375691 := by decide
  rcases family_descends (prefixWord ++ tailWord_375691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375708 : List Nat := [2, 2, 3, 3, 2, 7]
def baseStart_375708 : Nat := 118140960795 + 375708 * 2 ^ 59
def prefixEnd_375708 : Nat := 4983230072969 + 3 ^ 40 * 375708 * 2
def baseEnd_375708 : Nat := 12702471752396462513393

theorem tailTrace_375708 : CollatzResearch.WordTrace tailWord_375708 prefixEnd_375708 12702471752396462513393 := by
  unfold tailWord_375708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6851598261440778331503889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9135464348587704442005185 6851598261440778331503889)
  ·
    refine ⟨5138698696080583748627917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6851598261440778331503889 5138698696080583748627917)
    ·
      refine ⟨1927012011030218905735469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5138698696080583748627917 1927012011030218905735469)
      ·
        refine ⟨722629504136332089650801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1927012011030218905735469 722629504136332089650801)
        ·
          refine ⟨541972128102249067238101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 722629504136332089650801 541972128102249067238101)
          ·
            refine ⟨12702471752396462513393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 541972128102249067238101 12702471752396462513393)
            ·
              rfl

theorem cell19_375708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 7].length) (baseStart_375708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375708 prefixEnd_375708 := by exact prefixLift 375708
  have htrace : WordTrace (prefixWord ++ tailWord_375708) baseStart_375708 baseEnd_375708 := by
    simpa [prefixWord, tailWord_375708, baseEnd_375708] using wordTrace_append hprefix tailTrace_375708
  have hstable : (prefixWord ++ tailWord_375708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375708).length < 2 ^ (prefixWord ++ tailWord_375708).sum := by decide
  have hdescent : baseEnd_375708 < baseStart_375708 := by decide
  rcases family_descends (prefixWord ++ tailWord_375708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375765 : List Nat := [1, 3, 2, 3, 3, 1, 6]
def baseStart_375765 : Nat := 118140960795 + 375765 * 2 ^ 59
def prefixEnd_375765 : Nat := 4983230072969 + 3 ^ 40 * 375765 * 2
def baseEnd_375765 : Nat := 38113196669002973117905

theorem tailTrace_375765 : CollatzResearch.WordTrace tailWord_375765 prefixEnd_375765 38113196669002973117905 := by
  unfold tailWord_375765
  simp only [CollatzResearch.WordTrace]
  refine ⟨13705275483675055397832749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9136850322450036931888499 13705275483675055397832749)
  ·
    refine ⟨5139478306378145774187281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13705275483675055397832749 5139478306378145774187281)
    ·
      refine ⟨3854608729783609330640461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5139478306378145774187281 3854608729783609330640461)
      ·
        refine ⟨1445478273668853498990173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3854608729783609330640461 1445478273668853498990173)
        ·
          refine ⟨542054352625820062121315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1445478273668853498990173 542054352625820062121315)
          ·
            refine ⟨813081528938730093181973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542054352625820062121315 813081528938730093181973)
            ·
              refine ⟨38113196669002973117905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 813081528938730093181973 38113196669002973117905)
              ·
                rfl

theorem cell19_375765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_375765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375765 prefixEnd_375765 := by exact prefixLift 375765
  have htrace : WordTrace (prefixWord ++ tailWord_375765) baseStart_375765 baseEnd_375765 := by
    simpa [prefixWord, tailWord_375765, baseEnd_375765] using wordTrace_append hprefix tailTrace_375765
  have hstable : (prefixWord ++ tailWord_375765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375765).length < 2 ^ (prefixWord ++ tailWord_375765).sum := by decide
  have hdescent : baseEnd_375765 < baseStart_375765 := by decide
  rcases family_descends (prefixWord ++ tailWord_375765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375797 : List Nat := [1, 3, 5, 2, 1, 2, 2, 3]
def baseStart_375797 : Nat := 118140960795 + 375797 * 2 ^ 59
def prefixEnd_375797 : Nat := 4983230072969 + 3 ^ 40 * 375797 * 2
def baseEnd_375797 : Nat := 114349327121642326642517

theorem tailTrace_375797 : CollatzResearch.WordTrace tailWord_375797 prefixEnd_375797 114349327121642326642517 := by
  unfold tailWord_375797
  simp only [CollatzResearch.WordTrace]
  refine ⟨13706442619559124862997645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9137628413039416575331763 13706442619559124862997645)
  ·
    refine ⟨5139915982334671823624117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13706442619559124862997645 5139915982334671823624117)
    ·
      refine ⟨481867123343875483464761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5139915982334671823624117 481867123343875483464761)
      ·
        refine ⟨361400342507906612598571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481867123343875483464761 361400342507906612598571)
        ·
          refine ⟨542100513761859918897857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361400342507906612598571 542100513761859918897857)
          ·
            refine ⟨406575385321394939173393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542100513761859918897857 406575385321394939173393)
            ·
              refine ⟨304931538991046204380045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406575385321394939173393 304931538991046204380045)
              ·
                refine ⟨114349327121642326642517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304931538991046204380045 114349327121642326642517)
                ·
                  rfl

theorem cell19_375797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 3].length) (baseStart_375797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375797 prefixEnd_375797 := by exact prefixLift 375797
  have htrace : WordTrace (prefixWord ++ tailWord_375797) baseStart_375797 baseEnd_375797 := by
    simpa [prefixWord, tailWord_375797, baseEnd_375797] using wordTrace_append hprefix tailTrace_375797
  have hstable : (prefixWord ++ tailWord_375797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375797).length < 2 ^ (prefixWord ++ tailWord_375797).sum := by decide
  have hdescent : baseEnd_375797 < baseStart_375797 := by decide
  rcases family_descends (prefixWord ++ tailWord_375797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375822 : List Nat := [4, 1, 1, 2, 2, 4, 5]
def baseStart_375822 : Nat := 118140960795 + 375822 * 2 ^ 59
def prefixEnd_375822 : Nat := 4983230072969 + 3 ^ 40 * 375822 * 2
def baseEnd_375822 : Nat := 38118978080816558695631

theorem tailTrace_375822 : CollatzResearch.WordTrace tailWord_375822 prefixEnd_375822 38118978080816558695631 := by
  unfold tailWord_375822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1713419305558569266582215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9138236296312369421771813 1713419305558569266582215)
  ·
    refine ⟨2570128958337853899873323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1713419305558569266582215 2570128958337853899873323)
    ·
      refine ⟨3855193437506780849809985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2570128958337853899873323 3855193437506780849809985)
      ·
        refine ⟨2891395078130085637357489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3855193437506780849809985 2891395078130085637357489)
        ·
          refine ⟨2168546308597564228018117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2891395078130085637357489 2168546308597564228018117)
          ·
            refine ⟨406602432862043292753397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2168546308597564228018117 406602432862043292753397)
            ·
              refine ⟨38118978080816558695631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 406602432862043292753397 38118978080816558695631)
              ·
                rfl

theorem cell19_375822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_375822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375822 prefixEnd_375822 := by exact prefixLift 375822
  have htrace : WordTrace (prefixWord ++ tailWord_375822) baseStart_375822 baseEnd_375822 := by
    simpa [prefixWord, tailWord_375822, baseEnd_375822] using wordTrace_append hprefix tailTrace_375822
  have hstable : (prefixWord ++ tailWord_375822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375822).length < 2 ^ (prefixWord ++ tailWord_375822).sum := by decide
  have hdescent : baseEnd_375822 < baseStart_375822 := by decide
  rcases family_descends (prefixWord ++ tailWord_375822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375841 : List Nat := [1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_375841 : Nat := 118140960795 + 375841 * 2 ^ 59
def prefixEnd_375841 : Nat := 4983230072969 + 3 ^ 40 * 375841 * 2
def baseEnd_375841 : Nat := 114362715654263261664619

theorem tailTrace_375841 : CollatzResearch.WordTrace tailWord_375841 prefixEnd_375841 114362715654263261664619 := by
  unfold tailWord_375841
  simp only [CollatzResearch.WordTrace]
  refine ⟨13708047431399720377599377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9138698287599813585066251 13708047431399720377599377)
  ·
    refine ⟨10281035573549790283199533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13708047431399720377599377 10281035573549790283199533)
    ·
      refine ⟨3855388340081171356199825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10281035573549790283199533 3855388340081171356199825)
      ·
        refine ⟨2891541255060878517149869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3855388340081171356199825 2891541255060878517149869)
        ·
          refine ⟨1084327970647829443931201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2891541255060878517149869 1084327970647829443931201)
          ·
            refine ⟨813245977985872082948401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1084327970647829443931201 813245977985872082948401)
            ·
              refine ⟨609934483489404062211301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813245977985872082948401 609934483489404062211301)
              ·
                refine ⟨114362715654263261664619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 609934483489404062211301 114362715654263261664619)
                ·
                  rfl

theorem cell19_375841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_375841 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375841 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375841 prefixEnd_375841 := by exact prefixLift 375841
  have htrace : WordTrace (prefixWord ++ tailWord_375841) baseStart_375841 baseEnd_375841 := by
    simpa [prefixWord, tailWord_375841, baseEnd_375841] using wordTrace_append hprefix tailTrace_375841
  have hstable : (prefixWord ++ tailWord_375841).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375841).length < 2 ^ (prefixWord ++ tailWord_375841).sum := by decide
  have hdescent : baseEnd_375841 < baseStart_375841 := by decide
  rcases family_descends (prefixWord ++ tailWord_375841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375843 : List Nat := [1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_375843 : Nat := 118140960795 + 375843 * 2 ^ 59
def prefixEnd_375843 : Nat := 4983230072969 + 3 ^ 40 * 375843 * 2
def baseEnd_375843 : Nat := 114363324223927849620169

theorem tailTrace_375843 : CollatzResearch.WordTrace tailWord_375843 prefixEnd_375843 114363324223927849620169 := by
  unfold tailWord_375843
  simp only [CollatzResearch.WordTrace]
  refine ⟨13708120377392474719172183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9138746918261649812781455 13708120377392474719172183)
  ·
    refine ⟨20562180566088712078758275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13708120377392474719172183 20562180566088712078758275)
    ·
      refine ⟨30843270849133068118137413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20562180566088712078758275 30843270849133068118137413)
      ·
        refine ⟨5783113284212450272150765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30843270849133068118137413 5783113284212450272150765)
        ·
          refine ⟨2168667481579668852056537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5783113284212450272150765 2168667481579668852056537)
          ·
            refine ⟨1626500611184751639042403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2168667481579668852056537 1626500611184751639042403)
            ·
              refine ⟨2439750916777127458563605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626500611184751639042403 2439750916777127458563605)
              ·
                refine ⟨114363324223927849620169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2439750916777127458563605 114363324223927849620169)
                ·
                  rfl

theorem cell19_375843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_375843 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375843 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375843 prefixEnd_375843 := by exact prefixLift 375843
  have htrace : WordTrace (prefixWord ++ tailWord_375843) baseStart_375843 baseEnd_375843 := by
    simpa [prefixWord, tailWord_375843, baseEnd_375843] using wordTrace_append hprefix tailTrace_375843
  have hstable : (prefixWord ++ tailWord_375843).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375843).length < 2 ^ (prefixWord ++ tailWord_375843).sum := by decide
  have hdescent : baseEnd_375843 < baseStart_375843 := by decide
  rcases family_descends (prefixWord ++ tailWord_375843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375970 : List Nat := [3, 3, 1, 3, 2, 2, 2, 3]
def baseStart_375970 : Nat := 118140960795 + 375970 * 2 ^ 59
def prefixEnd_375970 : Nat := 4983230072969 + 3 ^ 40 * 375970 * 2
def baseEnd_375970 : Nat := 114401968397629184797601

theorem tailTrace_375970 : CollatzResearch.WordTrace tailWord_375970 prefixEnd_375970 114401968397629184797601 := by
  unfold tailWord_375970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3428188111983093852261341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9141834965288250272696909 3428188111983093852261341)
  ·
    refine ⟨1285570541993660194598003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3428188111983093852261341 1285570541993660194598003)
    ·
      refine ⟨1928355812990490291897005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1285570541993660194598003 1928355812990490291897005)
      ·
        refine ⟨723133429871433859461377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1928355812990490291897005 723133429871433859461377)
        ·
          refine ⟨542350072403575394596033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723133429871433859461377 542350072403575394596033)
          ·
            refine ⟨406762554302681545947025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542350072403575394596033 406762554302681545947025)
            ·
              refine ⟨305071915727011159460269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406762554302681545947025 305071915727011159460269)
              ·
                refine ⟨114401968397629184797601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305071915727011159460269 114401968397629184797601)
                ·
                  rfl

theorem cell19_375970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_375970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375970 prefixEnd_375970 := by exact prefixLift 375970
  have htrace : WordTrace (prefixWord ++ tailWord_375970) baseStart_375970 baseEnd_375970 := by
    simpa [prefixWord, tailWord_375970, baseEnd_375970] using wordTrace_append hprefix tailTrace_375970
  have hstable : (prefixWord ++ tailWord_375970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375970).length < 2 ^ (prefixWord ++ tailWord_375970).sum := by decide
  have hdescent : baseEnd_375970 < baseStart_375970 := by decide
  rcases family_descends (prefixWord ++ tailWord_375970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375972 : List Nat := [2, 3, 1, 2, 3, 3, 2, 3]
def baseStart_375972 : Nat := 118140960795 + 375972 * 2 ^ 59
def prefixEnd_375972 : Nat := 4983230072969 + 3 ^ 40 * 375972 * 2
def baseEnd_375972 : Nat := 114402576967293772753151

theorem tailTrace_375972 : CollatzResearch.WordTrace tailWord_375972 prefixEnd_375972 114402576967293772753151 := by
  unfold tailWord_375972
  simp only [CollatzResearch.WordTrace]
  refine ⟨6856412696962564875309085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9141883595950086500412113 6856412696962564875309085)
  ·
    refine ⟨2571154761360961828240907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6856412696962564875309085 2571154761360961828240907)
    ·
      refine ⟨3856732142041442742361361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571154761360961828240907 3856732142041442742361361)
      ·
        refine ⟨2892549106531082056771021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3856732142041442742361361 2892549106531082056771021)
        ·
          refine ⟨1084705914949155771289133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2892549106531082056771021 1084705914949155771289133)
          ·
            refine ⟨406764718105933414233425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1084705914949155771289133 406764718105933414233425)
            ·
              refine ⟨305073538579450060675069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406764718105933414233425 305073538579450060675069)
              ·
                refine ⟨114402576967293772753151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305073538579450060675069 114402576967293772753151)
                ·
                  rfl

theorem cell19_375972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_375972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_375972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_375972 prefixEnd_375972 := by exact prefixLift 375972
  have htrace : WordTrace (prefixWord ++ tailWord_375972) baseStart_375972 baseEnd_375972 := by
    simpa [prefixWord, tailWord_375972, baseEnd_375972] using wordTrace_append hprefix tailTrace_375972
  have hstable : (prefixWord ++ tailWord_375972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375972).length < 2 ^ (prefixWord ++ tailWord_375972).sum := by decide
  have hdescent : baseEnd_375972 < baseStart_375972 := by decide
  rcases family_descends (prefixWord ++ tailWord_375972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376006 : List Nat := [6, 1, 2, 2, 1, 1, 2, 4]
def baseStart_376006 : Nat := 118140960795 + 376006 * 2 ^ 59
def prefixEnd_376006 : Nat := 4983230072969 + 3 ^ 40 * 376006 * 2
def baseEnd_376006 : Nat := 114412922651591767997503

theorem tailTrace_376006 : CollatzResearch.WordTrace tailWord_376006 prefixEnd_376006 114412922651591767997503 := by
  unfold tailWord_376006
  simp only [CollatzResearch.WordTrace]
  refine ⟨428564546118811048667371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9142710317201302371570581 428564546118811048667371)
  ·
    refine ⟨642846819178216573001057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 428564546118811048667371 642846819178216573001057)
    ·
      refine ⟨482135114383662429750793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 642846819178216573001057 482135114383662429750793)
      ·
        refine ⟨361601335787746822313095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482135114383662429750793 361601335787746822313095)
        ·
          refine ⟨542402003681620233469643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361601335787746822313095 542402003681620233469643)
          ·
            refine ⟨813603005522430350204465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542402003681620233469643 813603005522430350204465)
            ·
              refine ⟨610202254141822762653349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813603005522430350204465 610202254141822762653349)
              ·
                refine ⟨114412922651591767997503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 610202254141822762653349 114412922651591767997503)
                ·
                  rfl

theorem cell19_376006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_376006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376006 prefixEnd_376006 := by exact prefixLift 376006
  have htrace : WordTrace (prefixWord ++ tailWord_376006) baseStart_376006 baseEnd_376006 := by
    simpa [prefixWord, tailWord_376006, baseEnd_376006] using wordTrace_append hprefix tailTrace_376006
  have hstable : (prefixWord ++ tailWord_376006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376006).length < 2 ^ (prefixWord ++ tailWord_376006).sum := by decide
  have hdescent : baseEnd_376006 < baseStart_376006 := by decide
  rcases family_descends (prefixWord ++ tailWord_376006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376033 : List Nat := [1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_376033 : Nat := 118140960795 + 376033 * 2 ^ 59
def prefixEnd_376033 : Nat := 4983230072969 + 3 ^ 40 * 376033 * 2
def baseEnd_376033 : Nat := 114421138342063705397429

theorem tailTrace_376033 : CollatzResearch.WordTrace tailWord_376033 prefixEnd_376033 114421138342063705397429 := by
  unfold tailWord_376033
  simp only [CollatzResearch.WordTrace]
  refine ⟨13715050246704137168588753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9143366831136091445725835 13715050246704137168588753)
  ·
    refine ⟨10286287685028102876441565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13715050246704137168588753 10286287685028102876441565)
    ·
      refine ⟨3857357881885538578665587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10286287685028102876441565 3857357881885538578665587)
      ·
        refine ⟨5786036822828307867998381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3857357881885538578665587 5786036822828307867998381)
        ·
          refine ⟨2169763808560615450499393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5786036822828307867998381 2169763808560615450499393)
          ·
            refine ⟨1627322856420461587874545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2169763808560615450499393 1627322856420461587874545)
            ·
              refine ⟨1220492142315346190905909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1627322856420461587874545 1220492142315346190905909)
              ·
                refine ⟨114421138342063705397429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1220492142315346190905909 114421138342063705397429)
                ·
                  rfl

theorem cell19_376033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_376033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376033 prefixEnd_376033 := by exact prefixLift 376033
  have htrace : WordTrace (prefixWord ++ tailWord_376033) baseStart_376033 baseEnd_376033 := by
    simpa [prefixWord, tailWord_376033, baseEnd_376033] using wordTrace_append hprefix tailTrace_376033
  have hstable : (prefixWord ++ tailWord_376033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376033).length < 2 ^ (prefixWord ++ tailWord_376033).sum := by decide
  have hdescent : baseEnd_376033 < baseStart_376033 := by decide
  rcases family_descends (prefixWord ++ tailWord_376033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376050 : List Nat := [3, 2, 1, 3, 4, 6]
def baseStart_376050 : Nat := 118140960795 + 376050 * 2 ^ 59
def prefixEnd_376050 : Nat := 4983230072969 + 3 ^ 40 * 376050 * 2
def baseEnd_376050 : Nat := 12714034576023633668845

theorem tailTrace_376050 : CollatzResearch.WordTrace tailWord_376050 prefixEnd_376050 12714034576023633668845 := by
  unfold tailWord_376050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3428917571910637267989401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9143780191761699381305069 3428917571910637267989401)
  ·
    refine ⟨2571688178932977950992051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3428917571910637267989401 2571688178932977950992051)
    ·
      refine ⟨3857532268399466926488077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571688178932977950992051 3857532268399466926488077)
      ·
        refine ⟨1446574600649800097433029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3857532268399466926488077 1446574600649800097433029)
        ·
          refine ⟨271232737621837518268693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1446574600649800097433029 271232737621837518268693)
          ·
            refine ⟨12714034576023633668845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 271232737621837518268693 12714034576023633668845)
            ·
              rfl

theorem cell19_376050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 6].length) (baseStart_376050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376050 prefixEnd_376050 := by exact prefixLift 376050
  have htrace : WordTrace (prefixWord ++ tailWord_376050) baseStart_376050 baseEnd_376050 := by
    simpa [prefixWord, tailWord_376050, baseEnd_376050] using wordTrace_append hprefix tailTrace_376050
  have hstable : (prefixWord ++ tailWord_376050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376050).length < 2 ^ (prefixWord ++ tailWord_376050).sum := by decide
  have hdescent : baseEnd_376050 < baseStart_376050 := by decide
  rcases family_descends (prefixWord ++ tailWord_376050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376088 : List Nat := [2, 1, 2, 3, 1, 4, 3, 3]
def baseStart_376088 : Nat := 118140960795 + 376088 * 2 ^ 59
def prefixEnd_376088 : Nat := 4983230072969 + 3 ^ 40 * 376088 * 2
def baseEnd_376088 : Nat := 114437874007839874175057

theorem tailTrace_376088 : CollatzResearch.WordTrace tailWord_376088 prefixEnd_376088 114437874007839874175057 := by
  unfold tailWord_376088
  simp only [CollatzResearch.WordTrace]
  refine ⟨6858528130752440780920459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9144704174336587707893945 6858528130752440780920459)
  ·
    refine ⟨10287792196128661171380689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6858528130752440780920459 10287792196128661171380689)
    ·
      refine ⟨7715844147096495878535517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10287792196128661171380689 7715844147096495878535517)
      ·
        refine ⟨2893441555161185954450819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7715844147096495878535517 2893441555161185954450819)
        ·
          refine ⟨4340162332741778931676229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2893441555161185954450819 4340162332741778931676229)
          ·
            refine ⟨813780437389083549689293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4340162332741778931676229 813780437389083549689293)
            ·
              refine ⟨305167664020906331133485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 813780437389083549689293 305167664020906331133485)
              ·
                refine ⟨114437874007839874175057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305167664020906331133485 114437874007839874175057)
                ·
                  rfl

theorem cell19_376088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_376088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376088 prefixEnd_376088 := by exact prefixLift 376088
  have htrace : WordTrace (prefixWord ++ tailWord_376088) baseStart_376088 baseEnd_376088 := by
    simpa [prefixWord, tailWord_376088, baseEnd_376088] using wordTrace_append hprefix tailTrace_376088
  have hstable : (prefixWord ++ tailWord_376088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376088).length < 2 ^ (prefixWord ++ tailWord_376088).sum := by decide
  have hdescent : baseEnd_376088 < baseStart_376088 := by decide
  rcases family_descends (prefixWord ++ tailWord_376088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376225 : List Nat := [1, 2, 3, 13]
def baseStart_376225 : Nat := 118140960795 + 376225 * 2 ^ 59
def prefixEnd_376225 : Nat := 4983230072969 + 3 ^ 40 * 376225 * 2
def baseEnd_376225 : Nat := 1413327913948940112719

theorem tailTrace_376225 : CollatzResearch.WordTrace tailWord_376225 prefixEnd_376225 1413327913948940112719 := by
  unfold tailWord_376225
  simp only [CollatzResearch.WordTrace]
  refine ⟨13722053062008553959578129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9148035374672369306385419 13722053062008553959578129)
  ·
    refine ⟨10291539796506415469683597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13722053062008553959578129 10291539796506415469683597)
    ·
      refine ⟨3859327423689905801131349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10291539796506415469683597 3859327423689905801131349)
      ·
        refine ⟨1413327913948940112719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3859327423689905801131349 1413327913948940112719)
        ·
          rfl

theorem cell19_376225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 13].length) (baseStart_376225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376225 prefixEnd_376225 := by exact prefixLift 376225
  have htrace : WordTrace (prefixWord ++ tailWord_376225) baseStart_376225 baseEnd_376225 := by
    simpa [prefixWord, tailWord_376225, baseEnd_376225] using wordTrace_append hprefix tailTrace_376225
  have hstable : (prefixWord ++ tailWord_376225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376225).length < 2 ^ (prefixWord ++ tailWord_376225).sum := by decide
  have hdescent : baseEnd_376225 < baseStart_376225 := by decide
  rcases family_descends (prefixWord ++ tailWord_376225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376278 : List Nat := [5, 2, 1, 1, 1, 3, 6]
def baseStart_376278 : Nat := 118140960795 + 376278 * 2 ^ 59
def prefixEnd_376278 : Nat := 4983230072969 + 3 ^ 40 * 376278 * 2
def baseEnd_376278 : Nat := 38165229375325243317439

theorem tailTrace_376278 : CollatzResearch.WordTrace tailWord_376278 prefixEnd_376278 38165229375325243317439 := by
  unfold tailWord_376278
  simp only [CollatzResearch.WordTrace]
  refine ⟨857749133176034000703593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9149324087211029340838325 857749133176034000703593)
  ·
    refine ⟨643311849882025500527695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 857749133176034000703593 643311849882025500527695)
    ·
      refine ⟨964967774823038250791543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643311849882025500527695 964967774823038250791543)
      ·
        refine ⟨1447451662234557376187315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964967774823038250791543 1447451662234557376187315)
        ·
          refine ⟨2171177493351836064280973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447451662234557376187315 2171177493351836064280973)
          ·
            refine ⟨814191560006938524105365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2171177493351836064280973 814191560006938524105365)
            ·
              refine ⟨38165229375325243317439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 814191560006938524105365 38165229375325243317439)
              ·
                rfl

theorem cell19_376278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_376278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376278 prefixEnd_376278 := by exact prefixLift 376278
  have htrace : WordTrace (prefixWord ++ tailWord_376278) baseStart_376278 baseEnd_376278 := by
    simpa [prefixWord, tailWord_376278, baseEnd_376278] using wordTrace_append hprefix tailTrace_376278
  have hstable : (prefixWord ++ tailWord_376278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376278).length < 2 ^ (prefixWord ++ tailWord_376278).sum := by decide
  have hdescent : baseEnd_376278 < baseStart_376278 := by decide
  rcases family_descends (prefixWord ++ tailWord_376278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376339 : List Nat := [1, 1, 1, 2, 1, 6, 7]
def baseStart_376339 : Nat := 118140960795 + 376339 * 2 ^ 59
def prefixEnd_376339 : Nat := 4983230072969 + 3 ^ 40 * 376339 * 2
def baseEnd_376339 : Nat := 38171416500248554198865

theorem tailTrace_376339 : CollatzResearch.WordTrace tailWord_376339 prefixEnd_376339 38171416500248554198865 := by
  unfold tailWord_376339
  simp only [CollatzResearch.WordTrace]
  refine ⟨13726210983595551429228071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9150807322397034286152047 13726210983595551429228071)
  ·
    refine ⟨20589316475393327143842107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13726210983595551429228071 20589316475393327143842107)
    ·
      refine ⟨30883974713089990715763161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20589316475393327143842107 30883974713089990715763161)
      ·
        refine ⟨23162981034817493036822371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30883974713089990715763161 23162981034817493036822371)
        ·
          refine ⟨34744471552226239555233557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23162981034817493036822371 34744471552226239555233557)
          ·
            refine ⟨1628647104010604979151573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34744471552226239555233557 1628647104010604979151573)
            ·
              refine ⟨38171416500248554198865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1628647104010604979151573 38171416500248554198865)
              ·
                rfl

theorem cell19_376339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_376339 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376339 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376339 prefixEnd_376339 := by exact prefixLift 376339
  have htrace : WordTrace (prefixWord ++ tailWord_376339) baseStart_376339 baseEnd_376339 := by
    simpa [prefixWord, tailWord_376339, baseEnd_376339] using wordTrace_append hprefix tailTrace_376339
  have hstable : (prefixWord ++ tailWord_376339).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376339).length < 2 ^ (prefixWord ++ tailWord_376339).sum := by decide
  have hdescent : baseEnd_376339 < baseStart_376339 := by decide
  rcases family_descends (prefixWord ++ tailWord_376339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376390 : List Nat := [6, 1, 1, 1, 4, 6]
def baseStart_376390 : Nat := 118140960795 + 376390 * 2 ^ 59
def prefixEnd_376390 : Nat := 4983230072969 + 3 ^ 40 * 376390 * 2
def baseEnd_376390 : Nat := 12725529780799183940347

theorem tailTrace_376390 : CollatzResearch.WordTrace tailWord_376390 prefixEnd_376390 12725529780799183940347 := by
  unfold tailWord_376390
  simp only [CollatzResearch.WordTrace]
  refine ⟨429002222075337098104207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9152047404273858092889749 429002222075337098104207)
  ·
    refine ⟨643503333113005647156311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 429002222075337098104207 643503333113005647156311)
    ·
      refine ⟨965254999669508470734467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643503333113005647156311 965254999669508470734467)
      ·
        refine ⟨1447882499504262706101701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965254999669508470734467 1447882499504262706101701)
        ·
          refine ⟨271477968657049257394069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1447882499504262706101701 271477968657049257394069)
          ·
            refine ⟨12725529780799183940347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 271477968657049257394069 12725529780799183940347)
            ·
              rfl

theorem cell19_376390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 6].length) (baseStart_376390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376390 prefixEnd_376390 := by exact prefixLift 376390
  have htrace : WordTrace (prefixWord ++ tailWord_376390) baseStart_376390 baseEnd_376390 := by
    simpa [prefixWord, tailWord_376390, baseEnd_376390] using wordTrace_append hprefix tailTrace_376390
  have hstable : (prefixWord ++ tailWord_376390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376390).length < 2 ^ (prefixWord ++ tailWord_376390).sum := by decide
  have hdescent : baseEnd_376390 < baseStart_376390 := by decide
  rcases family_descends (prefixWord ++ tailWord_376390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376396 : List Nat := [2, 2, 1, 3, 1, 10]
def baseStart_376396 : Nat := 118140960795 + 376396 * 2 ^ 59
def prefixEnd_376396 : Nat := 4983230072969 + 3 ^ 40 * 376396 * 2
def baseEnd_376396 : Nat := 12725732637354046592197

theorem tailTrace_376396 : CollatzResearch.WordTrace tailWord_376396 prefixEnd_376396 12725732637354046592197 := by
  unfold tailWord_376396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6864144972194525082026521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9152193296259366776035361 6864144972194525082026521)
  ·
    refine ⟨5148108729145893811519891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6864144972194525082026521 5148108729145893811519891)
    ·
      refine ⟨7722163093718840717279837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5148108729145893811519891 7722163093718840717279837)
      ·
        refine ⟨2895811160144565268979939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7722163093718840717279837 2895811160144565268979939)
        ·
          refine ⟨4343716740216847903469909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895811160144565268979939 4343716740216847903469909)
          ·
            refine ⟨12725732637354046592197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4343716740216847903469909 12725732637354046592197)
            ·
              rfl

theorem cell19_376396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 10].length) (baseStart_376396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376396 prefixEnd_376396 := by exact prefixLift 376396
  have htrace : WordTrace (prefixWord ++ tailWord_376396) baseStart_376396 baseEnd_376396 := by
    simpa [prefixWord, tailWord_376396, baseEnd_376396] using wordTrace_append hprefix tailTrace_376396
  have hstable : (prefixWord ++ tailWord_376396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376396).length < 2 ^ (prefixWord ++ tailWord_376396).sum := by decide
  have hdescent : baseEnd_376396 < baseStart_376396 := by decide
  rcases family_descends (prefixWord ++ tailWord_376396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376453 : List Nat := [1, 3, 1, 1, 4, 1, 8]
def baseStart_376453 : Nat := 118140960795 + 376453 * 2 ^ 59
def prefixEnd_376453 : Nat := 4983230072969 + 3 ^ 40 * 376453 * 2
def baseEnd_376453 : Nat := 38182979323875725354317

theorem tailTrace_376453 : CollatzResearch.WordTrace tailWord_376453 prefixEnd_376453 38182979323875725354317 := by
  unfold tailWord_376453
  simp only [CollatzResearch.WordTrace]
  refine ⟨13730368905182548898878013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9153579270121699265918675 13730368905182548898878013)
  ·
    refine ⟨5148888339443455837079255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13730368905182548898878013 5148888339443455837079255)
    ·
      refine ⟨7723332509165183755618883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5148888339443455837079255 7723332509165183755618883)
      ·
        refine ⟨11584998763747775633428325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7723332509165183755618883 11584998763747775633428325)
        ·
          refine ⟨2172187268202707931267811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11584998763747775633428325 2172187268202707931267811)
          ·
            refine ⟨3258280902304061896901717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172187268202707931267811 3258280902304061896901717)
            ·
              refine ⟨38182979323875725354317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3258280902304061896901717 38182979323875725354317)
              ·
                rfl

theorem cell19_376453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_376453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376453 prefixEnd_376453 := by exact prefixLift 376453
  have htrace : WordTrace (prefixWord ++ tailWord_376453) baseStart_376453 baseEnd_376453 := by
    simpa [prefixWord, tailWord_376453, baseEnd_376453] using wordTrace_append hprefix tailTrace_376453
  have hstable : (prefixWord ++ tailWord_376453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376453).length < 2 ^ (prefixWord ++ tailWord_376453).sum := by decide
  have hdescent : baseEnd_376453 < baseStart_376453 := by decide
  rcases family_descends (prefixWord ++ tailWord_376453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376508 : List Nat := [2, 2, 2, 3, 1, 4, 5]
def baseStart_376508 : Nat := 118140960795 + 376508 * 2 ^ 59
def prefixEnd_376508 : Nat := 4983230072969 + 3 ^ 40 * 376508 * 2
def baseEnd_376508 : Nat := 38188557879134448280193

theorem tailTrace_376508 : CollatzResearch.WordTrace tailWord_376508 prefixEnd_376508 38188557879134448280193 := by
  unfold tailWord_376508
  simp only [CollatzResearch.WordTrace]
  refine ⟨6866187459991646646065089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9154916613322195528086785 6866187459991646646065089)
  ·
    refine ⟨5149640594993734984548817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6866187459991646646065089 5149640594993734984548817)
    ·
      refine ⟨3862230446245301238411613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5149640594993734984548817 3862230446245301238411613)
      ·
        refine ⟨1448336417341987964404355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3862230446245301238411613 1448336417341987964404355)
        ·
          refine ⟨2172504626012981946606533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448336417341987964404355 2172504626012981946606533)
          ·
            refine ⟨407344617377434114988725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2172504626012981946606533 407344617377434114988725)
            ·
              refine ⟨38188557879134448280193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 407344617377434114988725 38188557879134448280193)
              ·
                rfl

theorem cell19_376508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_376508 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376508 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376508 prefixEnd_376508 := by exact prefixLift 376508
  have htrace : WordTrace (prefixWord ++ tailWord_376508) baseStart_376508 baseEnd_376508 := by
    simpa [prefixWord, tailWord_376508, baseEnd_376508] using wordTrace_append hprefix tailTrace_376508
  have hstable : (prefixWord ++ tailWord_376508).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376508).length < 2 ^ (prefixWord ++ tailWord_376508).sum := by decide
  have hdescent : baseEnd_376508 < baseStart_376508 := by decide
  rcases family_descends (prefixWord ++ tailWord_376508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376525 : List Nat := [1, 6, 2, 1, 1, 1, 1, 6]
def baseStart_376525 : Nat := 118140960795 + 376525 * 2 ^ 59
def prefixEnd_376525 : Nat := 4983230072969 + 3 ^ 40 * 376525 * 2
def baseEnd_376525 : Nat := 114570846479552342462755

theorem tailTrace_376525 : CollatzResearch.WordTrace tailWord_376525 prefixEnd_376525 114570846479552342462755 := by
  unfold tailWord_376525
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732994960921705195499029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9155329973947803463666019 13732994960921705195499029)
  ·
    refine ⟨643734138793204931039017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13732994960921705195499029 643734138793204931039017)
    ·
      refine ⟨482800604094903698279263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 643734138793204931039017 482800604094903698279263)
      ·
        refine ⟨724200906142355547418895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482800604094903698279263 724200906142355547418895)
        ·
          refine ⟨1086301359213533321128343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724200906142355547418895 1086301359213533321128343)
          ·
            refine ⟨1629452038820299981692515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086301359213533321128343 1629452038820299981692515)
            ·
              refine ⟨2444178058230449972538773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629452038820299981692515 2444178058230449972538773)
              ·
                refine ⟨114570846479552342462755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2444178058230449972538773 114570846479552342462755)
                ·
                  rfl

theorem cell19_376525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_376525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376525 prefixEnd_376525 := by exact prefixLift 376525
  have htrace : WordTrace (prefixWord ++ tailWord_376525) baseStart_376525 baseEnd_376525 := by
    simpa [prefixWord, tailWord_376525, baseEnd_376525] using wordTrace_append hprefix tailTrace_376525
  have hstable : (prefixWord ++ tailWord_376525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376525).length < 2 ^ (prefixWord ++ tailWord_376525).sum := by decide
  have hdescent : baseEnd_376525 < baseStart_376525 := by decide
  rcases family_descends (prefixWord ++ tailWord_376525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376529 : List Nat := [1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_376529 : Nat := 118140960795 + 376529 * 2 ^ 59
def prefixEnd_376529 : Nat := 4983230072969 + 3 ^ 40 * 376529 * 2
def baseEnd_376529 : Nat := 114572063618881518373855

theorem tailTrace_376529 : CollatzResearch.WordTrace tailWord_376529 prefixEnd_376529 114572063618881518373855 := by
  unfold tailWord_376529
  simp only [CollatzResearch.WordTrace]
  refine ⟨13733140852907213878644641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9155427235271475919096427 13733140852907213878644641)
  ·
    refine ⟨10299855639680410408983481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13733140852907213878644641 10299855639680410408983481)
    ·
      refine ⟨7724891729760307806737611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10299855639680410408983481 7724891729760307806737611)
      ·
        refine ⟨11587337594640461710106417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7724891729760307806737611 11587337594640461710106417)
        ·
          refine ⟨8690503195980346282579813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11587337594640461710106417 8690503195980346282579813)
          ·
            refine ⟨1629469349246314927983715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8690503195980346282579813 1629469349246314927983715)
            ·
              refine ⟨2444204023869472391975573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629469349246314927983715 2444204023869472391975573)
              ·
                refine ⟨114572063618881518373855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2444204023869472391975573 114572063618881518373855)
                ·
                  rfl

theorem cell19_376529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_376529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376529 prefixEnd_376529 := by exact prefixLift 376529
  have htrace : WordTrace (prefixWord ++ tailWord_376529) baseStart_376529 baseEnd_376529 := by
    simpa [prefixWord, tailWord_376529, baseEnd_376529] using wordTrace_append hprefix tailTrace_376529
  have hstable : (prefixWord ++ tailWord_376529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376529).length < 2 ^ (prefixWord ++ tailWord_376529).sum := by decide
  have hdescent : baseEnd_376529 < baseStart_376529 := by decide
  rcases family_descends (prefixWord ++ tailWord_376529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376548 : List Nat := [2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_376548 : Nat := 118140960795 + 376548 * 2 ^ 59
def prefixEnd_376548 : Nat := 4983230072969 + 3 ^ 40 * 376548 * 2
def baseEnd_376548 : Nat := 114577845030695103951581

theorem tailTrace_376548 : CollatzResearch.WordTrace tailWord_376548 prefixEnd_376548 114577845030695103951581 := by
  unfold tailWord_376548
  simp only [CollatzResearch.WordTrace]
  refine ⟨6866916919919190061793149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9155889226558920082390865 6866916919919190061793149)
  ·
    refine ⟨2575093844969696273172431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6866916919919190061793149 2575093844969696273172431)
    ·
      refine ⟨3862640767454544409758647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2575093844969696273172431 3862640767454544409758647)
      ·
        refine ⟨5793961151181816614637971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3862640767454544409758647 5793961151181816614637971)
        ·
          refine ⟨8690941726772724921956957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793961151181816614637971 8690941726772724921956957)
          ·
            refine ⟨3259103147539771845733859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8690941726772724921956957 3259103147539771845733859)
            ·
              refine ⟨4888654721309657768600789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3259103147539771845733859 4888654721309657768600789)
              ·
                refine ⟨114577845030695103951581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4888654721309657768600789 114577845030695103951581)
                ·
                  rfl

theorem cell19_376548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_376548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376548 prefixEnd_376548 := by exact prefixLift 376548
  have htrace : WordTrace (prefixWord ++ tailWord_376548) baseStart_376548 baseEnd_376548 := by
    simpa [prefixWord, tailWord_376548, baseEnd_376548] using wordTrace_append hprefix tailTrace_376548
  have hstable : (prefixWord ++ tailWord_376548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376548).length < 2 ^ (prefixWord ++ tailWord_376548).sum := by decide
  have hdescent : baseEnd_376548 < baseStart_376548 := by decide
  rcases family_descends (prefixWord ++ tailWord_376548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376565 : List Nat := [1, 3, 6, 9]
def baseStart_376565 : Nat := 118140960795 + 376565 * 2 ^ 59
def prefixEnd_376565 : Nat := 4983230072969 + 3 ^ 40 * 376565 * 2
def baseEnd_376565 : Nat := 1414605158924001253997

theorem tailTrace_376565 : CollatzResearch.WordTrace tailWord_376565 prefixEnd_376565 1414605158924001253997 := by
  unfold tailWord_376565
  simp only [CollatzResearch.WordTrace]
  refine ⟨13734453880776792026955149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9156302587184528017970099 13734453880776792026955149)
  ·
    refine ⟨5150420205291297010108181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13734453880776792026955149 5150420205291297010108181)
    ·
      refine ⟨241425947123029547348821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5150420205291297010108181 241425947123029547348821)
      ·
        refine ⟨1414605158924001253997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 241425947123029547348821 1414605158924001253997)
        ·
          rfl

theorem cell19_376565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 9].length) (baseStart_376565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376565 prefixEnd_376565 := by exact prefixLift 376565
  have htrace : WordTrace (prefixWord ++ tailWord_376565) baseStart_376565 baseEnd_376565 := by
    simpa [prefixWord, tailWord_376565, baseEnd_376565] using wordTrace_append hprefix tailTrace_376565
  have hstable : (prefixWord ++ tailWord_376565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376565).length < 2 ^ (prefixWord ++ tailWord_376565).sum := by decide
  have hdescent : baseEnd_376565 < baseStart_376565 := by decide
  rcases family_descends (prefixWord ++ tailWord_376565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376658 : List Nat := [3, 2, 2, 1, 1, 5, 2, 3]
def baseStart_376658 : Nat := 118140960795 + 376658 * 2 ^ 59
def prefixEnd_376658 : Nat := 4983230072969 + 3 ^ 40 * 376658 * 2
def baseEnd_376658 : Nat := 114611316362247441506837

theorem tailTrace_376658 : CollatzResearch.WordTrace tailWord_376658 prefixEnd_376658 114611316362247441506837 := by
  unfold tailWord_376658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3434461467359967227522657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9158563912959912606727085 3434461467359967227522657)
  ·
    refine ⟨2575846100519975420641993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3434461467359967227522657 2575846100519975420641993)
    ·
      refine ⟨1931884575389981565481495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2575846100519975420641993 1931884575389981565481495)
      ·
        refine ⟨2897826863084972348222243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1931884575389981565481495 2897826863084972348222243)
        ·
          refine ⟨4346740294627458522333365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897826863084972348222243 4346740294627458522333365)
          ·
            refine ⟨407506902621324236468753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4346740294627458522333365 407506902621324236468753)
            ·
              refine ⟨305630176965993177351565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407506902621324236468753 305630176965993177351565)
              ·
                refine ⟨114611316362247441506837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305630176965993177351565 114611316362247441506837)
                ·
                  rfl

theorem cell19_376658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_376658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376658 prefixEnd_376658 := by exact prefixLift 376658
  have htrace : WordTrace (prefixWord ++ tailWord_376658) baseStart_376658 baseEnd_376658 := by
    simpa [prefixWord, tailWord_376658, baseEnd_376658] using wordTrace_append hprefix tailTrace_376658
  have hstable : (prefixWord ++ tailWord_376658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376658).length < 2 ^ (prefixWord ++ tailWord_376658).sum := by decide
  have hdescent : baseEnd_376658 < baseStart_376658 := by decide
  rcases family_descends (prefixWord ++ tailWord_376658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376660 : List Nat := [2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_376660 : Nat := 118140960795 + 376660 * 2 ^ 59
def prefixEnd_376660 : Nat := 4983230072969 + 3 ^ 40 * 376660 * 2
def baseEnd_376660 : Nat := 114611924931912029462387

theorem tailTrace_376660 : CollatzResearch.WordTrace tailWord_376660 prefixEnd_376660 114611924931912029462387 := by
  unfold tailWord_376660
  simp only [CollatzResearch.WordTrace]
  refine ⟨6868959407716311625831717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9158612543621748834442289 6868959407716311625831717)
  ·
    refine ⟨1287929888946808429843447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6868959407716311625831717 1287929888946808429843447)
    ·
      refine ⟨1931894833420212644765171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1287929888946808429843447 1931894833420212644765171)
      ·
        refine ⟨2897842250130318967147757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1931894833420212644765171 2897842250130318967147757)
        ·
          refine ⟨1086690843798869612680409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2897842250130318967147757 1086690843798869612680409)
          ·
            refine ⟨815018132849152209510307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086690843798869612680409 815018132849152209510307)
            ·
              refine ⟨1222527199273728314265461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815018132849152209510307 1222527199273728314265461)
              ·
                refine ⟨114611924931912029462387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1222527199273728314265461 114611924931912029462387)
                ·
                  rfl

theorem cell19_376660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_376660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376660 prefixEnd_376660 := by exact prefixLift 376660
  have htrace : WordTrace (prefixWord ++ tailWord_376660) baseStart_376660 baseEnd_376660 := by
    simpa [prefixWord, tailWord_376660, baseEnd_376660] using wordTrace_append hprefix tailTrace_376660
  have hstable : (prefixWord ++ tailWord_376660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376660).length < 2 ^ (prefixWord ++ tailWord_376660).sum := by decide
  have hdescent : baseEnd_376660 < baseStart_376660 := by decide
  rcases family_descends (prefixWord ++ tailWord_376660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376734 : List Nat := [4, 3, 1, 3, 1, 7]
def baseStart_376734 : Nat := 118140960795 + 376734 * 2 ^ 59
def prefixEnd_376734 : Nat := 4983230072969 + 3 ^ 40 * 376734 * 2
def baseEnd_376734 : Nat := 12737160223277975979749

theorem tailTrace_376734 : CollatzResearch.WordTrace tailWord_376734 prefixEnd_376734 12737160223277975979749 := by
  unfold tailWord_376734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717577227145566736232157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9160411878109689259904837 1717577227145566736232157)
  ·
    refine ⟨644091460179587526087059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1717577227145566736232157 644091460179587526087059)
    ·
      refine ⟨966137190269381289130589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 644091460179587526087059 966137190269381289130589)
      ·
        refine ⟨362301446351017983423971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 966137190269381289130589 362301446351017983423971)
        ·
          refine ⟨543452169526526975135957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362301446351017983423971 543452169526526975135957)
          ·
            refine ⟨12737160223277975979749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 543452169526526975135957 12737160223277975979749)
            ·
              rfl

theorem cell19_376734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 7].length) (baseStart_376734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376734 prefixEnd_376734 := by exact prefixLift 376734
  have htrace : WordTrace (prefixWord ++ tailWord_376734) baseStart_376734 baseEnd_376734 := by
    simpa [prefixWord, tailWord_376734, baseEnd_376734] using wordTrace_append hprefix tailTrace_376734
  have hstable : (prefixWord ++ tailWord_376734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376734).length < 2 ^ (prefixWord ++ tailWord_376734).sum := by decide
  have hdescent : baseEnd_376734 < baseStart_376734 := by decide
  rcases family_descends (prefixWord ++ tailWord_376734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376738 : List Nat := [3, 3, 1, 2, 10]
def baseStart_376738 : Nat := 118140960795 + 376738 * 2 ^ 59
def prefixEnd_376738 : Nat := 4983230072969 + 3 ^ 40 * 376738 * 2
def baseEnd_376738 : Nat := 4245765153660405915883

theorem tailTrace_376738 : CollatzResearch.WordTrace tailWord_376738 prefixEnd_376738 4245765153660405915883 := by
  unfold tailWord_376738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435190927287510643250717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9160509139433361715335245 3435190927287510643250717)
  ·
    refine ⟨1288196597732816491219019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3435190927287510643250717 1288196597732816491219019)
    ·
      refine ⟨1932294896599224736828529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1288196597732816491219019 1932294896599224736828529)
      ·
        refine ⟨1449221172449418552621397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1932294896599224736828529 1449221172449418552621397)
        ·
          refine ⟨4245765153660405915883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1449221172449418552621397 4245765153660405915883)
          ·
            rfl

theorem cell19_376738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 10].length) (baseStart_376738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376738 prefixEnd_376738 := by exact prefixLift 376738
  have htrace : WordTrace (prefixWord ++ tailWord_376738) baseStart_376738 baseEnd_376738 := by
    simpa [prefixWord, tailWord_376738, baseEnd_376738] using wordTrace_append hprefix tailTrace_376738
  have hstable : (prefixWord ++ tailWord_376738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376738).length < 2 ^ (prefixWord ++ tailWord_376738).sum := by decide
  have hdescent : baseEnd_376738 < baseStart_376738 := by decide
  rcases family_descends (prefixWord ++ tailWord_376738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376833 : List Nat := [1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_376833 : Nat := 118140960795 + 376833 * 2 ^ 59
def prefixEnd_376833 : Nat := 4983230072969 + 3 ^ 40 * 376833 * 2
def baseEnd_376833 : Nat := 114664566207898887617471

theorem tailTrace_376833 : CollatzResearch.WordTrace tailWord_376833 prefixEnd_376833 114664566207898887617471 := by
  unfold tailWord_376833
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744228643805873797711153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9162819095870582531807435 13744228643805873797711153)
  ·
    refine ⟨10308171482854405348283365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13744228643805873797711153 10308171482854405348283365)
    ·
      refine ⟨1932782153035201002803131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10308171482854405348283365 1932782153035201002803131)
      ·
        refine ⟨2899173229552801504204697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932782153035201002803131 2899173229552801504204697)
        ·
          refine ⟨2174379922164601128153523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2899173229552801504204697 2174379922164601128153523)
          ·
            refine ⟨3261569883246901692230285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174379922164601128153523 3261569883246901692230285)
            ·
              refine ⟨1223088706217588134586357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3261569883246901692230285 1223088706217588134586357)
              ·
                refine ⟨114664566207898887617471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1223088706217588134586357 114664566207898887617471)
                ·
                  rfl

theorem cell19_376833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_376833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376833 prefixEnd_376833 := by exact prefixLift 376833
  have htrace : WordTrace (prefixWord ++ tailWord_376833) baseStart_376833 baseEnd_376833 := by
    simpa [prefixWord, tailWord_376833, baseEnd_376833] using wordTrace_append hprefix tailTrace_376833
  have hstable : (prefixWord ++ tailWord_376833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376833).length < 2 ^ (prefixWord ++ tailWord_376833).sum := by decide
  have hdescent : baseEnd_376833 < baseStart_376833 := by decide
  rcases family_descends (prefixWord ++ tailWord_376833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376928 : List Nat := [2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_376928 : Nat := 118140960795 + 376928 * 2 ^ 59
def prefixEnd_376928 : Nat := 4983230072969 + 3 ^ 40 * 376928 * 2
def baseEnd_376928 : Nat := 114693473266966815506101

theorem tailTrace_376928 : CollatzResearch.WordTrace tailWord_376928 prefixEnd_376928 114693473266966815506101 := by
  unfold tailWord_376928
  simp only [CollatzResearch.WordTrace]
  refine ⟨6873846789230852511209719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9165129052307803348279625 6873846789230852511209719)
  ·
    refine ⟨10310770183846278766814579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6873846789230852511209719 10310770183846278766814579)
    ·
      refine ⟨15466155275769418150221869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10310770183846278766814579 15466155275769418150221869)
      ·
        refine ⟨5799808228413531806333201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15466155275769418150221869 5799808228413531806333201)
        ·
          refine ⟨4349856171310148854749901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5799808228413531806333201 4349856171310148854749901)
          ·
            refine ⟨1631196064241305820531213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4349856171310148854749901 1631196064241305820531213)
            ·
              refine ⟨611698524090489682699205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1631196064241305820531213 611698524090489682699205)
              ·
                refine ⟨114693473266966815506101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 611698524090489682699205 114693473266966815506101)
                ·
                  rfl

theorem cell19_376928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_376928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_376928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_376928 prefixEnd_376928 := by exact prefixLift 376928
  have htrace : WordTrace (prefixWord ++ tailWord_376928) baseStart_376928 baseEnd_376928 := by
    simpa [prefixWord, tailWord_376928, baseEnd_376928] using wordTrace_append hprefix tailTrace_376928
  have hstable : (prefixWord ++ tailWord_376928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376928).length < 2 ^ (prefixWord ++ tailWord_376928).sum := by decide
  have hdescent : baseEnd_376928 < baseStart_376928 := by decide
  rcases family_descends (prefixWord ++ tailWord_376928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377042 : List Nat := [3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_377042 : Nat := 118140960795 + 377042 * 2 ^ 59
def prefixEnd_377042 : Nat := 4983230072969 + 3 ^ 40 * 377042 * 2
def baseEnd_377042 : Nat := 114728161737848328972457

theorem tailTrace_377042 : CollatzResearch.WordTrace tailWord_377042 prefixEnd_377042 114728161737848328972457 := by
  unfold tailWord_377042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437962875012175623017345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9167901000032468328046253 3437962875012175623017345)
  ·
    refine ⟨2578472156259131717263009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3437962875012175623017345 2578472156259131717263009)
    ·
      refine ⟨1933854117194348787947257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2578472156259131717263009 1933854117194348787947257)
      ·
        refine ⟨1450390587895761590960443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1933854117194348787947257 1450390587895761590960443)
        ·
          refine ⟨2175585881843642386440665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450390587895761590960443 2175585881843642386440665)
          ·
            refine ⟨1631689411382731789830499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2175585881843642386440665 1631689411382731789830499)
            ·
              refine ⟨2447534117074097684745749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631689411382731789830499 2447534117074097684745749)
              ·
                refine ⟨114728161737848328972457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2447534117074097684745749 114728161737848328972457)
                ·
                  rfl

theorem cell19_377042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_377042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377042 prefixEnd_377042 := by exact prefixLift 377042
  have htrace : WordTrace (prefixWord ++ tailWord_377042) baseStart_377042 baseEnd_377042 := by
    simpa [prefixWord, tailWord_377042, baseEnd_377042] using wordTrace_append hprefix tailTrace_377042
  have hstable : (prefixWord ++ tailWord_377042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377042).length < 2 ^ (prefixWord ++ tailWord_377042).sum := by decide
  have hdescent : baseEnd_377042 < baseStart_377042 := by decide
  rcases family_descends (prefixWord ++ tailWord_377042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377061 : List Nat := [1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_377061 : Nat := 118140960795 + 377061 * 2 ^ 59
def prefixEnd_377061 : Nat := 4983230072969 + 3 ^ 40 * 377061 * 2
def baseEnd_377061 : Nat := 114733943149661914550183

theorem tailTrace_377061 : CollatzResearch.WordTrace tailWord_377061 prefixEnd_377061 114733943149661914550183 := by
  unfold tailWord_377061
  simp only [CollatzResearch.WordTrace]
  refine ⟨13752544486979868737011037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9168362991319912491340691 13752544486979868737011037)
  ·
    refine ⟨5157204182617450776379139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13752544486979868737011037 5157204182617450776379139)
    ·
      refine ⟨7735806273926176164568709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5157204182617450776379139 7735806273926176164568709)
      ·
        refine ⟨1450463676361158030856633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7735806273926176164568709 1450463676361158030856633)
        ·
          refine ⟨1087847757270868523142475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1450463676361158030856633 1087847757270868523142475)
          ·
            refine ⟨1631771635906302784713713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087847757270868523142475 1631771635906302784713713)
            ·
              refine ⟨1223828726929727088535285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631771635906302784713713 1223828726929727088535285)
              ·
                refine ⟨114733943149661914550183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1223828726929727088535285 114733943149661914550183)
                ·
                  rfl

theorem cell19_377061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_377061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377061 prefixEnd_377061 := by exact prefixLift 377061
  have htrace : WordTrace (prefixWord ++ tailWord_377061) baseStart_377061 baseEnd_377061 := by
    simpa [prefixWord, tailWord_377061, baseEnd_377061] using wordTrace_append hprefix tailTrace_377061
  have hstable : (prefixWord ++ tailWord_377061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377061).length < 2 ^ (prefixWord ++ tailWord_377061).sum := by decide
  have hdescent : baseEnd_377061 < baseStart_377061 := by decide
  rcases family_descends (prefixWord ++ tailWord_377061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377082 : List Nat := [3, 1, 1, 1, 1, 12]
def baseStart_377082 : Nat := 118140960795 + 377082 * 2 ^ 59
def prefixEnd_377082 : Nat := 4983230072969 + 3 ^ 40 * 377082 * 2
def baseEnd_377082 : Nat := 12748925903460009787051

theorem tailTrace_377082 : CollatzResearch.WordTrace tailWord_377082 prefixEnd_377082 12748925903460009787051 := by
  unfold tailWord_377082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3438327604975947330881375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9168873613269192882350333 3438327604975947330881375)
  ·
    refine ⟨5157491407463920996322063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3438327604975947330881375 5157491407463920996322063)
    ·
      refine ⟨7736237111195881494483095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5157491407463920996322063 7736237111195881494483095)
      ·
        refine ⟨11604355666793822241724643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7736237111195881494483095 11604355666793822241724643)
        ·
          refine ⟨17406533500190733362586965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11604355666793822241724643 17406533500190733362586965)
          ·
            refine ⟨12748925903460009787051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17406533500190733362586965 12748925903460009787051)
            ·
              rfl

theorem cell19_377082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 12].length) (baseStart_377082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377082 prefixEnd_377082 := by exact prefixLift 377082
  have htrace : WordTrace (prefixWord ++ tailWord_377082) baseStart_377082 baseEnd_377082 := by
    simpa [prefixWord, tailWord_377082, baseEnd_377082] using wordTrace_append hprefix tailTrace_377082
  have hstable : (prefixWord ++ tailWord_377082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377082).length < 2 ^ (prefixWord ++ tailWord_377082).sum := by decide
  have hdescent : baseEnd_377082 < baseStart_377082 := by decide
  rcases family_descends (prefixWord ++ tailWord_377082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377095 : List Nat := [1, 1, 4, 5, 1, 2, 1, 4]
def baseStart_377095 : Nat := 118140960795 + 377095 * 2 ^ 59
def prefixEnd_377095 : Nat := 4983230072969 + 3 ^ 40 * 377095 * 2
def baseEnd_377095 : Nat := 114744288833959909794535

theorem tailTrace_377095 : CollatzResearch.WordTrace tailWord_377095 prefixEnd_377095 114744288833959909794535 := by
  unfold tailWord_377095
  simp only [CollatzResearch.WordTrace]
  refine ⟨13753784568856692543748739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9169189712571128362499159 13753784568856692543748739)
  ·
    refine ⟨20630676853285038815623109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13753784568856692543748739 20630676853285038815623109)
    ·
      refine ⟨3868251909990944777929333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20630676853285038815623109 3868251909990944777929333)
      ·
        refine ⟨362648616561651072930875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3868251909990944777929333 362648616561651072930875)
        ·
          refine ⟨543972924842476609396313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362648616561651072930875 543972924842476609396313)
          ·
            refine ⟨407979693631857457047235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543972924842476609396313 407979693631857457047235)
            ·
              refine ⟨611969540447786185570853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407979693631857457047235 611969540447786185570853)
              ·
                refine ⟨114744288833959909794535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 611969540447786185570853 114744288833959909794535)
                ·
                  rfl

theorem cell19_377095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 4].length) (baseStart_377095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377095 prefixEnd_377095 := by exact prefixLift 377095
  have htrace : WordTrace (prefixWord ++ tailWord_377095) baseStart_377095 baseEnd_377095 := by
    simpa [prefixWord, tailWord_377095, baseEnd_377095] using wordTrace_append hprefix tailTrace_377095
  have hstable : (prefixWord ++ tailWord_377095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377095).length < 2 ^ (prefixWord ++ tailWord_377095).sum := by decide
  have hdescent : baseEnd_377095 < baseStart_377095 := by decide
  rcases family_descends (prefixWord ++ tailWord_377095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377137 : List Nat := [1, 2, 2, 3, 4, 1, 6]
def baseStart_377137 : Nat := 118140960795 + 377137 * 2 ^ 59
def prefixEnd_377137 : Nat := 4983230072969 + 3 ^ 40 * 377137 * 2
def baseEnd_377137 : Nat := 38252356265638752287029

theorem tailTrace_377137 : CollatzResearch.WordTrace tailWord_377137 prefixEnd_377137 38252356265638752287029 := by
  unfold tailWord_377137
  simp only [CollatzResearch.WordTrace]
  refine ⟨13755316434704533716777665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9170210956469689144518443 13755316434704533716777665)
  ·
    refine ⟨10316487326028400287583249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13755316434704533716777665 10316487326028400287583249)
    ·
      refine ⟨7737365494521300215687437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10316487326028400287583249 7737365494521300215687437)
      ·
        refine ⟨2901512060445487580882789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7737365494521300215687437 2901512060445487580882789)
        ·
          refine ⟨544033511333528921415523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2901512060445487580882789 544033511333528921415523)
          ·
            refine ⟨816050267000293382123285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544033511333528921415523 816050267000293382123285)
            ·
              refine ⟨38252356265638752287029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 816050267000293382123285 38252356265638752287029)
              ·
                rfl

theorem cell19_377137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_377137 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377137 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377137 prefixEnd_377137 := by exact prefixLift 377137
  have htrace : WordTrace (prefixWord ++ tailWord_377137) baseStart_377137 baseEnd_377137 := by
    simpa [prefixWord, tailWord_377137, baseEnd_377137] using wordTrace_append hprefix tailTrace_377137
  have hstable : (prefixWord ++ tailWord_377137).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377137).length < 2 ^ (prefixWord ++ tailWord_377137).sum := by decide
  have hdescent : baseEnd_377137 < baseStart_377137 := by decide
  rcases family_descends (prefixWord ++ tailWord_377137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377139 : List Nat := [1, 1, 1, 2, 5, 1, 8]
def baseStart_377139 : Nat := 118140960795 + 377139 * 2 ^ 59
def prefixEnd_377139 : Nat := 4983230072969 + 3 ^ 40 * 377139 * 2
def baseEnd_377139 : Nat := 38252559122193614938879

theorem tailTrace_377139 : CollatzResearch.WordTrace tailWord_377139 prefixEnd_377139 38252559122193614938879 := by
  unfold tailWord_377139
  simp only [CollatzResearch.WordTrace]
  refine ⟨13755389380697288058350471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9170259587131525372233647 13755389380697288058350471)
  ·
    refine ⟨20633084071045932087525707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13755389380697288058350471 20633084071045932087525707)
    ·
      refine ⟨30949626106568898131288561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20633084071045932087525707 30949626106568898131288561)
      ·
        refine ⟨23212219579926673598466421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30949626106568898131288561 23212219579926673598466421)
        ·
          refine ⟨2176145585618125649856227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23212219579926673598466421 2176145585618125649856227)
          ·
            refine ⟨3264218378427188474784341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176145585618125649856227 3264218378427188474784341)
            ·
              refine ⟨38252559122193614938879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3264218378427188474784341 38252559122193614938879)
              ·
                rfl

theorem cell19_377139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_377139 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377139 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377139 prefixEnd_377139 := by exact prefixLift 377139
  have htrace : WordTrace (prefixWord ++ tailWord_377139) baseStart_377139 baseEnd_377139 := by
    simpa [prefixWord, tailWord_377139, baseEnd_377139] using wordTrace_append hprefix tailTrace_377139
  have hstable : (prefixWord ++ tailWord_377139).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377139).length < 2 ^ (prefixWord ++ tailWord_377139).sum := by decide
  have hdescent : baseEnd_377139 < baseStart_377139 := by decide
  rcases family_descends (prefixWord ++ tailWord_377139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377194 : List Nat := [3, 1, 3, 3, 1, 1, 7]
def baseStart_377194 : Nat := 118140960795 + 377194 * 2 ^ 59
def prefixEnd_377194 : Nat := 4983230072969 + 3 ^ 40 * 377194 * 2
def baseEnd_377194 : Nat := 38258137677452337864755

theorem tailTrace_377194 : CollatzResearch.WordTrace tailWord_377194 prefixEnd_377194 38258137677452337864755 := by
  unfold tailWord_377194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3439348848874508112900659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9171596930332021634401757 3439348848874508112900659)
  ·
    refine ⟨5159023273311762169350989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3439348848874508112900659 5159023273311762169350989)
    ·
      refine ⟨1934633727491910813506621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5159023273311762169350989 1934633727491910813506621)
      ·
        refine ⟨725487647809466555064983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1934633727491910813506621 725487647809466555064983)
        ·
          refine ⟨1088231471714199832597475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725487647809466555064983 1088231471714199832597475)
          ·
            refine ⟨1632347207571299748896213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088231471714199832597475 1632347207571299748896213)
            ·
              refine ⟨38258137677452337864755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1632347207571299748896213 38258137677452337864755)
              ·
                rfl

theorem cell19_377194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_377194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377194 prefixEnd_377194 := by exact prefixLift 377194
  have htrace : WordTrace (prefixWord ++ tailWord_377194) baseStart_377194 baseEnd_377194 := by
    simpa [prefixWord, tailWord_377194, baseEnd_377194] using wordTrace_append hprefix tailTrace_377194
  have hstable : (prefixWord ++ tailWord_377194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377194).length < 2 ^ (prefixWord ++ tailWord_377194).sum := by decide
  have hdescent : baseEnd_377194 < baseStart_377194 := by decide
  rcases family_descends (prefixWord ++ tailWord_377194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377213 : List Nat := [1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_377213 : Nat := 118140960795 + 377213 * 2 ^ 59
def prefixEnd_377213 : Nat := 4983230072969 + 3 ^ 40 * 377213 * 2
def baseEnd_377213 : Nat := 114780194444170599171991

theorem tailTrace_377213 : CollatzResearch.WordTrace tailWord_377213 prefixEnd_377213 114780194444170599171991 := by
  unfold tailWord_377213
  simp only [CollatzResearch.WordTrace]
  refine ⟨13758088382429198696544293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9172058921619465797696195 13758088382429198696544293)
  ·
    refine ⟨2579641571705474755602055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13758088382429198696544293 2579641571705474755602055)
    ·
      refine ⟨3869462357558212133403083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2579641571705474755602055 3869462357558212133403083)
      ·
        refine ⟨5804193536337318200104625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3869462357558212133403083 5804193536337318200104625)
        ·
          refine ⟨4353145152252988650078469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5804193536337318200104625 4353145152252988650078469)
          ·
            refine ⟨816214716047435371889713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4353145152252988650078469 816214716047435371889713)
            ·
              refine ⟨612161037035576528917285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816214716047435371889713 612161037035576528917285)
              ·
                refine ⟨114780194444170599171991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 612161037035576528917285 114780194444170599171991)
                ·
                  rfl

theorem cell19_377213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_377213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377213 prefixEnd_377213 := by exact prefixLift 377213
  have htrace : WordTrace (prefixWord ++ tailWord_377213) baseStart_377213 baseEnd_377213 := by
    simpa [prefixWord, tailWord_377213, baseEnd_377213] using wordTrace_append hprefix tailTrace_377213
  have hstable : (prefixWord ++ tailWord_377213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377213).length < 2 ^ (prefixWord ++ tailWord_377213).sum := by decide
  have hdescent : baseEnd_377213 < baseStart_377213 := by decide
  rcases family_descends (prefixWord ++ tailWord_377213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377249 : List Nat := [1, 2, 3, 5, 2, 6]
def baseStart_377249 : Nat := 118140960795 + 377249 * 2 ^ 59
def prefixEnd_377249 : Nat := 4983230072969 + 3 ^ 40 * 377249 * 2
def baseEnd_377249 : Nat := 12754572077570353596877

theorem tailTrace_377249 : CollatzResearch.WordTrace tailWord_377249 prefixEnd_377249 12754572077570353596877 := by
  unfold tailWord_377249
  simp only [CollatzResearch.WordTrace]
  refine ⟨13759401410298776844854801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9172934273532517896569867 13759401410298776844854801)
  ·
    refine ⟨10319551057724082633641101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13759401410298776844854801 10319551057724082633641101)
    ·
      refine ⟨3869831646646530987615413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10319551057724082633641101 3869831646646530987615413)
      ·
        refine ⟨362796716873112280088945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3869831646646530987615413 362796716873112280088945)
        ·
          refine ⟨272097537654834210066709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362796716873112280088945 272097537654834210066709)
          ·
            refine ⟨12754572077570353596877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 272097537654834210066709 12754572077570353596877)
            ·
              rfl

theorem cell19_377249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 6].length) (baseStart_377249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377249 prefixEnd_377249 := by exact prefixLift 377249
  have htrace : WordTrace (prefixWord ++ tailWord_377249) baseStart_377249 baseEnd_377249 := by
    simpa [prefixWord, tailWord_377249, baseEnd_377249] using wordTrace_append hprefix tailTrace_377249
  have hstable : (prefixWord ++ tailWord_377249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377249).length < 2 ^ (prefixWord ++ tailWord_377249).sum := by decide
  have hdescent : baseEnd_377249 < baseStart_377249 := by decide
  rcases family_descends (prefixWord ++ tailWord_377249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377329 : List Nat := [1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_377329 : Nat := 118140960795 + 377329 * 2 ^ 59
def prefixEnd_377329 : Nat := 4983230072969 + 3 ^ 40 * 377329 * 2
def baseEnd_377329 : Nat := 114815491484716700593897

theorem tailTrace_377329 : CollatzResearch.WordTrace tailWord_377329 prefixEnd_377329 114815491484716700593897 := by
  unfold tailWord_377329
  simp only [CollatzResearch.WordTrace]
  refine ⟨13762319250008950507767041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9174879500005967005178027 13762319250008950507767041)
  ·
    refine ⟨10321739437506712880825281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13762319250008950507767041 10321739437506712880825281)
    ·
      refine ⟨7741304578130034660618961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10321739437506712880825281 7741304578130034660618961)
      ·
        refine ⟨5805978433597525995464221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7741304578130034660618961 5805978433597525995464221)
        ·
          refine ⟨2177241912599072248299083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5805978433597525995464221 2177241912599072248299083)
          ·
            refine ⟨3265862868898608372448625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177241912599072248299083 3265862868898608372448625)
            ·
              refine ⟨2449397151673956279336469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3265862868898608372448625 2449397151673956279336469)
              ·
                refine ⟨114815491484716700593897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2449397151673956279336469 114815491484716700593897)
                ·
                  rfl

theorem cell19_377329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_377329 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377329 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377329 prefixEnd_377329 := by exact prefixLift 377329
  have htrace : WordTrace (prefixWord ++ tailWord_377329) baseStart_377329 baseEnd_377329 := by
    simpa [prefixWord, tailWord_377329, baseEnd_377329] using wordTrace_append hprefix tailTrace_377329
  have hstable : (prefixWord ++ tailWord_377329).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377329).length < 2 ^ (prefixWord ++ tailWord_377329).sum := by decide
  have hdescent : baseEnd_377329 < baseStart_377329 := by decide
  rcases family_descends (prefixWord ++ tailWord_377329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377384 : List Nat := [2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_377384 : Nat := 118140960795 + 377384 * 2 ^ 59
def prefixEnd_377384 : Nat := 4983230072969 + 3 ^ 40 * 377384 * 2
def baseEnd_377384 : Nat := 114832227150492869371525

theorem tailTrace_377384 : CollatzResearch.WordTrace tailWord_377384 prefixEnd_377384 114832227150492869371525 := by
  unfold tailWord_377384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6882162632404847450509603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9176216843206463267346137 6882162632404847450509603)
  ·
    refine ⟨10323243948607271175764405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6882162632404847450509603 10323243948607271175764405)
    ·
      refine ⟨967804120181931672727913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10323243948607271175764405 967804120181931672727913)
      ·
        refine ⟨725853090136448754545935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 967804120181931672727913 725853090136448754545935)
        ·
          refine ⟨1088779635204673131818903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725853090136448754545935 1088779635204673131818903)
          ·
            refine ⟨1633169452807009697728355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088779635204673131818903 1633169452807009697728355)
            ·
              refine ⟨2449754179210514546592533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633169452807009697728355 2449754179210514546592533)
              ·
                refine ⟨114832227150492869371525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2449754179210514546592533 114832227150492869371525)
                ·
                  rfl

theorem cell19_377384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_377384 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377384 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377384 prefixEnd_377384 := by exact prefixLift 377384
  have htrace : WordTrace (prefixWord ++ tailWord_377384) baseStart_377384 baseEnd_377384 := by
    simpa [prefixWord, tailWord_377384, baseEnd_377384] using wordTrace_append hprefix tailTrace_377384
  have hstable : (prefixWord ++ tailWord_377384).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377384).length < 2 ^ (prefixWord ++ tailWord_377384).sum := by decide
  have hdescent : baseEnd_377384 < baseStart_377384 := by decide
  rcases family_descends (prefixWord ++ tailWord_377384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377441 : List Nat := [1, 2, 3, 1, 1, 6, 1, 4]
def baseStart_377441 : Nat := 118140960795 + 377441 * 2 ^ 59
def prefixEnd_377441 : Nat := 4983230072969 + 3 ^ 40 * 377441 * 2
def baseEnd_377441 : Nat := 114849571385933626104703

theorem tailTrace_377441 : CollatzResearch.WordTrace tailWord_377441 prefixEnd_377441 114849571385933626104703 := by
  unfold tailWord_377441
  simp only [CollatzResearch.WordTrace]
  refine ⟨13766404225603193635844177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9177602817068795757229451 13766404225603193635844177)
  ·
    refine ⟨10324803169202395226883133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13766404225603193635844177 10324803169202395226883133)
    ·
      refine ⟨3871801188450898210081175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10324803169202395226883133 3871801188450898210081175)
      ·
        refine ⟨5807701782676347315121763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3871801188450898210081175 5807701782676347315121763)
        ·
          refine ⟨8711552674014520972682645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5807701782676347315121763 8711552674014520972682645)
          ·
            refine ⟨408354031594430670594499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8711552674014520972682645 408354031594430670594499)
            ·
              refine ⟨612531047391646005891749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408354031594430670594499 612531047391646005891749)
              ·
                refine ⟨114849571385933626104703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 612531047391646005891749 114849571385933626104703)
                ·
                  rfl

theorem cell19_377441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_377441 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377441 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377441 prefixEnd_377441 := by exact prefixLift 377441
  have htrace : WordTrace (prefixWord ++ tailWord_377441) baseStart_377441 baseEnd_377441 := by
    simpa [prefixWord, tailWord_377441, baseEnd_377441] using wordTrace_append hprefix tailTrace_377441
  have hstable : (prefixWord ++ tailWord_377441).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377441).length < 2 ^ (prefixWord ++ tailWord_377441).sum := by decide
  have hdescent : baseEnd_377441 < baseStart_377441 := by decide
  rcases family_descends (prefixWord ++ tailWord_377441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377458 : List Nat := [3, 2, 1, 2, 4, 1, 3, 3]
def baseStart_377458 : Nat := 118140960795 + 377458 * 2 ^ 59
def prefixEnd_377458 : Nat := 4983230072969 + 3 ^ 40 * 377458 * 2
def baseEnd_377458 : Nat := 114854744228082623726879

theorem tailTrace_377458 : CollatzResearch.WordTrace tailWord_377458 prefixEnd_377458 114854744228082623726879 := by
  unfold tailWord_377458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3441756066635401384803257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9178016177694403692808685 3441756066635401384803257)
  ·
    refine ⟨2581317049976551038602443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3441756066635401384803257 2581317049976551038602443)
    ·
      refine ⟨3871975574964826557903665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2581317049976551038602443 3871975574964826557903665)
      ·
        refine ⟨2903981681223619918427749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3871975574964826557903665 2903981681223619918427749)
        ·
          refine ⟨544496565229428734705203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2903981681223619918427749 544496565229428734705203)
          ·
            refine ⟨816744847844143102057805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544496565229428734705203 816744847844143102057805)
            ·
              refine ⟨306279317941553663271677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 816744847844143102057805 306279317941553663271677)
              ·
                refine ⟨114854744228082623726879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306279317941553663271677 114854744228082623726879)
                ·
                  rfl

theorem cell19_377458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_377458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377458 prefixEnd_377458 := by exact prefixLift 377458
  have htrace : WordTrace (prefixWord ++ tailWord_377458) baseStart_377458 baseEnd_377458 := by
    simpa [prefixWord, tailWord_377458, baseEnd_377458] using wordTrace_append hprefix tailTrace_377458
  have hstable : (prefixWord ++ tailWord_377458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377458).length < 2 ^ (prefixWord ++ tailWord_377458).sum := by decide
  have hdescent : baseEnd_377458 < baseStart_377458 := by decide
  rcases family_descends (prefixWord ++ tailWord_377458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377511 : List Nat := [1, 1, 6, 3, 2, 1, 2, 3]
def baseStart_377511 : Nat := 118140960795 + 377511 * 2 ^ 59
def prefixEnd_377511 : Nat := 4983230072969 + 3 ^ 40 * 377511 * 2
def baseEnd_377511 : Nat := 114870871324194204548957

theorem tailTrace_377511 : CollatzResearch.WordTrace tailWord_377511 prefixEnd_377511 114870871324194204548957 := by
  unfold tailWord_377511
  simp only [CollatzResearch.WordTrace]
  refine ⟨13768957335349595590892387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9179304890233063727261591 13768957335349595590892387)
  ·
    refine ⟨20653436003024393386338581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13768957335349595590892387 20653436003024393386338581)
    ·
      refine ⟨968129812641768439984621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20653436003024393386338581 968129812641768439984621)
      ·
        refine ⟨363048679740663164994233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 968129812641768439984621 363048679740663164994233)
        ·
          refine ⟨272286509805497373745675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363048679740663164994233 272286509805497373745675)
          ·
            refine ⟨408429764708246060618513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272286509805497373745675 408429764708246060618513)
            ·
              refine ⟨306322323531184545463885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408429764708246060618513 306322323531184545463885)
              ·
                refine ⟨114870871324194204548957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306322323531184545463885 114870871324194204548957)
                ·
                  rfl

theorem cell19_377511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 3].length) (baseStart_377511 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377511 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377511 prefixEnd_377511 := by exact prefixLift 377511
  have htrace : WordTrace (prefixWord ++ tailWord_377511) baseStart_377511 baseEnd_377511 := by
    simpa [prefixWord, tailWord_377511, baseEnd_377511] using wordTrace_append hprefix tailTrace_377511
  have hstable : (prefixWord ++ tailWord_377511).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377511).length < 2 ^ (prefixWord ++ tailWord_377511).sum := by decide
  have hdescent : baseEnd_377511 < baseStart_377511 := by decide
  rcases family_descends (prefixWord ++ tailWord_377511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377517 : List Nat := [1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_377517 : Nat := 118140960795 + 377517 * 2 ^ 59
def prefixEnd_377517 : Nat := 4983230072969 + 3 ^ 40 * 377517 * 2
def baseEnd_377517 : Nat := 114872697033187968415607

theorem tailTrace_377517 : CollatzResearch.WordTrace tailWord_377517 prefixEnd_377517 114872697033187968415607 := by
  unfold tailWord_377517
  simp only [CollatzResearch.WordTrace]
  refine ⟨13769176173327858615610805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9179450782218572410407203 13769176173327858615610805)
  ·
    refine ⟨1290860266249486745213513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13769176173327858615610805 1290860266249486745213513)
    ·
      refine ⟨968145199687115058910135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1290860266249486745213513 968145199687115058910135)
      ·
        refine ⟨1452217799530672588365203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968145199687115058910135 1452217799530672588365203)
        ·
          refine ⟨2178326699296008882547805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452217799530672588365203 2178326699296008882547805)
          ·
            refine ⟨816872512236003330955427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2178326699296008882547805 816872512236003330955427)
            ·
              refine ⟨1225308768354004996433141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816872512236003330955427 1225308768354004996433141)
              ·
                refine ⟨114872697033187968415607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1225308768354004996433141 114872697033187968415607)
                ·
                  rfl

theorem cell19_377517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_377517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377517 prefixEnd_377517 := by exact prefixLift 377517
  have htrace : WordTrace (prefixWord ++ tailWord_377517) baseStart_377517 baseEnd_377517 := by
    simpa [prefixWord, tailWord_377517, baseEnd_377517] using wordTrace_append hprefix tailTrace_377517
  have hstable : (prefixWord ++ tailWord_377517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377517).length < 2 ^ (prefixWord ++ tailWord_377517).sum := by decide
  have hdescent : baseEnd_377517 < baseStart_377517 := by decide
  rcases family_descends (prefixWord ++ tailWord_377517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377519 : List Nat := [1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_377519 : Nat := 118140960795 + 377519 * 2 ^ 59
def prefixEnd_377519 : Nat := 4983230072969 + 3 ^ 40 * 377519 * 2
def baseEnd_377519 : Nat := 114873305602852556371157

theorem tailTrace_377519 : CollatzResearch.WordTrace tailWord_377519 prefixEnd_377519 114873305602852556371157 := by
  unfold tailWord_377519
  simp only [CollatzResearch.WordTrace]
  refine ⟨13769249119320612957183611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9179499412880408638122407 13769249119320612957183611)
  ·
    refine ⟨20653873678980919435775417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13769249119320612957183611 20653873678980919435775417)
    ·
      refine ⟨15490405259235689576831563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20653873678980919435775417 15490405259235689576831563)
      ·
        refine ⟨23235607888853534365247345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15490405259235689576831563 23235607888853534365247345)
        ·
          refine ⟨17426705916640150773935509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23235607888853534365247345 17426705916640150773935509)
          ·
            refine ⟨816876839842507067528227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17426705916640150773935509 816876839842507067528227)
            ·
              refine ⟨1225315259763760601292341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816876839842507067528227 1225315259763760601292341)
              ·
                refine ⟨114873305602852556371157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1225315259763760601292341 114873305602852556371157)
                ·
                  rfl

theorem cell19_377519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_377519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377519 prefixEnd_377519 := by exact prefixLift 377519
  have htrace : WordTrace (prefixWord ++ tailWord_377519) baseStart_377519 baseEnd_377519 := by
    simpa [prefixWord, tailWord_377519, baseEnd_377519] using wordTrace_append hprefix tailTrace_377519
  have hstable : (prefixWord ++ tailWord_377519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377519).length < 2 ^ (prefixWord ++ tailWord_377519).sum := by decide
  have hdescent : baseEnd_377519 < baseStart_377519 := by decide
  rcases family_descends (prefixWord ++ tailWord_377519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377589 : List Nat := [1, 3, 6, 1, 2, 6]
def baseStart_377589 : Nat := 118140960795 + 377589 * 2 ^ 59
def prefixEnd_377589 : Nat := 4983230072969 + 3 ^ 40 * 377589 * 2
def baseEnd_377589 : Nat := 12766067282345903868379

theorem tailTrace_377589 : CollatzResearch.WordTrace tailWord_377589 prefixEnd_377589 12766067282345903868379 := by
  unfold tailWord_377589
  simp only [CollatzResearch.WordTrace]
  refine ⟨13771802229067014912231821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9181201486044676608154547 13771802229067014912231821)
  ·
    refine ⟨5164425835900130592086933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13771802229067014912231821 5164425835900130592086933)
    ·
      refine ⟨242082461057818621504075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5164425835900130592086933 242082461057818621504075)
      ·
        refine ⟨363123691586727932256113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242082461057818621504075 363123691586727932256113)
        ·
          refine ⟨272342768690045949192085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363123691586727932256113 272342768690045949192085)
          ·
            refine ⟨12766067282345903868379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 272342768690045949192085 12766067282345903868379)
            ·
              rfl

theorem cell19_377589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 6].length) (baseStart_377589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377589 prefixEnd_377589 := by exact prefixLift 377589
  have htrace : WordTrace (prefixWord ++ tailWord_377589) baseStart_377589 baseEnd_377589 := by
    simpa [prefixWord, tailWord_377589, baseEnd_377589] using wordTrace_append hprefix tailTrace_377589
  have hstable : (prefixWord ++ tailWord_377589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377589).length < 2 ^ (prefixWord ++ tailWord_377589).sum := by decide
  have hdescent : baseEnd_377589 < baseStart_377589 := by decide
  rcases family_descends (prefixWord ++ tailWord_377589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377631 : List Nat := [1, 1, 2, 4, 2, 3, 3, 3]
def baseStart_377631 : Nat := 118140960795 + 377631 * 2 ^ 59
def prefixEnd_377631 : Nat := 4983230072969 + 3 ^ 40 * 377631 * 2
def baseEnd_377631 : Nat := 114907385504069481881963

theorem tailTrace_377631 : CollatzResearch.WordTrace tailWord_377631 prefixEnd_377631 114907385504069481881963 := by
  unfold tailWord_377631
  simp only [CollatzResearch.WordTrace]
  refine ⟨13773334094914856085260747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9182222729943237390173831 13773334094914856085260747)
  ·
    refine ⟨20660001142372284127891121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13773334094914856085260747 20660001142372284127891121)
    ·
      refine ⟨15495000856779213095918341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20660001142372284127891121 15495000856779213095918341)
      ·
        refine ⟨2905312660646102455484689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15495000856779213095918341 2905312660646102455484689)
        ·
          refine ⟨2178984495484576841613517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2905312660646102455484689 2178984495484576841613517)
          ·
            refine ⟨817119185806716315605069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2178984495484576841613517 817119185806716315605069)
            ·
              refine ⟨306419694677518618351901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 817119185806716315605069 306419694677518618351901)
              ·
                refine ⟨114907385504069481881963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306419694677518618351901 114907385504069481881963)
                ·
                  rfl

theorem cell19_377631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 3].length) (baseStart_377631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377631 prefixEnd_377631 := by exact prefixLift 377631
  have htrace : WordTrace (prefixWord ++ tailWord_377631) baseStart_377631 baseEnd_377631 := by
    simpa [prefixWord, tailWord_377631, baseEnd_377631] using wordTrace_append hprefix tailTrace_377631
  have hstable : (prefixWord ++ tailWord_377631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377631).length < 2 ^ (prefixWord ++ tailWord_377631).sum := by decide
  have hdescent : baseEnd_377631 < baseStart_377631 := by decide
  rcases family_descends (prefixWord ++ tailWord_377631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377684 : List Nat := [2, 4, 1, 1, 5, 1, 2, 3]
def baseStart_377684 : Nat := 118140960795 + 377684 * 2 ^ 59
def prefixEnd_377684 : Nat := 4983230072969 + 3 ^ 40 * 377684 * 2
def baseEnd_377684 : Nat := 114923512600181062704041

theorem tailTrace_377684 : CollatzResearch.WordTrace tailWord_377684 prefixEnd_377684 114923512600181062704041 := by
  unfold tailWord_377684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887633581861423068470053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9183511442481897424626737 6887633581861423068470053)
  ·
    refine ⟨1291431296599016825338135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6887633581861423068470053 1291431296599016825338135)
    ·
      refine ⟨1937146944898525238007203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291431296599016825338135 1937146944898525238007203)
      ·
        refine ⟨2905720417347787857010805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937146944898525238007203 2905720417347787857010805)
        ·
          refine ⟨272411289126355111594763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2905720417347787857010805 272411289126355111594763)
          ·
            refine ⟨408616933689532667392145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272411289126355111594763 408616933689532667392145)
            ·
              refine ⟨306462700267149500544109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408616933689532667392145 306462700267149500544109)
              ·
                refine ⟨114923512600181062704041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306462700267149500544109 114923512600181062704041)
                ·
                  rfl

theorem cell19_377684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_377684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377684 prefixEnd_377684 := by exact prefixLift 377684
  have htrace : WordTrace (prefixWord ++ tailWord_377684) baseStart_377684 baseEnd_377684 := by
    simpa [prefixWord, tailWord_377684, baseEnd_377684] using wordTrace_append hprefix tailTrace_377684
  have hstable : (prefixWord ++ tailWord_377684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377684).length < 2 ^ (prefixWord ++ tailWord_377684).sum := by decide
  have hdescent : baseEnd_377684 < baseStart_377684 := by decide
  rcases family_descends (prefixWord ++ tailWord_377684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377690 : List Nat := [3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_377690 : Nat := 118140960795 + 377690 * 2 ^ 59
def prefixEnd_377690 : Nat := 4983230072969 + 3 ^ 40 * 377690 * 2
def baseEnd_377690 : Nat := 114925338309174826570691

theorem tailTrace_377690 : CollatzResearch.WordTrace tailWord_377690 prefixEnd_377690 114925338309174826570691 := by
  unfold tailWord_377690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443871500425277290414631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9183657334467406107772349 3443871500425277290414631)
  ·
    refine ⟨5165807250637915935621947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3443871500425277290414631 5165807250637915935621947)
    ·
      refine ⟨7748710875956873903432921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5165807250637915935621947 7748710875956873903432921)
      ·
        refine ⟨5811533156967655427574691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7748710875956873903432921 5811533156967655427574691)
        ·
          refine ⟨8717299735451483141362037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5811533156967655427574691 8717299735451483141362037)
          ·
            refine ⟨817246850198576544502691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8717299735451483141362037 817246850198576544502691)
            ·
              refine ⟨1225870275297864816754037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817246850198576544502691 1225870275297864816754037)
              ·
                refine ⟨114925338309174826570691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1225870275297864816754037 114925338309174826570691)
                ·
                  rfl

theorem cell19_377690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_377690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377690 prefixEnd_377690 := by exact prefixLift 377690
  have htrace : WordTrace (prefixWord ++ tailWord_377690) baseStart_377690 baseEnd_377690 := by
    simpa [prefixWord, tailWord_377690, baseEnd_377690] using wordTrace_append hprefix tailTrace_377690
  have hstable : (prefixWord ++ tailWord_377690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377690).length < 2 ^ (prefixWord ++ tailWord_377690).sum := by decide
  have hdescent : baseEnd_377690 < baseStart_377690 := by decide
  rcases family_descends (prefixWord ++ tailWord_377690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377785 : List Nat := [1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_377785 : Nat := 118140960795 + 377785 * 2 ^ 59
def prefixEnd_377785 : Nat := 4983230072969 + 3 ^ 40 * 377785 * 2
def baseEnd_377785 : Nat := 114954245368242754459321

theorem tailTrace_377785 : CollatzResearch.WordTrace tailWord_377785 prefixEnd_377785 114954245368242754459321 := by
  unfold tailWord_377785
  simp only [CollatzResearch.WordTrace]
  refine ⟨13778950936356940386366809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9185967290904626924244539 13778950936356940386366809)
  ·
    refine ⟨10334213202267705289775107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13778950936356940386366809 10334213202267705289775107)
    ·
      refine ⟨15501319803401557934662661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10334213202267705289775107 15501319803401557934662661)
      ·
        refine ⟨2906497463137792112749249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15501319803401557934662661 2906497463137792112749249)
        ·
          refine ⟨2179873097353344084561937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2906497463137792112749249 2179873097353344084561937)
          ·
            refine ⟨1634904823015008063421453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2179873097353344084561937 1634904823015008063421453)
            ·
              refine ⟨613089308630628023783045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1634904823015008063421453 613089308630628023783045)
              ·
                refine ⟨114954245368242754459321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 613089308630628023783045 114954245368242754459321)
                ·
                  rfl

theorem cell19_377785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_377785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377785 prefixEnd_377785 := by exact prefixLift 377785
  have htrace : WordTrace (prefixWord ++ tailWord_377785) baseStart_377785 baseEnd_377785 := by
    simpa [prefixWord, tailWord_377785, baseEnd_377785] using wordTrace_append hprefix tailTrace_377785
  have hstable : (prefixWord ++ tailWord_377785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377785).length < 2 ^ (prefixWord ++ tailWord_377785).sum := by decide
  have hdescent : baseEnd_377785 < baseStart_377785 := by decide
  rcases family_descends (prefixWord ++ tailWord_377785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377823 : List Nat := [1, 1, 2, 3, 5, 1, 6]
def baseStart_377823 : Nat := 118140960795 + 377823 * 2 ^ 59
def prefixEnd_377823 : Nat := 4983230072969 + 3 ^ 40 * 377823 * 2
def baseEnd_377823 : Nat := 38321936063956641871591

theorem tailTrace_377823 : CollatzResearch.WordTrace tailWord_377823 prefixEnd_377823 38321936063956641871591 := by
  unfold tailWord_377823
  simp only [CollatzResearch.WordTrace]
  refine ⟨13780336910219272876250123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9186891273479515250833415 13780336910219272876250123)
  ·
    refine ⟨20670505365328909314375185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13780336910219272876250123 20670505365328909314375185)
    ·
      refine ⟨15502879023996681985781389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20670505365328909314375185 15502879023996681985781389)
      ·
        refine ⟨5813579633998755744668021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15502879023996681985781389 5813579633998755744668021)
        ·
          refine ⟨545023090687383351062627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5813579633998755744668021 545023090687383351062627)
          ·
            refine ⟨817534636031075026593941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545023090687383351062627 817534636031075026593941)
            ·
              refine ⟨38321936063956641871591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 817534636031075026593941 38321936063956641871591)
              ·
                rfl

theorem cell19_377823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_377823 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377823 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377823 prefixEnd_377823 := by exact prefixLift 377823
  have htrace : WordTrace (prefixWord ++ tailWord_377823) baseStart_377823 baseEnd_377823 := by
    simpa [prefixWord, tailWord_377823, baseEnd_377823] using wordTrace_append hprefix tailTrace_377823
  have hstable : (prefixWord ++ tailWord_377823).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377823).length < 2 ^ (prefixWord ++ tailWord_377823).sum := by decide
  have hdescent : baseEnd_377823 < baseStart_377823 := by decide
  rcases family_descends (prefixWord ++ tailWord_377823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377874 : List Nat := [3, 2, 5, 1, 1, 2, 5]
def baseStart_377874 : Nat := 118140960795 + 377874 * 2 ^ 59
def prefixEnd_377874 : Nat := 4983230072969 + 3 ^ 40 * 377874 * 2
def baseEnd_377874 : Nat := 38327108906105639493767

theorem tailTrace_377874 : CollatzResearch.WordTrace tailWord_377874 prefixEnd_377874 38327108906105639493767 := by
  unfold tailWord_377874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445549258258627146589169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9188131355356339057571117 3445549258258627146589169)
  ·
    refine ⟨2584161943693970359941877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3445549258258627146589169 2584161943693970359941877)
    ·
      refine ⟨242265182221309721244551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2584161943693970359941877 242265182221309721244551)
      ·
        refine ⟨363397773331964581866827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242265182221309721244551 363397773331964581866827)
        ·
          refine ⟨545096659997946872800241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363397773331964581866827 545096659997946872800241)
          ·
            refine ⟨408822494998460154600181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545096659997946872800241 408822494998460154600181)
            ·
              refine ⟨38327108906105639493767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 408822494998460154600181 38327108906105639493767)
              ·
                rfl

theorem cell19_377874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 5].length) (baseStart_377874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377874 prefixEnd_377874 := by exact prefixLift 377874
  have htrace : WordTrace (prefixWord ++ tailWord_377874) baseStart_377874 baseEnd_377874 := by
    simpa [prefixWord, tailWord_377874, baseEnd_377874] using wordTrace_append hprefix tailTrace_377874
  have hstable : (prefixWord ++ tailWord_377874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377874).length < 2 ^ (prefixWord ++ tailWord_377874).sum := by decide
  have hdescent : baseEnd_377874 < baseStart_377874 := by decide
  rcases family_descends (prefixWord ++ tailWord_377874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377880 : List Nat := [2, 1, 2, 3, 2, 4, 5]
def baseStart_377880 : Nat := 118140960795 + 377880 * 2 ^ 59
def prefixEnd_377880 : Nat := 4983230072969 + 3 ^ 40 * 377880 * 2
def baseEnd_377880 : Nat := 38327717475770227449317

theorem tailTrace_377880 : CollatzResearch.WordTrace tailWord_377880 prefixEnd_377880 38327717475770227449317 := by
  unfold tailWord_377880
  simp only [CollatzResearch.WordTrace]
  refine ⟨6891207935506385805537547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9188277247341847740716729 6891207935506385805537547)
  ·
    refine ⟨10336811903259578708306321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6891207935506385805537547 10336811903259578708306321)
    ·
      refine ⟨7752608927444684031229741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10336811903259578708306321 7752608927444684031229741)
      ·
        refine ⟨2907228347791756511711153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7752608927444684031229741 2907228347791756511711153)
        ·
          refine ⟨2180421260843817383783365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2907228347791756511711153 2180421260843817383783365)
          ·
            refine ⟨408828986408215759459381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2180421260843817383783365 408828986408215759459381)
            ·
              refine ⟨38327717475770227449317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 408828986408215759459381 38327717475770227449317)
              ·
                rfl

theorem cell19_377880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_377880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377880 prefixEnd_377880 := by exact prefixLift 377880
  have htrace : WordTrace (prefixWord ++ tailWord_377880) baseStart_377880 baseEnd_377880 := by
    simpa [prefixWord, tailWord_377880, baseEnd_377880] using wordTrace_append hprefix tailTrace_377880
  have hstable : (prefixWord ++ tailWord_377880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377880).length < 2 ^ (prefixWord ++ tailWord_377880).sum := by decide
  have hdescent : baseEnd_377880 < baseStart_377880 := by decide
  rcases family_descends (prefixWord ++ tailWord_377880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377920 : List Nat := [2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_377920 : Nat := 118140960795 + 377920 * 2 ^ 59
def prefixEnd_377920 : Nat := 4983230072969 + 3 ^ 40 * 377920 * 2
def baseEnd_377920 : Nat := 114995323820602441458953

theorem tailTrace_377920 : CollatzResearch.WordTrace tailWord_377920 prefixEnd_377920 114995323820602441458953 := by
  unfold tailWord_377920
  simp only [CollatzResearch.WordTrace]
  refine ⟨6891937395433929221265607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9189249860578572295020809 6891937395433929221265607)
  ·
    refine ⟨10337906093150893831898411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6891937395433929221265607 10337906093150893831898411)
    ·
      refine ⟨15506859139726340747847617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10337906093150893831898411 15506859139726340747847617)
      ·
        refine ⟨11630144354794755560885713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15506859139726340747847617 11630144354794755560885713)
        ·
          refine ⟨8722608266096066670664285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11630144354794755560885713 8722608266096066670664285)
          ·
            refine ⟨3270978099786025001499107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8722608266096066670664285 3270978099786025001499107)
            ·
              refine ⟨4906467149679037502248661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270978099786025001499107 4906467149679037502248661)
              ·
                refine ⟨114995323820602441458953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4906467149679037502248661 114995323820602441458953)
                ·
                  rfl

theorem cell19_377920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_377920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377920 prefixEnd_377920 := by exact prefixLift 377920
  have htrace : WordTrace (prefixWord ++ tailWord_377920) baseStart_377920 baseEnd_377920 := by
    simpa [prefixWord, tailWord_377920, baseEnd_377920] using wordTrace_append hprefix tailTrace_377920
  have hstable : (prefixWord ++ tailWord_377920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377920).length < 2 ^ (prefixWord ++ tailWord_377920).sum := by decide
  have hdescent : baseEnd_377920 < baseStart_377920 := by decide
  rcases family_descends (prefixWord ++ tailWord_377920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377950 : List Nat := [4, 4, 1, 1, 1, 3, 1, 4]
def baseStart_377950 : Nat := 118140960795 + 377950 * 2 ^ 59
def prefixEnd_377950 : Nat := 4983230072969 + 3 ^ 40 * 377950 * 2
def baseEnd_377950 : Nat := 115004452365571260792205

theorem tailTrace_377950 : CollatzResearch.WordTrace tailWord_377950 prefixEnd_377950 115004452365571260792205 := by
  unfold tailWord_377950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723121122594896695765413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9189979320506115710748869 1723121122594896695765413)
  ·
    refine ⟨323085210486543130456015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1723121122594896695765413 323085210486543130456015)
    ·
      refine ⟨484627815729814695684023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323085210486543130456015 484627815729814695684023)
      ·
        refine ⟨726941723594722043526035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484627815729814695684023 726941723594722043526035)
        ·
          refine ⟨1090412585392083065289053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726941723594722043526035 1090412585392083065289053)
          ·
            refine ⟨408904719522031149483395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1090412585392083065289053 408904719522031149483395)
            ·
              refine ⟨613357079283046724225093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408904719522031149483395 613357079283046724225093)
              ·
                refine ⟨115004452365571260792205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 613357079283046724225093 115004452365571260792205)
                ·
                  rfl

theorem cell19_377950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_377950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377950 prefixEnd_377950 := by exact prefixLift 377950
  have htrace : WordTrace (prefixWord ++ tailWord_377950) baseStart_377950 baseEnd_377950 := by
    simpa [prefixWord, tailWord_377950, baseEnd_377950] using wordTrace_append hprefix tailTrace_377950
  have hstable : (prefixWord ++ tailWord_377950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377950).length < 2 ^ (prefixWord ++ tailWord_377950).sum := by decide
  have hdescent : baseEnd_377950 < baseStart_377950 := by decide
  rcases family_descends (prefixWord ++ tailWord_377950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377954 : List Nat := [3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_377954 : Nat := 118140960795 + 377954 * 2 ^ 59
def prefixEnd_377954 : Nat := 4983230072969 + 3 ^ 40 * 377954 * 2
def baseEnd_377954 : Nat := 115005669504900436703305

theorem tailTrace_377954 : CollatzResearch.WordTrace tailWord_377954 prefixEnd_377954 115005669504900436703305 := by
  unfold tailWord_377954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3446278718186170562317229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9190076581829788166179277 3446278718186170562317229)
  ·
    refine ⟨1292354519319813960868961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3446278718186170562317229 1292354519319813960868961)
    ·
      refine ⟨969265889489860470651721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1292354519319813960868961 969265889489860470651721)
      ·
        refine ⟨726949417117395352988791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 969265889489860470651721 726949417117395352988791)
        ·
          refine ⟨1090424125676093029483187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726949417117395352988791 1090424125676093029483187)
          ·
            refine ⟨1635636188514139544224781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090424125676093029483187 1635636188514139544224781)
            ·
              refine ⟨613363570692802329084293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1635636188514139544224781 613363570692802329084293)
              ·
                refine ⟨115005669504900436703305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 613363570692802329084293 115005669504900436703305)
                ·
                  rfl

theorem cell19_377954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_377954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377954 prefixEnd_377954 := by exact prefixLift 377954
  have htrace : WordTrace (prefixWord ++ tailWord_377954) baseStart_377954 baseEnd_377954 := by
    simpa [prefixWord, tailWord_377954, baseEnd_377954] using wordTrace_append hprefix tailTrace_377954
  have hstable : (prefixWord ++ tailWord_377954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377954).length < 2 ^ (prefixWord ++ tailWord_377954).sum := by decide
  have hdescent : baseEnd_377954 < baseStart_377954 := by decide
  rcases family_descends (prefixWord ++ tailWord_377954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377975 : List Nat := [1, 1, 3, 1, 1, 4, 5, 3]
def baseStart_377975 : Nat := 118140960795 + 377975 * 2 ^ 59
def prefixEnd_377975 : Nat := 4983230072969 + 3 ^ 40 * 377975 * 2
def baseEnd_377975 : Nat := 115012059486378610236581

theorem tailTrace_377975 : CollatzResearch.WordTrace tailWord_377975 prefixEnd_377975 115012059486378610236581 := by
  unfold tailWord_377975
  simp only [CollatzResearch.WordTrace]
  refine ⟨13785880805668602835783379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9190587203779068557188919 13785880805668602835783379)
  ·
    refine ⟨20678821208502904253675069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13785880805668602835783379 20678821208502904253675069)
    ·
      refine ⟨7754557953188589095128151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20678821208502904253675069 7754557953188589095128151)
      ·
        refine ⟨11631836929782883642692227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7754557953188589095128151 11631836929782883642692227)
        ·
          refine ⟨17447755394674325464038341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11631836929782883642692227 17447755394674325464038341)
          ·
            refine ⟨3271454136501436024507189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17447755394674325464038341 3271454136501436024507189)
            ·
              refine ⟨306698825297009627297549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3271454136501436024507189 306698825297009627297549)
              ·
                refine ⟨115012059486378610236581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306698825297009627297549 115012059486378610236581)
                ·
                  rfl

theorem cell19_377975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 3].length) (baseStart_377975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_377975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_377975 prefixEnd_377975 := by exact prefixLift 377975
  have htrace : WordTrace (prefixWord ++ tailWord_377975) baseStart_377975 baseEnd_377975 := by
    simpa [prefixWord, tailWord_377975, baseEnd_377975] using wordTrace_append hprefix tailTrace_377975
  have hstable : (prefixWord ++ tailWord_377975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377975).length < 2 ^ (prefixWord ++ tailWord_377975).sum := by decide
  have hdescent : baseEnd_377975 < baseStart_377975 := by decide
  rcases family_descends (prefixWord ++ tailWord_377975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378049 : List Nat := [1, 2, 6, 1, 1, 3, 5]
def baseStart_378049 : Nat := 118140960795 + 378049 * 2 ^ 59
def prefixEnd_378049 : Nat := 4983230072969 + 3 ^ 40 * 378049 * 2
def baseEnd_378049 : Nat := 38344858854656121530645

theorem tailTrace_378049 : CollatzResearch.WordTrace tailWord_378049 prefixEnd_378049 38344858854656121530645 := by
  unfold tailWord_378049
  simp only [CollatzResearch.WordTrace]
  refine ⟨13788579807400513473977201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9192386538267008982651467 13788579807400513473977201)
  ·
    refine ⟨10341434855550385105482901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13788579807400513473977201 10341434855550385105482901)
    ·
      refine ⟨484754758853924301819511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10341434855550385105482901 484754758853924301819511)
      ·
        refine ⟨727132138280886452729267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484754758853924301819511 727132138280886452729267)
        ·
          refine ⟨1090698207421329679093901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727132138280886452729267 1090698207421329679093901)
          ·
            refine ⟨409011827782998629660213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1090698207421329679093901 409011827782998629660213)
            ·
              refine ⟨38344858854656121530645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 409011827782998629660213 38344858854656121530645)
              ·
                rfl

theorem cell19_378049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_378049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378049 prefixEnd_378049 := by exact prefixLift 378049
  have htrace : WordTrace (prefixWord ++ tailWord_378049) baseStart_378049 baseEnd_378049 := by
    simpa [prefixWord, tailWord_378049, baseEnd_378049] using wordTrace_append hprefix tailTrace_378049
  have hstable : (prefixWord ++ tailWord_378049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378049).length < 2 ^ (prefixWord ++ tailWord_378049).sum := by decide
  have hdescent : baseEnd_378049 < baseStart_378049 := by decide
  rcases family_descends (prefixWord ++ tailWord_378049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378091 : List Nat := [1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_378091 : Nat := 118140960795 + 378091 * 2 ^ 59
def prefixEnd_378091 : Nat := 4983230072969 + 3 ^ 40 * 378091 * 2
def baseEnd_378091 : Nat := 115047356526924711658487

theorem tailTrace_378091 : CollatzResearch.WordTrace tailWord_378091 prefixEnd_378091 115047356526924711658487 := by
  unfold tailWord_378091
  simp only [CollatzResearch.WordTrace]
  refine ⟨13790111673248354647006127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9193407782165569764670751 13790111673248354647006127)
  ·
    refine ⟨20685167509872531970509191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13790111673248354647006127 20685167509872531970509191)
    ·
      refine ⟨31027751264808797955763787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20685167509872531970509191 31027751264808797955763787)
      ·
        refine ⟨46541626897213196933645681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31027751264808797955763787 46541626897213196933645681)
        ·
          refine ⟨34906220172909897700234261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46541626897213196933645681 34906220172909897700234261)
          ·
            refine ⟨1636229070605151454698481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34906220172909897700234261 1636229070605151454698481)
            ·
              refine ⟨1227171802953863591023861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636229070605151454698481 1227171802953863591023861)
              ·
                refine ⟨115047356526924711658487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1227171802953863591023861 115047356526924711658487)
                ·
                  rfl

theorem cell19_378091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_378091 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378091 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378091 prefixEnd_378091 := by exact prefixLift 378091
  have htrace : WordTrace (prefixWord ++ tailWord_378091) baseStart_378091 baseEnd_378091 := by
    simpa [prefixWord, tailWord_378091, baseEnd_378091] using wordTrace_append hprefix tailTrace_378091
  have hstable : (prefixWord ++ tailWord_378091).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378091).length < 2 ^ (prefixWord ++ tailWord_378091).sum := by decide
  have hdescent : baseEnd_378091 < baseStart_378091 := by decide
  rcases family_descends (prefixWord ++ tailWord_378091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378108 : List Nat := [2, 2, 2, 1, 6, 6]
def baseStart_378108 : Nat := 118140960795 + 378108 * 2 ^ 59
def prefixEnd_378108 : Nat := 4983230072969 + 3 ^ 40 * 378108 * 2
def baseEnd_378108 : Nat := 12783614374341523253407

theorem tailTrace_378108 : CollatzResearch.WordTrace tailWord_378108 prefixEnd_378108 12783614374341523253407 := by
  unfold tailWord_378108
  simp only [CollatzResearch.WordTrace]
  refine ⟨6895365857093383275187489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9193821142791177700249985 6895365857093383275187489)
  ·
    refine ⟨5171524392820037456390617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6895365857093383275187489 5171524392820037456390617)
    ·
      refine ⟨3878643294615028092292963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5171524392820037456390617 3878643294615028092292963)
      ·
        refine ⟨5817964941922542138439445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878643294615028092292963 5817964941922542138439445)
        ·
          refine ⟨272717106652619162739349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5817964941922542138439445 272717106652619162739349)
          ·
            refine ⟨12783614374341523253407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 272717106652619162739349 12783614374341523253407)
            ·
              rfl

theorem cell19_378108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 6].length) (baseStart_378108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378108 prefixEnd_378108 := by exact prefixLift 378108
  have htrace : WordTrace (prefixWord ++ tailWord_378108) baseStart_378108 baseEnd_378108 := by
    simpa [prefixWord, tailWord_378108, baseEnd_378108] using wordTrace_append hprefix tailTrace_378108
  have hstable : (prefixWord ++ tailWord_378108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378108).length < 2 ^ (prefixWord ++ tailWord_378108).sum := by decide
  have hdescent : baseEnd_378108 < baseStart_378108 := by decide
  rcases family_descends (prefixWord ++ tailWord_378108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378144 : List Nat := [2, 1, 1, 5, 3, 1, 3, 3]
def baseStart_378144 : Nat := 118140960795 + 378144 * 2 ^ 59
def prefixEnd_378144 : Nat := 4983230072969 + 3 ^ 40 * 378144 * 2
def baseEnd_378144 : Nat := 115063483623036292480565

theorem tailTrace_378144 : CollatzResearch.WordTrace tailWord_378144 prefixEnd_378144 115063483623036292480565 := by
  unfold tailWord_378144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6896022371028172349342743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9194696494704229799123657 6896022371028172349342743)
  ·
    refine ⟨10344033556542258524014115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6896022371028172349342743 10344033556542258524014115)
    ·
      refine ⟨15516050334813387786021173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10344033556542258524014115 15516050334813387786021173)
      ·
        refine ⟨1454629718888755104939485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15516050334813387786021173 1454629718888755104939485)
        ·
          refine ⟨545486144583283164352307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1454629718888755104939485 545486144583283164352307)
          ·
            refine ⟨818229216874924746528461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545486144583283164352307 818229216874924746528461)
            ·
              refine ⟨306835956328096779948173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818229216874924746528461 306835956328096779948173)
              ·
                refine ⟨115063483623036292480565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306835956328096779948173 115063483623036292480565)
                ·
                  rfl

theorem cell19_378144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_378144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378144 prefixEnd_378144 := by exact prefixLift 378144
  have htrace : WordTrace (prefixWord ++ tailWord_378144) baseStart_378144 baseEnd_378144 := by
    simpa [prefixWord, tailWord_378144, baseEnd_378144] using wordTrace_append hprefix tailTrace_378144
  have hstable : (prefixWord ++ tailWord_378144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378144).length < 2 ^ (prefixWord ++ tailWord_378144).sum := by decide
  have hdescent : baseEnd_378144 < baseStart_378144 := by decide
  rcases family_descends (prefixWord ++ tailWord_378144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378243 : List Nat := [1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_378243 : Nat := 118140960795 + 378243 * 2 ^ 59
def prefixEnd_378243 : Nat := 4983230072969 + 3 ^ 40 * 378243 * 2
def baseEnd_378243 : Nat := 115093607821433396280295

theorem tailTrace_378243 : CollatzResearch.WordTrace tailWord_378243 prefixEnd_378243 115093607821433396280295 := by
  unfold tailWord_378243
  simp only [CollatzResearch.WordTrace]
  refine ⟨13795655568697684606539383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9197103712465123071026255 13795655568697684606539383)
  ·
    refine ⟨20693483353046526909809075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13795655568697684606539383 20693483353046526909809075)
    ·
      refine ⟨31040225029569790364713613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20693483353046526909809075 31040225029569790364713613)
      ·
        refine ⟨11640084386088671386767605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31040225029569790364713613 11640084386088671386767605)
        ·
          refine ⟨1091257911195812942509463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11640084386088671386767605 1091257911195812942509463)
          ·
            refine ⟨1636886866793719413764195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091257911195812942509463 1636886866793719413764195)
            ·
              refine ⟨2455330300190579120646293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636886866793719413764195 2455330300190579120646293)
              ·
                refine ⟨115093607821433396280295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2455330300190579120646293 115093607821433396280295)
                ·
                  rfl

theorem cell19_378243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_378243 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378243 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378243 prefixEnd_378243 := by exact prefixLift 378243
  have htrace : WordTrace (prefixWord ++ tailWord_378243) baseStart_378243 baseEnd_378243 := by
    simpa [prefixWord, tailWord_378243, baseEnd_378243] using wordTrace_append hprefix tailTrace_378243
  have hstable : (prefixWord ++ tailWord_378243).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378243).length < 2 ^ (prefixWord ++ tailWord_378243).sum := by decide
  have hdescent : baseEnd_378243 < baseStart_378243 := by decide
  rcases family_descends (prefixWord ++ tailWord_378243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378260 : List Nat := [2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_378260 : Nat := 118140960795 + 378260 * 2 ^ 59
def prefixEnd_378260 : Nat := 4983230072969 + 3 ^ 40 * 378260 * 2
def baseEnd_378260 : Nat := 115098780663582393902471

theorem tailTrace_378260 : CollatzResearch.WordTrace tailWord_378260 prefixEnd_378260 115098780663582393902471 := by
  unfold tailWord_378260
  simp only [CollatzResearch.WordTrace]
  refine ⟨6898137804818048254954117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9197517073090731006605489 6898137804818048254954117)
  ·
    refine ⟨1293400838403384047803897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6898137804818048254954117 1293400838403384047803897)
    ·
      refine ⟨970050628802538035852923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1293400838403384047803897 970050628802538035852923)
      ·
        refine ⟨1455075943203807053779385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970050628802538035852923 1455075943203807053779385)
        ·
          refine ⟨1091306957402855290334539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455075943203807053779385 1091306957402855290334539)
          ·
            refine ⟨1636960436104282935501809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091306957402855290334539 1636960436104282935501809)
            ·
              refine ⟨1227720327078212201626357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636960436104282935501809 1227720327078212201626357)
              ·
                refine ⟨115098780663582393902471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1227720327078212201626357 115098780663582393902471)
                ·
                  rfl

theorem cell19_378260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_378260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378260 prefixEnd_378260 := by exact prefixLift 378260
  have htrace : WordTrace (prefixWord ++ tailWord_378260) baseStart_378260 baseEnd_378260 := by
    simpa [prefixWord, tailWord_378260, baseEnd_378260] using wordTrace_append hprefix tailTrace_378260
  have hstable : (prefixWord ++ tailWord_378260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378260).length < 2 ^ (prefixWord ++ tailWord_378260).sum := by decide
  have hdescent : baseEnd_378260 < baseStart_378260 := by decide
  rcases family_descends (prefixWord ++ tailWord_378260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378370 : List Nat := [3, 4, 1, 2, 1, 3, 2, 3]
def baseStart_378370 : Nat := 118140960795 + 378370 * 2 ^ 59
def prefixEnd_378370 : Nat := 4983230072969 + 3 ^ 40 * 378370 * 2
def baseEnd_378370 : Nat := 115132251995134731457727

theorem tailTrace_378370 : CollatzResearch.WordTrace tailWord_378370 prefixEnd_378370 115132251995134731457727 := by
  unfold tailWord_378370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3450071909809396324103141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9200191759491723530941709 3450071909809396324103141)
  ·
    refine ⟨646888483089261810769339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3450071909809396324103141 646888483089261810769339)
    ·
      refine ⟨970332724633892716154009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646888483089261810769339 970332724633892716154009)
      ·
        refine ⟨727749543475419537115507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 970332724633892716154009 727749543475419537115507)
        ·
          refine ⟨1091624315213129305673261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727749543475419537115507 1091624315213129305673261)
          ·
            refine ⟨409359118204923489627473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1091624315213129305673261 409359118204923489627473)
            ·
              refine ⟨307019338653692617220605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409359118204923489627473 307019338653692617220605)
              ·
                refine ⟨115132251995134731457727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307019338653692617220605 115132251995134731457727)
                ·
                  rfl

theorem cell19_378370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_378370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378370 prefixEnd_378370 := by exact prefixLift 378370
  have htrace : WordTrace (prefixWord ++ tailWord_378370) baseStart_378370 baseEnd_378370 := by
    simpa [prefixWord, tailWord_378370, baseEnd_378370] using wordTrace_append hprefix tailTrace_378370
  have hstable : (prefixWord ++ tailWord_378370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378370).length < 2 ^ (prefixWord ++ tailWord_378370).sum := by decide
  have hdescent : baseEnd_378370 < baseStart_378370 := by decide
  rcases family_descends (prefixWord ++ tailWord_378370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378433 : List Nat := [1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_378433 : Nat := 118140960795 + 378433 * 2 ^ 59
def prefixEnd_378433 : Nat := 4983230072969 + 3 ^ 40 * 378433 * 2
def baseEnd_378433 : Nat := 115151421939569252057555

theorem tailTrace_378433 : CollatzResearch.WordTrace tailWord_378433 prefixEnd_378433 115151421939569252057555 := by
  unfold tailWord_378433
  simp only [CollatzResearch.WordTrace]
  refine ⟨13802585438009347055955953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9201723625339564703970635 13802585438009347055955953)
  ·
    refine ⟨10351939078507010291966965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13802585438009347055955953 10351939078507010291966965)
    ·
      refine ⟨970494288610032214871903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10351939078507010291966965 970494288610032214871903)
      ·
        refine ⟨1455741432915048322307855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970494288610032214871903 1455741432915048322307855)
        ·
          refine ⟨2183612149372572483461783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455741432915048322307855 2183612149372572483461783)
          ·
            refine ⟨3275418224058858725192675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183612149372572483461783 3275418224058858725192675)
            ·
              refine ⟨4913127336088288087789013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275418224058858725192675 4913127336088288087789013)
              ·
                refine ⟨115151421939569252057555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4913127336088288087789013 115151421939569252057555)
                ·
                  rfl

theorem cell19_378433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_378433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378433 prefixEnd_378433 := by exact prefixLift 378433
  have htrace : WordTrace (prefixWord ++ tailWord_378433) baseStart_378433 baseEnd_378433 := by
    simpa [prefixWord, tailWord_378433, baseEnd_378433] using wordTrace_append hprefix tailTrace_378433
  have hstable : (prefixWord ++ tailWord_378433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378433).length < 2 ^ (prefixWord ++ tailWord_378433).sum := by decide
  have hdescent : baseEnd_378433 < baseStart_378433 := by decide
  rcases family_descends (prefixWord ++ tailWord_378433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378469 : List Nat := [1, 3, 1, 3, 3, 3, 1, 4]
def baseStart_378469 : Nat := 118140960795 + 378469 * 2 ^ 59
def prefixEnd_378469 : Nat := 4983230072969 + 3 ^ 40 * 378469 * 2
def baseEnd_378469 : Nat := 115162376193531835257457

theorem tailTrace_378469 : CollatzResearch.WordTrace tailWord_378469 prefixEnd_378469 115162376193531835257457 := by
  unfold tailWord_378469
  simp only [CollatzResearch.WordTrace]
  refine ⟨13803898465878925204266461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9202598977252616802844307 13803898465878925204266461)
  ·
    refine ⟨5176461924704596951599923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13803898465878925204266461 5176461924704596951599923)
    ·
      refine ⟨7764692887056895427399885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5176461924704596951599923 7764692887056895427399885)
      ·
        refine ⟨2911759832646335785274957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7764692887056895427399885 2911759832646335785274957)
        ·
          refine ⟨1091909937242375919478109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2911759832646335785274957 1091909937242375919478109)
          ·
            refine ⟨409466226465890969804291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1091909937242375919478109 409466226465890969804291)
            ·
              refine ⟨614199339698836454706437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409466226465890969804291 614199339698836454706437)
              ·
                refine ⟨115162376193531835257457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 614199339698836454706437 115162376193531835257457)
                ·
                  rfl

theorem cell19_378469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_378469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378469 prefixEnd_378469 := by exact prefixLift 378469
  have htrace : WordTrace (prefixWord ++ tailWord_378469) baseStart_378469 baseEnd_378469 := by
    simpa [prefixWord, tailWord_378469, baseEnd_378469] using wordTrace_append hprefix tailTrace_378469
  have hstable : (prefixWord ++ tailWord_378469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378469).length < 2 ^ (prefixWord ++ tailWord_378469).sum := by decide
  have hdescent : baseEnd_378469 < baseStart_378469 := by decide
  rcases family_descends (prefixWord ++ tailWord_378469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378471 : List Nat := [1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_378471 : Nat := 118140960795 + 378471 * 2 ^ 59
def prefixEnd_378471 : Nat := 4983230072969 + 3 ^ 40 * 378471 * 2
def baseEnd_378471 : Nat := 115162984763196423213007

theorem tailTrace_378471 : CollatzResearch.WordTrace tailWord_378471 prefixEnd_378471 115162984763196423213007 := by
  unfold tailWord_378471
  simp only [CollatzResearch.WordTrace]
  refine ⟨13803971411871679545839267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9202647607914453030559511 13803971411871679545839267)
  ·
    refine ⟨20705957117807519318758901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13803971411871679545839267 20705957117807519318758901)
    ·
      refine ⟨1941183479794454936133647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20705957117807519318758901 1941183479794454936133647)
      ·
        refine ⟨2911775219691682404200471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1941183479794454936133647 2911775219691682404200471)
        ·
          refine ⟨4367662829537523606300707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2911775219691682404200471 4367662829537523606300707)
          ·
            refine ⟨6551494244306285409451061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367662829537523606300707 6551494244306285409451061)
            ·
              refine ⟨614202585403714257136037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6551494244306285409451061 614202585403714257136037)
              ·
                refine ⟨115162984763196423213007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 614202585403714257136037 115162984763196423213007)
                ·
                  rfl

theorem cell19_378471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_378471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378471 prefixEnd_378471 := by exact prefixLift 378471
  have htrace : WordTrace (prefixWord ++ tailWord_378471) baseStart_378471 baseEnd_378471 := by
    simpa [prefixWord, tailWord_378471, baseEnd_378471] using wordTrace_append hprefix tailTrace_378471
  have hstable : (prefixWord ++ tailWord_378471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378471).length < 2 ^ (prefixWord ++ tailWord_378471).sum := by decide
  have hdescent : baseEnd_378471 < baseStart_378471 := by decide
  rcases family_descends (prefixWord ++ tailWord_378471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378486 : List Nat := [5, 1, 1, 2, 2, 2, 3, 3]
def baseStart_378486 : Nat := 118140960795 + 378486 * 2 ^ 59
def prefixEnd_378486 : Nat := 4983230072969 + 3 ^ 40 * 378486 * 2
def baseEnd_378486 : Nat := 115167549035680832879633

theorem tailTrace_378486 : CollatzResearch.WordTrace tailWord_378486 prefixEnd_378486 115167549035680832879633 := by
  unfold tailWord_378486
  simp only [CollatzResearch.WordTrace]
  refine ⟨862782406676083569227207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9203012337878224738423541 862782406676083569227207)
  ·
    refine ⟨1294173610014125353840811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 862782406676083569227207 1294173610014125353840811)
    ·
      refine ⟨1941260415021188030761217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1294173610014125353840811 1941260415021188030761217)
      ·
        refine ⟨1455945311265891023070913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1941260415021188030761217 1455945311265891023070913)
        ·
          refine ⟨1091958983449418267303185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455945311265891023070913 1091958983449418267303185)
          ·
            refine ⟨818969237587063700477389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091958983449418267303185 818969237587063700477389)
            ·
              refine ⟨307113464095148887679021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818969237587063700477389 307113464095148887679021)
              ·
                refine ⟨115167549035680832879633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307113464095148887679021 115167549035680832879633)
                ·
                  rfl

theorem cell19_378486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_378486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378486 prefixEnd_378486 := by exact prefixLift 378486
  have htrace : WordTrace (prefixWord ++ tailWord_378486) baseStart_378486 baseEnd_378486 := by
    simpa [prefixWord, tailWord_378486, baseEnd_378486] using wordTrace_append hprefix tailTrace_378486
  have hstable : (prefixWord ++ tailWord_378486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378486).length < 2 ^ (prefixWord ++ tailWord_378486).sum := by decide
  have hdescent : baseEnd_378486 < baseStart_378486 := by decide
  rcases family_descends (prefixWord ++ tailWord_378486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378585 : List Nat := [1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_378585 : Nat := 118140960795 + 378585 * 2 ^ 59
def prefixEnd_378585 : Nat := 4983230072969 + 3 ^ 40 * 378585 * 2
def baseEnd_378585 : Nat := 115197673234077936679363

theorem tailTrace_378585 : CollatzResearch.WordTrace tailWord_378585 prefixEnd_378585 115197673234077936679363 := by
  unfold tailWord_378585
  simp only [CollatzResearch.WordTrace]
  refine ⟨13808129333458677015489209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9205419555639118010326139 13808129333458677015489209)
  ·
    refine ⟨10356097000094007761616907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13808129333458677015489209 10356097000094007761616907)
    ·
      refine ⟨15534145500141011642425361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10356097000094007761616907 15534145500141011642425361)
      ·
        refine ⟨11650609125105758731819021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15534145500141011642425361 11650609125105758731819021)
        ·
          refine ⟨4368978421914659524432133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11650609125105758731819021 4368978421914659524432133)
          ·
            refine ⟨819183454108998660831025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4368978421914659524432133 819183454108998660831025)
            ·
              refine ⟨614387590581748995623269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819183454108998660831025 614387590581748995623269)
              ·
                refine ⟨115197673234077936679363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 614387590581748995623269 115197673234077936679363)
                ·
                  rfl

theorem cell19_378585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_378585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378585 prefixEnd_378585 := by exact prefixLift 378585
  have htrace : WordTrace (prefixWord ++ tailWord_378585) baseStart_378585 baseEnd_378585 := by
    simpa [prefixWord, tailWord_378585, baseEnd_378585] using wordTrace_append hprefix tailTrace_378585
  have hstable : (prefixWord ++ tailWord_378585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378585).length < 2 ^ (prefixWord ++ tailWord_378585).sum := by decide
  have hdescent : baseEnd_378585 < baseStart_378585 := by decide
  rcases family_descends (prefixWord ++ tailWord_378585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378630 : List Nat := [6, 2, 2, 1, 2, 1, 1, 4]
def baseStart_378630 : Nat := 118140960795 + 378630 * 2 ^ 59
def prefixEnd_378630 : Nat := 4983230072969 + 3 ^ 40 * 378630 * 2
def baseEnd_378630 : Nat := 115211366051531165679241

theorem tailTrace_378630 : CollatzResearch.WordTrace tailWord_378630 prefixEnd_378630 115211366051531165679241 := by
  unfold tailWord_378630
  simp only [CollatzResearch.WordTrace]
  refine ⟨431555331821739053152417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9206513745530433133918229 431555331821739053152417)
  ·
    refine ⟨323666498866304289864313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 431555331821739053152417 323666498866304289864313)
    ·
      refine ⟨242749874149728217398235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323666498866304289864313 242749874149728217398235)
      ·
        refine ⟨364124811224592326097353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242749874149728217398235 364124811224592326097353)
        ·
          refine ⟨273093608418444244573015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364124811224592326097353 273093608418444244573015)
          ·
            refine ⟨409640412627666366859523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273093608418444244573015 409640412627666366859523)
            ·
              refine ⟨614460618941499550289285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409640412627666366859523 614460618941499550289285)
              ·
                refine ⟨115211366051531165679241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 614460618941499550289285 115211366051531165679241)
                ·
                  rfl

theorem cell19_378630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_378630 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378630 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378630 prefixEnd_378630 := by exact prefixLift 378630
  have htrace : WordTrace (prefixWord ++ tailWord_378630) baseStart_378630 baseEnd_378630 := by
    simpa [prefixWord, tailWord_378630, baseEnd_378630] using wordTrace_append hprefix tailTrace_378630
  have hstable : (prefixWord ++ tailWord_378630).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378630).length < 2 ^ (prefixWord ++ tailWord_378630).sum := by decide
  have hdescent : baseEnd_378630 < baseStart_378630 := by decide
  rcases family_descends (prefixWord ++ tailWord_378630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378678 : List Nat := [5, 1, 2, 2, 1, 2, 6]
def baseStart_378678 : Nat := 118140960795 + 378678 * 2 ^ 59
def prefixEnd_378678 : Nat := 4983230072969 + 3 ^ 40 * 378678 * 2
def baseEnd_378678 : Nat := 38408657241160425537481

theorem tailTrace_378678 : CollatzResearch.WordTrace tailWord_378678 prefixEnd_378678 38408657241160425537481 := by
  unfold tailWord_378678
  simp only [CollatzResearch.WordTrace]
  refine ⟨863220082632609618664043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9207680881414502599083125 863220082632609618664043)
  ·
    refine ⟨1294830123948914427996065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 863220082632609618664043 1294830123948914427996065)
    ·
      refine ⟨971122592961685820997049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1294830123948914427996065 971122592961685820997049)
      ·
        refine ⟨728341944721264365747787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 971122592961685820997049 728341944721264365747787)
        ·
          refine ⟨1092512917081896548621681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728341944721264365747787 1092512917081896548621681)
          ·
            refine ⟨819384687811422411466261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092512917081896548621681 819384687811422411466261)
            ·
              refine ⟨38408657241160425537481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 819384687811422411466261 38408657241160425537481)
              ·
                rfl

theorem cell19_378678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_378678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378678 prefixEnd_378678 := by exact prefixLift 378678
  have htrace : WordTrace (prefixWord ++ tailWord_378678) baseStart_378678 baseEnd_378678 := by
    simpa [prefixWord, tailWord_378678, baseEnd_378678] using wordTrace_append hprefix tailTrace_378678
  have hstable : (prefixWord ++ tailWord_378678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378678).length < 2 ^ (prefixWord ++ tailWord_378678).sum := by decide
  have hdescent : baseEnd_378678 < baseStart_378678 := by decide
  rcases family_descends (prefixWord ++ tailWord_378678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378716 : List Nat := [2, 2, 4, 2, 2, 1, 1, 5]
def baseStart_378716 : Nat := 118140960795 + 378716 * 2 ^ 59
def prefixEnd_378716 : Nat := 4983230072969 + 3 ^ 40 * 378716 * 2
def baseEnd_378716 : Nat := 115237534547108447767895

theorem tailTrace_378716 : CollatzResearch.WordTrace tailWord_378716 prefixEnd_378716 115237534547108447767895 := by
  unfold tailWord_378716
  simp only [CollatzResearch.WordTrace]
  refine ⟨6906453647992043194254001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9208604863989390925672001 6906453647992043194254001)
  ·
    refine ⟨5179840235994032395690501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6906453647992043194254001 5179840235994032395690501)
    ·
      refine ⟨971220044248881074191969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5179840235994032395690501 971220044248881074191969)
      ·
        refine ⟨728415033186660805643977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 971220044248881074191969 728415033186660805643977)
        ·
          refine ⟨546311274889995604232983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 728415033186660805643977 546311274889995604232983)
          ·
            refine ⟨819466912334993406349475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546311274889995604232983 819466912334993406349475)
            ·
              refine ⟨1229200368502490109524213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819466912334993406349475 1229200368502490109524213)
              ·
                refine ⟨115237534547108447767895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1229200368502490109524213 115237534547108447767895)
                ·
                  rfl

theorem cell19_378716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_378716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378716 prefixEnd_378716 := by exact prefixLift 378716
  have htrace : WordTrace (prefixWord ++ tailWord_378716) baseStart_378716 baseEnd_378716 := by
    simpa [prefixWord, tailWord_378716, baseEnd_378716] using wordTrace_append hprefix tailTrace_378716
  have hstable : (prefixWord ++ tailWord_378716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378716).length < 2 ^ (prefixWord ++ tailWord_378716).sum := by decide
  have hdescent : baseEnd_378716 < baseStart_378716 := by decide
  rcases family_descends (prefixWord ++ tailWord_378716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378777 : List Nat := [1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_378777 : Nat := 118140960795 + 378777 * 2 ^ 59
def prefixEnd_378777 : Nat := 4983230072969 + 3 ^ 40 * 378777 * 2
def baseEnd_378777 : Nat := 115256095921878380412173

theorem tailTrace_378777 : CollatzResearch.WordTrace tailWord_378777 prefixEnd_378777 115256095921878380412173 := by
  unfold tailWord_378777
  simp only [CollatzResearch.WordTrace]
  refine ⟨13815132148763093806478585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9210088099175395870985723 13815132148763093806478585)
  ·
    refine ⟨10361349111572320354858939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13815132148763093806478585 10361349111572320354858939)
    ·
      refine ⟨15542023667358480532288409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10361349111572320354858939 15542023667358480532288409)
      ·
        refine ⟨11656517750518860399216307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15542023667358480532288409 11656517750518860399216307)
        ·
          refine ⟨17484776625778290598824461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11656517750518860399216307 17484776625778290598824461)
          ·
            refine ⟨6556791234666858974559173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17484776625778290598824461 6556791234666858974559173)
            ·
              refine ⟨1229398356500036057729845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6556791234666858974559173 1229398356500036057729845)
              ·
                refine ⟨115256095921878380412173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1229398356500036057729845 115256095921878380412173)
                ·
                  rfl

theorem cell19_378777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_378777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378777 prefixEnd_378777 := by exact prefixLift 378777
  have htrace : WordTrace (prefixWord ++ tailWord_378777) baseStart_378777 baseEnd_378777 := by
    simpa [prefixWord, tailWord_378777, baseEnd_378777] using wordTrace_append hprefix tailTrace_378777
  have hstable : (prefixWord ++ tailWord_378777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378777).length < 2 ^ (prefixWord ++ tailWord_378777).sum := by decide
  have hdescent : baseEnd_378777 < baseStart_378777 := by decide
  rcases family_descends (prefixWord ++ tailWord_378777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378792 : List Nat := [2, 1, 6, 2, 1, 7]
def baseStart_378792 : Nat := 118140960795 + 378792 * 2 ^ 59
def prefixEnd_378792 : Nat := 4983230072969 + 3 ^ 40 * 378792 * 2
def baseEnd_378792 : Nat := 12806740021595865564311

theorem tailTrace_378792 : CollatzResearch.WordTrace tailWord_378792 prefixEnd_378792 12806740021595865564311 := by
  unfold tailWord_378792
  simp only [CollatzResearch.WordTrace]
  refine ⟨6907839621854375684137315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9210452829139167578849753 6907839621854375684137315)
  ·
    refine ⟨10361759432781563526205973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6907839621854375684137315 10361759432781563526205973)
    ·
      refine ⟨485707473411635790290905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10361759432781563526205973 485707473411635790290905)
      ·
        refine ⟨364280605058726842718179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485707473411635790290905 364280605058726842718179)
        ·
          refine ⟨546420907588090264077269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364280605058726842718179 546420907588090264077269)
          ·
            refine ⟨12806740021595865564311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 546420907588090264077269 12806740021595865564311)
            ·
              rfl

theorem cell19_378792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 7].length) (baseStart_378792 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378792 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378792 prefixEnd_378792 := by exact prefixLift 378792
  have htrace : WordTrace (prefixWord ++ tailWord_378792) baseStart_378792 baseEnd_378792 := by
    simpa [prefixWord, tailWord_378792, baseEnd_378792] using wordTrace_append hprefix tailTrace_378792
  have hstable : (prefixWord ++ tailWord_378792).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378792).length < 2 ^ (prefixWord ++ tailWord_378792).sum := by decide
  have hdescent : baseEnd_378792 < baseStart_378792 := by decide
  rcases family_descends (prefixWord ++ tailWord_378792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378813 : List Nat := [1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_378813 : Nat := 118140960795 + 378813 * 2 ^ 59
def prefixEnd_378813 : Nat := 4983230072969 + 3 ^ 40 * 378813 * 2
def baseEnd_378813 : Nat := 115267050175840963612075

theorem tailTrace_378813 : CollatzResearch.WordTrace tailWord_378813 prefixEnd_378813 115267050175840963612075 := by
  unfold tailWord_378813
  simp only [CollatzResearch.WordTrace]
  refine ⟨13816445176632671954789093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9210963451088447969859395 13816445176632671954789093)
  ·
    refine ⟨2590583470618625991522955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13816445176632671954789093 2590583470618625991522955)
    ·
      refine ⟨3885875205927938987284433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2590583470618625991522955 3885875205927938987284433)
      ·
        refine ⟨2914406404445954240463325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3885875205927938987284433 2914406404445954240463325)
        ·
          refine ⟨1092902401667232840173747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2914406404445954240463325 1092902401667232840173747)
          ·
            refine ⟨1639353602500849260260621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092902401667232840173747 1639353602500849260260621)
            ·
              refine ⟨614757600937818472597733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1639353602500849260260621 614757600937818472597733)
              ·
                refine ⟨115267050175840963612075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 614757600937818472597733 115267050175840963612075)
                ·
                  rfl

theorem cell19_378813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_378813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378813 prefixEnd_378813 := by exact prefixLift 378813
  have htrace : WordTrace (prefixWord ++ tailWord_378813) baseStart_378813 baseEnd_378813 := by
    simpa [prefixWord, tailWord_378813, baseEnd_378813] using wordTrace_append hprefix tailTrace_378813
  have hstable : (prefixWord ++ tailWord_378813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378813).length < 2 ^ (prefixWord ++ tailWord_378813).sum := by decide
  have hdescent : baseEnd_378813 < baseStart_378813 := by decide
  rcases family_descends (prefixWord ++ tailWord_378813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378887 : List Nat := [1, 1, 4, 3, 1, 4, 2, 3]
def baseStart_378887 : Nat := 118140960795 + 378887 * 2 ^ 59
def prefixEnd_378887 : Nat := 4983230072969 + 3 ^ 40 * 378887 * 2
def baseEnd_378887 : Nat := 115289567253430717967429

theorem tailTrace_378887 : CollatzResearch.WordTrace tailWord_378887 prefixEnd_378887 115289567253430717967429 := by
  unfold tailWord_378887
  simp only [CollatzResearch.WordTrace]
  refine ⟨13819144178364582592982915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9212762785576388395321943 13819144178364582592982915)
  ·
    refine ⟨20728716267546873889474373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13819144178364582592982915 20728716267546873889474373)
    ·
      refine ⟨3886634300165038854276445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20728716267546873889474373 3886634300165038854276445)
      ·
        refine ⟨1457487862561889570353667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3886634300165038854276445 1457487862561889570353667)
        ·
          refine ⟨2186231793842834355530501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457487862561889570353667 2186231793842834355530501)
          ·
            refine ⟨409918461345531441661969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2186231793842834355530501 409918461345531441661969)
            ·
              refine ⟨307438846009148581246477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409918461345531441661969 307438846009148581246477)
              ·
                refine ⟨115289567253430717967429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307438846009148581246477 115289567253430717967429)
                ·
                  rfl

theorem cell19_378887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 3].length) (baseStart_378887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378887 prefixEnd_378887 := by exact prefixLift 378887
  have htrace : WordTrace (prefixWord ++ tailWord_378887) baseStart_378887 baseEnd_378887 := by
    simpa [prefixWord, tailWord_378887, baseEnd_378887] using wordTrace_append hprefix tailTrace_378887
  have hstable : (prefixWord ++ tailWord_378887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378887).length < 2 ^ (prefixWord ++ tailWord_378887).sum := by decide
  have hdescent : baseEnd_378887 < baseStart_378887 := by decide
  rcases family_descends (prefixWord ++ tailWord_378887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378891 : List Nat := [1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_378891 : Nat := 118140960795 + 378891 * 2 ^ 59
def prefixEnd_378891 : Nat := 4983230072969 + 3 ^ 40 * 378891 * 2
def baseEnd_378891 : Nat := 115290784392759893878529

theorem tailTrace_378891 : CollatzResearch.WordTrace tailWord_378891 prefixEnd_378891 115290784392759893878529 := by
  unfold tailWord_378891
  simp only [CollatzResearch.WordTrace]
  refine ⟨13819290070350091276128527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9212860046900060850752351 13819290070350091276128527)
  ·
    refine ⟨20728935105525136914192791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13819290070350091276128527 20728935105525136914192791)
    ·
      refine ⟨31093402658287705371289187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20728935105525136914192791 31093402658287705371289187)
      ·
        refine ⟨46640103987431558056933781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31093402658287705371289187 46640103987431558056933781)
        ·
          refine ⟨2186254874410854283918771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46640103987431558056933781 2186254874410854283918771)
          ·
            refine ⟨3279382311616281425878157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186254874410854283918771 3279382311616281425878157)
            ·
              refine ⟨1229768366856105534704309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3279382311616281425878157 1229768366856105534704309)
              ·
                refine ⟨115290784392759893878529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1229768366856105534704309 115290784392759893878529)
                ·
                  rfl

theorem cell19_378891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_378891 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378891 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378891 prefixEnd_378891 := by exact prefixLift 378891
  have htrace : WordTrace (prefixWord ++ tailWord_378891) baseStart_378891 baseEnd_378891 := by
    simpa [prefixWord, tailWord_378891, baseEnd_378891] using wordTrace_append hprefix tailTrace_378891
  have hstable : (prefixWord ++ tailWord_378891).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378891).length < 2 ^ (prefixWord ++ tailWord_378891).sum := by decide
  have hdescent : baseEnd_378891 < baseStart_378891 := by decide
  rcases family_descends (prefixWord ++ tailWord_378891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378908 : List Nat := [2, 2, 3, 1, 3, 3, 5]
def baseStart_378908 : Nat := 118140960795 + 378908 * 2 ^ 59
def prefixEnd_378908 : Nat := 4983230072969 + 3 ^ 40 * 378908 * 2
def baseEnd_378908 : Nat := 38431985744969630500235

theorem tailTrace_378908 : CollatzResearch.WordTrace tailWord_378908 prefixEnd_378908 38431985744969630500235 := by
  unfold tailWord_378908
  simp only [CollatzResearch.WordTrace]
  refine ⟨6909955055644251589748689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9213273407525668786331585 6909955055644251589748689)
  ·
    refine ⟨5182466291733188692311517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6909955055644251589748689 5182466291733188692311517)
    ·
      refine ⟨1943424859399945759616819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5182466291733188692311517 1943424859399945759616819)
      ·
        refine ⟨2915137289099918639425229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943424859399945759616819 2915137289099918639425229)
        ·
          refine ⟨1093176483412469489784461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2915137289099918639425229 1093176483412469489784461)
          ·
            refine ⟨409941181279676058669173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1093176483412469489784461 409941181279676058669173)
            ·
              refine ⟨38431985744969630500235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 409941181279676058669173 38431985744969630500235)
              ·
                rfl

theorem cell19_378908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_378908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378908 prefixEnd_378908 := by exact prefixLift 378908
  have htrace : WordTrace (prefixWord ++ tailWord_378908) baseStart_378908 baseEnd_378908 := by
    simpa [prefixWord, tailWord_378908, baseEnd_378908] using wordTrace_append hprefix tailTrace_378908
  have hstable : (prefixWord ++ tailWord_378908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378908).length < 2 ^ (prefixWord ++ tailWord_378908).sum := by decide
  have hdescent : baseEnd_378908 < baseStart_378908 := by decide
  rcases family_descends (prefixWord ++ tailWord_378908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378929 : List Nat := [1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_378929 : Nat := 118140960795 + 378929 * 2 ^ 59
def prefixEnd_378929 : Nat := 4983230072969 + 3 ^ 40 * 378929 * 2
def baseEnd_378929 : Nat := 115302347216387065033981

theorem tailTrace_378929 : CollatzResearch.WordTrace tailWord_378929 prefixEnd_378929 115302347216387065033981 := by
  unfold tailWord_378929
  simp only [CollatzResearch.WordTrace]
  refine ⟨13820676044212423766011841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9213784029474949177341227 13820676044212423766011841)
  ·
    refine ⟨10365507033159317824508881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13820676044212423766011841 10365507033159317824508881)
    ·
      refine ⟨7774130274869488368381661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10365507033159317824508881 7774130274869488368381661)
      ·
        refine ⟨2915298853076058138143123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7774130274869488368381661 2915298853076058138143123)
        ·
          refine ⟨4372948279614087207214685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915298853076058138143123 4372948279614087207214685)
          ·
            refine ⟨1639855604855282702705507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4372948279614087207214685 1639855604855282702705507)
            ·
              refine ⟨2459783407282924054058261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639855604855282702705507 2459783407282924054058261)
              ·
                refine ⟨115302347216387065033981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2459783407282924054058261 115302347216387065033981)
                ·
                  rfl

theorem cell19_378929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_378929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_378929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_378929 prefixEnd_378929 := by exact prefixLift 378929
  have htrace : WordTrace (prefixWord ++ tailWord_378929) baseStart_378929 baseEnd_378929 := by
    simpa [prefixWord, tailWord_378929, baseEnd_378929] using wordTrace_append hprefix tailTrace_378929
  have hstable : (prefixWord ++ tailWord_378929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378929).length < 2 ^ (prefixWord ++ tailWord_378929).sum := by decide
  have hdescent : baseEnd_378929 < baseStart_378929 := by decide
  rcases family_descends (prefixWord ++ tailWord_378929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379022 : List Nat := [4, 1, 1, 3, 3, 1, 6]
def baseStart_379022 : Nat := 118140960795 + 379022 * 2 ^ 59
def prefixEnd_379022 : Nat := 4983230072969 + 3 ^ 40 * 379022 * 2
def baseEnd_379022 : Nat := 38443548568596801655687

theorem tailTrace_379022 : CollatzResearch.WordTrace tailWord_379022 prefixEnd_379022 38443548568596801655687 := by
  unfold tailWord_379022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728008504109437581143415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9216045355250333766098213 1728008504109437581143415)
  ·
    refine ⟨2592012756164156371715123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1728008504109437581143415 2592012756164156371715123)
    ·
      refine ⟨3888019134246234557572685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592012756164156371715123 3888019134246234557572685)
      ·
        refine ⟨1458007175342337959089757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3888019134246234557572685 1458007175342337959089757)
        ·
          refine ⟨546752690753376734658659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1458007175342337959089757 546752690753376734658659)
          ·
            refine ⟨820129036130065101987989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546752690753376734658659 820129036130065101987989)
            ·
              refine ⟨38443548568596801655687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 820129036130065101987989 38443548568596801655687)
              ·
                rfl

theorem cell19_379022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_379022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379022 prefixEnd_379022 := by exact prefixLift 379022
  have htrace : WordTrace (prefixWord ++ tailWord_379022) baseStart_379022 baseEnd_379022 := by
    simpa [prefixWord, tailWord_379022, baseEnd_379022] using wordTrace_append hprefix tailTrace_379022
  have hstable : (prefixWord ++ tailWord_379022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379022).length < 2 ^ (prefixWord ++ tailWord_379022).sum := by decide
  have hdescent : baseEnd_379022 < baseStart_379022 := by decide
  rcases family_descends (prefixWord ++ tailWord_379022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379054 : List Nat := [4, 1, 4, 2, 1, 2, 2, 3]
def baseStart_379054 : Nat := 118140960795 + 379054 * 2 ^ 59
def prefixEnd_379054 : Nat := 4983230072969 + 3 ^ 40 * 379054 * 2
def baseEnd_379054 : Nat := 115340382820423812255863

theorem tailTrace_379054 : CollatzResearch.WordTrace tailWord_379054 prefixEnd_379054 115340382820423812255863 := by
  unfold tailWord_379054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728154396094946264289027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9216823445839713409541477 1728154396094946264289027)
  ·
    refine ⟨2592231594142419396433541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1728154396094946264289027 2592231594142419396433541)
    ·
      refine ⟨486043423901703636831289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2592231594142419396433541 486043423901703636831289)
      ·
        refine ⟨364532567926277727623467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486043423901703636831289 364532567926277727623467)
        ·
          refine ⟨546798851889416591435201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364532567926277727623467 546798851889416591435201)
          ·
            refine ⟨410099138917062443576401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546798851889416591435201 410099138917062443576401)
            ·
              refine ⟨307574354187796832682301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410099138917062443576401 307574354187796832682301)
              ·
                refine ⟨115340382820423812255863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307574354187796832682301 115340382820423812255863)
                ·
                  rfl

theorem cell19_379054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_379054 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379054 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379054 prefixEnd_379054 := by exact prefixLift 379054
  have htrace : WordTrace (prefixWord ++ tailWord_379054) baseStart_379054 baseEnd_379054 := by
    simpa [prefixWord, tailWord_379054, baseEnd_379054] using wordTrace_append hprefix tailTrace_379054
  have hstable : (prefixWord ++ tailWord_379054).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379054).length < 2 ^ (prefixWord ++ tailWord_379054).sum := by decide
  have hdescent : baseEnd_379054 < baseStart_379054 := by decide
  rcases family_descends (prefixWord ++ tailWord_379054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379119 : List Nat := [1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_379119 : Nat := 118140960795 + 379119 * 2 ^ 59
def prefixEnd_379119 : Nat := 4983230072969 + 3 ^ 40 * 379119 * 2
def baseEnd_379119 : Nat := 115360161334522920811241

theorem tailTrace_379119 : CollatzResearch.WordTrace tailWord_379119 prefixEnd_379119 115360161334522920811241 := by
  unfold tailWord_379119
  simp only [CollatzResearch.WordTrace]
  refine ⟨13827605913524086215428411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9218403942349390810285607 13827605913524086215428411)
  ·
    refine ⟨20741408870286129323142617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13827605913524086215428411 20741408870286129323142617)
    ·
      refine ⟨15556056652714596992356963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20741408870286129323142617 15556056652714596992356963)
      ·
        refine ⟨23334084979071895488535445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15556056652714596992356963 23334084979071895488535445)
        ·
          refine ⟨1093785233393995101025099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23334084979071895488535445 1093785233393995101025099)
          ·
            refine ⟨1640677850090992651537649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093785233393995101025099 1640677850090992651537649)
            ·
              refine ⟨1230508387568244488653237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1640677850090992651537649 1230508387568244488653237)
              ·
                refine ⟨115360161334522920811241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1230508387568244488653237 115360161334522920811241)
                ·
                  rfl

theorem cell19_379119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_379119 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379119 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379119 prefixEnd_379119 := by exact prefixLift 379119
  have htrace : WordTrace (prefixWord ++ tailWord_379119) baseStart_379119 baseEnd_379119 := by
    simpa [prefixWord, tailWord_379119, baseEnd_379119] using wordTrace_append hprefix tailTrace_379119
  have hstable : (prefixWord ++ tailWord_379119).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379119).length < 2 ^ (prefixWord ++ tailWord_379119).sum := by decide
  have hdescent : baseEnd_379119 < baseStart_379119 := by decide
  rcases family_descends (prefixWord ++ tailWord_379119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379157 : List Nat := [1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_379157 : Nat := 118140960795 + 379157 * 2 ^ 59
def prefixEnd_379157 : Nat := 4983230072969 + 3 ^ 40 * 379157 * 2
def baseEnd_379157 : Nat := 115371724158150091966693

theorem tailTrace_379157 : CollatzResearch.WordTrace tailWord_379157 prefixEnd_379157 115371724158150091966693 := by
  unfold tailWord_379157
  simp only [CollatzResearch.WordTrace]
  refine ⟨13828991887386418705311725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9219327924924279136874483 13828991887386418705311725)
  ·
    refine ⟨5185871957769907014491897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13828991887386418705311725 5185871957769907014491897)
    ·
      refine ⟨3889403968327430260868923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5185871957769907014491897 3889403968327430260868923)
      ·
        refine ⟨5834105952491145391303385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889403968327430260868923 5834105952491145391303385)
        ·
          refine ⟨4375579464368359043477539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5834105952491145391303385 4375579464368359043477539)
          ·
            refine ⟨6563369196552538565216309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375579464368359043477539 6563369196552538565216309)
            ·
              refine ⟨615315862176800490489029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6563369196552538565216309 615315862176800490489029)
              ·
                refine ⟨115371724158150091966693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 615315862176800490489029 115371724158150091966693)
                ·
                  rfl

theorem cell19_379157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_379157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379157 prefixEnd_379157 := by exact prefixLift 379157
  have htrace : WordTrace (prefixWord ++ tailWord_379157) baseStart_379157 baseEnd_379157 := by
    simpa [prefixWord, tailWord_379157, baseEnd_379157] using wordTrace_append hprefix tailTrace_379157
  have hstable : (prefixWord ++ tailWord_379157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379157).length < 2 ^ (prefixWord ++ tailWord_379157).sum := by decide
  have hdescent : baseEnd_379157 < baseStart_379157 := by decide
  rcases family_descends (prefixWord ++ tailWord_379157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379271 : List Nat := [1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_379271 : Nat := 118140960795 + 379271 * 2 ^ 59
def prefixEnd_379271 : Nat := 4983230072969 + 3 ^ 40 * 379271 * 2
def baseEnd_379271 : Nat := 115406412629031605433049

theorem tailTrace_379271 : CollatzResearch.WordTrace tailWord_379271 prefixEnd_379271 115406412629031605433049 := by
  unfold tailWord_379271
  simp only [CollatzResearch.WordTrace]
  refine ⟨13833149808973416174961667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9222099872648944116641111 13833149808973416174961667)
  ·
    refine ⟨20749724713460124262442501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13833149808973416174961667 20749724713460124262442501)
    ·
      refine ⟨3890573383773773299207969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20749724713460124262442501 3890573383773773299207969)
      ·
        refine ⟨2917930037830329974405977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3890573383773773299207969 2917930037830329974405977)
        ·
          refine ⟨2188447528372747480804483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2917930037830329974405977 2188447528372747480804483)
          ·
            refine ⟨3282671292559121221206725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188447528372747480804483 3282671292559121221206725)
            ·
              refine ⟨615500867354835228976261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3282671292559121221206725 615500867354835228976261)
              ·
                refine ⟨115406412629031605433049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 615500867354835228976261 115406412629031605433049)
                ·
                  rfl

theorem cell19_379271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_379271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379271 prefixEnd_379271 := by exact prefixLift 379271
  have htrace : WordTrace (prefixWord ++ tailWord_379271) baseStart_379271 baseEnd_379271 := by
    simpa [prefixWord, tailWord_379271, baseEnd_379271] using wordTrace_append hprefix tailTrace_379271
  have hstable : (prefixWord ++ tailWord_379271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379271).length < 2 ^ (prefixWord ++ tailWord_379271).sum := by decide
  have hdescent : baseEnd_379271 < baseStart_379271 := by decide
  rcases family_descends (prefixWord ++ tailWord_379271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379290 : List Nat := [3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_379290 : Nat := 118140960795 + 379290 * 2 ^ 59
def prefixEnd_379290 : Nat := 4983230072969 + 3 ^ 40 * 379290 * 2
def baseEnd_379290 : Nat := 115412194040845191010775

theorem tailTrace_379290 : CollatzResearch.WordTrace tailWord_379290 prefixEnd_379290 115412194040845191010775 := by
  unfold tailWord_379290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3458460698976145604975831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9222561863936388279935549 3458460698976145604975831)
  ·
    refine ⟨5187691048464218407463747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3458460698976145604975831 5187691048464218407463747)
    ·
      refine ⟨7781536572696327611195621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5187691048464218407463747 7781536572696327611195621)
      ·
        refine ⟨1459038107380561427099179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7781536572696327611195621 1459038107380561427099179)
        ·
          refine ⟨2188557161070842140648769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459038107380561427099179 2188557161070842140648769)
          ·
            refine ⟨1641417870803131605486577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2188557161070842140648769 1641417870803131605486577)
            ·
              refine ⟨1231063403102348704114933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1641417870803131605486577 1231063403102348704114933)
              ·
                refine ⟨115412194040845191010775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1231063403102348704114933 115412194040845191010775)
                ·
                  rfl

theorem cell19_379290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_379290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379290 prefixEnd_379290 := by exact prefixLift 379290
  have htrace : WordTrace (prefixWord ++ tailWord_379290) baseStart_379290 baseEnd_379290 := by
    simpa [prefixWord, tailWord_379290, baseEnd_379290] using wordTrace_append hprefix tailTrace_379290
  have hstable : (prefixWord ++ tailWord_379290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379290).length < 2 ^ (prefixWord ++ tailWord_379290).sum := by decide
  have hdescent : baseEnd_379290 < baseStart_379290 := by decide
  rcases family_descends (prefixWord ++ tailWord_379290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379309 : List Nat := [1, 5, 2, 2, 9]
def baseStart_379309 : Nat := 118140960795 + 379309 * 2 ^ 59
def prefixEnd_379309 : Nat := 4983230072969 + 3 ^ 40 * 379309 * 2
def baseEnd_379309 : Nat := 4274739831579954688463

theorem tailTrace_379309 : CollatzResearch.WordTrace tailWord_379309 prefixEnd_379309 4274739831579954688463 := by
  unfold tailWord_379309
  simp only [CollatzResearch.WordTrace]
  refine ⟨13834535782835748664844981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9223023855223832443229987 13834535782835748664844981)
  ·
    refine ⟨1296987729640851437329217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13834535782835748664844981 1296987729640851437329217)
    ·
      refine ⟨972740797230638577996913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1296987729640851437329217 972740797230638577996913)
      ·
        refine ⟨729555597922978933497685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 972740797230638577996913 729555597922978933497685)
        ·
          refine ⟨4274739831579954688463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 729555597922978933497685 4274739831579954688463)
          ·
            rfl

theorem cell19_379309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 9].length) (baseStart_379309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379309 prefixEnd_379309 := by exact prefixLift 379309
  have htrace : WordTrace (prefixWord ++ tailWord_379309) baseStart_379309 baseEnd_379309 := by
    simpa [prefixWord, tailWord_379309, baseEnd_379309] using wordTrace_append hprefix tailTrace_379309
  have hstable : (prefixWord ++ tailWord_379309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379309).length < 2 ^ (prefixWord ++ tailWord_379309).sum := by decide
  have hdescent : baseEnd_379309 < baseStart_379309 := by decide
  rcases family_descends (prefixWord ++ tailWord_379309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379362 : List Nat := [3, 3, 3, 2, 1, 1, 6]
def baseStart_379362 : Nat := 118140960795 + 379362 * 2 ^ 59
def prefixEnd_379362 : Nat := 4983230072969 + 3 ^ 40 * 379362 * 2
def baseEnd_379362 : Nat := 38478034182923452470193

theorem tailTrace_379362 : CollatzResearch.WordTrace tailWord_379362 prefixEnd_379362 38478034182923452470193 := by
  unfold tailWord_379362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459117212910934679131085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9224312567762492477682893 3459117212910934679131085)
  ·
    refine ⟨1297168954841600504674157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3459117212910934679131085 1297168954841600504674157)
    ·
      refine ⟨486438358065600189252809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1297168954841600504674157 486438358065600189252809)
      ·
        refine ⟨364828768549200141939607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486438358065600189252809 364828768549200141939607)
        ·
          refine ⟨547243152823800212909411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364828768549200141939607 547243152823800212909411)
          ·
            refine ⟨820864729235700319364117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547243152823800212909411 820864729235700319364117)
            ·
              refine ⟨38478034182923452470193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 820864729235700319364117 38478034182923452470193)
              ·
                rfl

theorem cell19_379362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 6].length) (baseStart_379362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379362 prefixEnd_379362 := by exact prefixLift 379362
  have htrace : WordTrace (prefixWord ++ tailWord_379362) baseStart_379362 baseEnd_379362 := by
    simpa [prefixWord, tailWord_379362, baseEnd_379362] using wordTrace_append hprefix tailTrace_379362
  have hstable : (prefixWord ++ tailWord_379362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379362).length < 2 ^ (prefixWord ++ tailWord_379362).sum := by decide
  have hdescent : baseEnd_379362 < baseStart_379362 := by decide
  rcases family_descends (prefixWord ++ tailWord_379362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379398 : List Nat := [6, 2, 1, 1, 1, 2, 1, 5]
def baseStart_379398 : Nat := 118140960795 + 379398 * 2 ^ 59
def prefixEnd_379398 : Nat := 4983230072969 + 3 ^ 40 * 379398 * 2
def baseEnd_379398 : Nat := 115445056802732940610481

theorem tailTrace_379398 : CollatzResearch.WordTrace tailWord_379398 prefixEnd_379398 115445056802732940610481 := by
  unfold tailWord_379398
  simp only [CollatzResearch.WordTrace]
  refine ⟨432430683734791152026089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9225187919675544576556565 432430683734791152026089)
  ·
    refine ⟨324323012801093364019567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 432430683734791152026089 324323012801093364019567)
    ·
      refine ⟨486484519201640046029351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324323012801093364019567 486484519201640046029351)
      ·
        refine ⟨729726778802460069044027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486484519201640046029351 729726778802460069044027)
        ·
          refine ⟨1094590168203690103566041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729726778802460069044027 1094590168203690103566041)
          ·
            refine ⟨820942626152767577674531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1094590168203690103566041 820942626152767577674531)
            ·
              refine ⟨1231413939229151366511797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820942626152767577674531 1231413939229151366511797)
              ·
                refine ⟨115445056802732940610481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1231413939229151366511797 115445056802732940610481)
                ·
                  rfl

theorem cell19_379398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_379398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379398 prefixEnd_379398 := by exact prefixLift 379398
  have htrace : WordTrace (prefixWord ++ tailWord_379398) baseStart_379398 baseEnd_379398 := by
    simpa [prefixWord, tailWord_379398, baseEnd_379398] using wordTrace_append hprefix tailTrace_379398
  have hstable : (prefixWord ++ tailWord_379398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379398).length < 2 ^ (prefixWord ++ tailWord_379398).sum := by decide
  have hdescent : baseEnd_379398 < baseStart_379398 := by decide
  rcases family_descends (prefixWord ++ tailWord_379398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379404 : List Nat := [2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_379404 : Nat := 118140960795 + 379404 * 2 ^ 59
def prefixEnd_379404 : Nat := 4983230072969 + 3 ^ 40 * 379404 * 2
def baseEnd_379404 : Nat := 115446882511726704477131

theorem tailTrace_379404 : CollatzResearch.WordTrace tailWord_379404 prefixEnd_379404 115446882511726704477131 := by
  unfold tailWord_379404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919000358745789944776633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9225333811661053259702177 6919000358745789944776633)
  ·
    refine ⟨5189250269059342458582475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6919000358745789944776633 5189250269059342458582475)
    ·
      refine ⟨7783875403589013687873713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5189250269059342458582475 7783875403589013687873713)
      ·
        refine ⟨5837906552691760265905285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7783875403589013687873713 5837906552691760265905285)
        ·
          refine ⟨1094607478629705049857241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5837906552691760265905285 1094607478629705049857241)
          ·
            refine ⟨820955608972278787392931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1094607478629705049857241 820955608972278787392931)
            ·
              refine ⟨1231433413458418181089397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820955608972278787392931 1231433413458418181089397)
              ·
                refine ⟨115446882511726704477131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1231433413458418181089397 115446882511726704477131)
                ·
                  rfl

theorem cell19_379404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_379404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379404 prefixEnd_379404 := by exact prefixLift 379404
  have htrace : WordTrace (prefixWord ++ tailWord_379404) baseStart_379404 baseEnd_379404 := by
    simpa [prefixWord, tailWord_379404, baseEnd_379404] using wordTrace_append hprefix tailTrace_379404
  have hstable : (prefixWord ++ tailWord_379404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379404).length < 2 ^ (prefixWord ++ tailWord_379404).sum := by decide
  have hdescent : baseEnd_379404 < baseStart_379404 := by decide
  rcases family_descends (prefixWord ++ tailWord_379404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379569 : List Nat := [1, 2, 2, 6, 2, 1, 2, 3]
def baseStart_379569 : Nat := 118140960795 + 379569 * 2 ^ 59
def prefixEnd_379569 : Nat := 4983230072969 + 3 ^ 40 * 379569 * 2
def baseEnd_379569 : Nat := 115497089509055210810015

theorem tailTrace_379569 : CollatzResearch.WordTrace tailWord_379569 prefixEnd_379569 115497089509055210810015 := by
  unfold tailWord_379569
  simp only [CollatzResearch.WordTrace]
  refine ⟨13844018761893813069309761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9229345841262542046206507 13844018761893813069309761)
  ·
    refine ⟨10383014071420359801982321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13844018761893813069309761 10383014071420359801982321)
    ·
      refine ⟨7787260553565269851486741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10383014071420359801982321 7787260553565269851486741)
      ·
        refine ⟨365027838448372024288441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7787260553565269851486741 365027838448372024288441)
        ·
          refine ⟨273770878836279018216331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365027838448372024288441 273770878836279018216331)
          ·
            refine ⟨410656318254418527324497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273770878836279018216331 410656318254418527324497)
            ·
              refine ⟨307992238690813895493373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410656318254418527324497 307992238690813895493373)
              ·
                refine ⟨115497089509055210810015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307992238690813895493373 115497089509055210810015)
                ·
                  rfl

theorem cell19_379569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 3].length) (baseStart_379569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379569 prefixEnd_379569 := by exact prefixLift 379569
  have htrace : WordTrace (prefixWord ++ tailWord_379569) baseStart_379569 baseEnd_379569 := by
    simpa [prefixWord, tailWord_379569, baseEnd_379569] using wordTrace_append hprefix tailTrace_379569
  have hstable : (prefixWord ++ tailWord_379569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379569).length < 2 ^ (prefixWord ++ tailWord_379569).sum := by decide
  have hdescent : baseEnd_379569 < baseStart_379569 := by decide
  rcases family_descends (prefixWord ++ tailWord_379569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379573 : List Nat := [1, 3, 3, 3, 1, 1, 4, 3]
def baseStart_379573 : Nat := 118140960795 + 379573 * 2 ^ 59
def prefixEnd_379573 : Nat := 4983230072969 + 3 ^ 40 * 379573 * 2
def baseEnd_379573 : Nat := 115498306648384386721115

theorem tailTrace_379573 : CollatzResearch.WordTrace tailWord_379573 prefixEnd_379573 115498306648384386721115 := by
  unfold tailWord_379573
  simp only [CollatzResearch.WordTrace]
  refine ⟨13844164653879321752455373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9229443102586214501636915 13844164653879321752455373)
  ·
    refine ⟨5191561745204745657170765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13844164653879321752455373 5191561745204745657170765)
    ·
      refine ⟨1946835654451779621439037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5191561745204745657170765 1946835654451779621439037)
      ·
        refine ⟨730063370419417358039639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1946835654451779621439037 730063370419417358039639)
        ·
          refine ⟨1095095055629126037059459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730063370419417358039639 1095095055629126037059459)
          ·
            refine ⟨1642642583443689055589189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095095055629126037059459 1642642583443689055589189)
            ·
              refine ⟨307995484395691697922973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1642642583443689055589189 307995484395691697922973)
              ·
                refine ⟨115498306648384386721115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307995484395691697922973 115498306648384386721115)
                ·
                  rfl

theorem cell19_379573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 3].length) (baseStart_379573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379573 prefixEnd_379573 := by exact prefixLift 379573
  have htrace : WordTrace (prefixWord ++ tailWord_379573) baseStart_379573 baseEnd_379573 := by
    simpa [prefixWord, tailWord_379573, baseEnd_379573] using wordTrace_append hprefix tailTrace_379573
  have hstable : (prefixWord ++ tailWord_379573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379573).length < 2 ^ (prefixWord ++ tailWord_379573).sum := by decide
  have hdescent : baseEnd_379573 < baseStart_379573 := by decide
  rcases family_descends (prefixWord ++ tailWord_379573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379575 : List Nat := [1, 1, 3, 1, 6, 1, 1, 5]
def baseStart_379575 : Nat := 118140960795 + 379575 * 2 ^ 59
def prefixEnd_379575 : Nat := 4983230072969 + 3 ^ 40 * 379575 * 2
def baseEnd_379575 : Nat := 115498915218048974676665

theorem tailTrace_379575 : CollatzResearch.WordTrace tailWord_379575 prefixEnd_379575 115498915218048974676665 := by
  unfold tailWord_379575
  simp only [CollatzResearch.WordTrace]
  refine ⟨13844237599872076094028179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9229491733248050729352119 13844237599872076094028179)
  ·
    refine ⟨20766356399808114141042269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13844237599872076094028179 20766356399808114141042269)
    ·
      refine ⟨7787383649928042802890851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20766356399808114141042269 7787383649928042802890851)
      ·
        refine ⟨11681075474892064204336277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7787383649928042802890851 11681075474892064204336277)
        ·
          refine ⟨547550412885565509578263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11681075474892064204336277 547550412885565509578263)
          ·
            refine ⟨821325619328348264367395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547550412885565509578263 821325619328348264367395)
            ·
              refine ⟨1231988428992522396551093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821325619328348264367395 1231988428992522396551093)
              ·
                refine ⟨115498915218048974676665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1231988428992522396551093 115498915218048974676665)
                ·
                  rfl

theorem cell19_379575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_379575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379575 prefixEnd_379575 := by exact prefixLift 379575
  have htrace : WordTrace (prefixWord ++ tailWord_379575) baseStart_379575 baseEnd_379575 := by
    simpa [prefixWord, tailWord_379575, baseEnd_379575] using wordTrace_append hprefix tailTrace_379575
  have hstable : (prefixWord ++ tailWord_379575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379575).length < 2 ^ (prefixWord ++ tailWord_379575).sum := by decide
  have hdescent : baseEnd_379575 < baseStart_379575 := by decide
  rcases family_descends (prefixWord ++ tailWord_379575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379594 : List Nat := [3, 1, 2, 1, 4, 3, 5]
def baseStart_379594 : Nat := 118140960795 + 379594 * 2 ^ 59
def prefixEnd_379594 : Nat := 4983230072969 + 3 ^ 40 * 379594 * 2
def baseEnd_379594 : Nat := 38501565543287520084797

theorem tailTrace_379594 : CollatzResearch.WordTrace tailWord_379594 prefixEnd_379594 38501565543287520084797 := by
  unfold tailWord_379594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461232646700810584742459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9229953724535494892646557 3461232646700810584742459)
  ·
    refine ⟨5191848970051215877113689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3461232646700810584742459 5191848970051215877113689)
    ·
      refine ⟨3893886727538411907835267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5191848970051215877113689 3893886727538411907835267)
      ·
        refine ⟨5840830091307617861752901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893886727538411907835267 5840830091307617861752901)
        ·
          refine ⟨1095155642120178349078669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5840830091307617861752901 1095155642120178349078669)
          ·
            refine ⟨410683365795066880904501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1095155642120178349078669 410683365795066880904501)
            ·
              refine ⟨38501565543287520084797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 410683365795066880904501 38501565543287520084797)
              ·
                rfl

theorem cell19_379594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_379594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379594 prefixEnd_379594 := by exact prefixLift 379594
  have htrace : WordTrace (prefixWord ++ tailWord_379594) baseStart_379594 baseEnd_379594 := by
    simpa [prefixWord, tailWord_379594, baseEnd_379594] using wordTrace_append hprefix tailTrace_379594
  have hstable : (prefixWord ++ tailWord_379594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379594).length < 2 ^ (prefixWord ++ tailWord_379594).sum := by decide
  have hdescent : baseEnd_379594 < baseStart_379594 := by decide
  rcases family_descends (prefixWord ++ tailWord_379594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379615 : List Nat := [1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_379615 : Nat := 118140960795 + 379615 * 2 ^ 59
def prefixEnd_379615 : Nat := 4983230072969 + 3 ^ 40 * 379615 * 2
def baseEnd_379615 : Nat := 115511086611340733787667

theorem tailTrace_379615 : CollatzResearch.WordTrace tailWord_379615 prefixEnd_379615 115511086611340733787667 := by
  unfold tailWord_379615
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845696519727162925484299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9230464346484775283656199 13845696519727162925484299)
  ·
    refine ⟨20768544779590744388226449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13845696519727162925484299 20768544779590744388226449)
    ·
      refine ⟨15576408584693058291169837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20768544779590744388226449 15576408584693058291169837)
      ·
        refine ⟨5841153219259896859188689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15576408584693058291169837 5841153219259896859188689)
        ·
          refine ⟨4380864914444922644391517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5841153219259896859188689 4380864914444922644391517)
          ·
            refine ⟨1642824342916845991646819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4380864914444922644391517 1642824342916845991646819)
            ·
              refine ⟨2464236514375268987470229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642824342916845991646819 2464236514375268987470229)
              ·
                refine ⟨115511086611340733787667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2464236514375268987470229 115511086611340733787667)
                ·
                  rfl

theorem cell19_379615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_379615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379615 prefixEnd_379615 := by exact prefixLift 379615
  have htrace : WordTrace (prefixWord ++ tailWord_379615) baseStart_379615 baseEnd_379615 := by
    simpa [prefixWord, tailWord_379615, baseEnd_379615] using wordTrace_append hprefix tailTrace_379615
  have hstable : (prefixWord ++ tailWord_379615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379615).length < 2 ^ (prefixWord ++ tailWord_379615).sum := by decide
  have hdescent : baseEnd_379615 < baseStart_379615 := by decide
  rcases family_descends (prefixWord ++ tailWord_379615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379666 : List Nat := [3, 2, 4, 1, 2, 2, 1, 4]
def baseStart_379666 : Nat := 118140960795 + 379666 * 2 ^ 59
def prefixEnd_379666 : Nat := 4983230072969 + 3 ^ 40 * 379666 * 2
def baseEnd_379666 : Nat := 115526605137787726654195

theorem tailTrace_379666 : CollatzResearch.WordTrace tailWord_379666 prefixEnd_379666 115526605137787726654195 := by
  unfold tailWord_379666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461889160635599658897713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9231704428361599090393901 3461889160635599658897713)
  ·
    refine ⟨2596416870476699744173285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3461889160635599658897713 2596416870476699744173285)
    ·
      refine ⟨486828163214381202032491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2596416870476699744173285 486828163214381202032491)
      ·
        refine ⟨730242244821571803048737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486828163214381202032491 730242244821571803048737)
        ·
          refine ⟨547681683616178852286553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730242244821571803048737 547681683616178852286553)
          ·
            refine ⟨410761262712134139214915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547681683616178852286553 410761262712134139214915)
            ·
              refine ⟨616141894068201208822373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410761262712134139214915 616141894068201208822373)
              ·
                refine ⟨115526605137787726654195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 616141894068201208822373 115526605137787726654195)
                ·
                  rfl

theorem cell19_379666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_379666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379666 prefixEnd_379666 := by exact prefixLift 379666
  have htrace : WordTrace (prefixWord ++ tailWord_379666) baseStart_379666 baseEnd_379666 := by
    simpa [prefixWord, tailWord_379666, baseEnd_379666] using wordTrace_append hprefix tailTrace_379666
  have hstable : (prefixWord ++ tailWord_379666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379666).length < 2 ^ (prefixWord ++ tailWord_379666).sum := by decide
  have hdescent : baseEnd_379666 < baseStart_379666 := by decide
  rcases family_descends (prefixWord ++ tailWord_379666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379765 : List Nat := [1, 3, 4, 1, 1, 4, 5]
def baseStart_379765 : Nat := 118140960795 + 379765 * 2 ^ 59
def prefixEnd_379765 : Nat := 4983230072969 + 3 ^ 40 * 379765 * 2
def baseEnd_379765 : Nat := 38518909778728276817975

theorem tailTrace_379765 : CollatzResearch.WordTrace tailWord_379765 prefixEnd_379765 38518909778728276817975 := by
  unfold tailWord_379765
  simp only [CollatzResearch.WordTrace]
  refine ⟨13851167469183738543444749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9234111646122492362296499 13851167469183738543444749)
  ·
    refine ⟨5194187800943901953791781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13851167469183738543444749 5194187800943901953791781)
    ·
      refine ⟨973910212676981616335959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5194187800943901953791781 973910212676981616335959)
      ·
        refine ⟨1460865319015472424503939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973910212676981616335959 1460865319015472424503939)
        ·
          refine ⟨2191297978523208636755909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460865319015472424503939 2191297978523208636755909)
          ·
            refine ⟨410868370973101619391733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2191297978523208636755909 410868370973101619391733)
            ·
              refine ⟨38518909778728276817975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 410868370973101619391733 38518909778728276817975)
              ·
                rfl

theorem cell19_379765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_379765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379765 prefixEnd_379765 := by exact prefixLift 379765
  have htrace : WordTrace (prefixWord ++ tailWord_379765) baseStart_379765 baseEnd_379765 := by
    simpa [prefixWord, tailWord_379765, baseEnd_379765] using wordTrace_append hprefix tailTrace_379765
  have hstable : (prefixWord ++ tailWord_379765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379765).length < 2 ^ (prefixWord ++ tailWord_379765).sum := by decide
  have hdescent : baseEnd_379765 < baseStart_379765 := by decide
  rcases family_descends (prefixWord ++ tailWord_379765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379784 : List Nat := [2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_379784 : Nat := 118140960795 + 379784 * 2 ^ 59
def prefixEnd_379784 : Nat := 4983230072969 + 3 ^ 40 * 379784 * 2
def baseEnd_379784 : Nat := 115562510747998416031651

theorem tailTrace_379784 : CollatzResearch.WordTrace tailWord_379784 prefixEnd_379784 115562510747998416031651 := by
  unfold tailWord_379784
  simp only [CollatzResearch.WordTrace]
  refine ⟨6925930228057452394193203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9234573637409936525590937 6925930228057452394193203)
  ·
    refine ⟨10388895342086178591289805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6925930228057452394193203 10388895342086178591289805)
    ·
      refine ⟨3895835753282316971733677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10388895342086178591289805 3895835753282316971733677)
      ·
        refine ⟨1460938407480868864400129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3895835753282316971733677 1460938407480868864400129)
        ·
          refine ⟨1095703805610651648300097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1460938407480868864400129 1095703805610651648300097)
          ·
            refine ⟨821777854207988736225073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095703805610651648300097 821777854207988736225073)
            ·
              refine ⟨616333390655991552168805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821777854207988736225073 616333390655991552168805)
              ·
                refine ⟨115562510747998416031651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 616333390655991552168805 115562510747998416031651)
                ·
                  rfl

theorem cell19_379784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_379784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379784 prefixEnd_379784 := by exact prefixLift 379784
  have htrace : WordTrace (prefixWord ++ tailWord_379784) baseStart_379784 baseEnd_379784 := by
    simpa [prefixWord, tailWord_379784, baseEnd_379784] using wordTrace_append hprefix tailTrace_379784
  have hstable : (prefixWord ++ tailWord_379784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379784).length < 2 ^ (prefixWord ++ tailWord_379784).sum := by decide
  have hdescent : baseEnd_379784 < baseStart_379784 := by decide
  rcases family_descends (prefixWord ++ tailWord_379784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379805 : List Nat := [1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_379805 : Nat := 118140960795 + 379805 * 2 ^ 59
def prefixEnd_379805 : Nat := 4983230072969 + 3 ^ 40 * 379805 * 2
def baseEnd_379805 : Nat := 115568900729476589564927

theorem tailTrace_379805 : CollatzResearch.WordTrace tailWord_379805 prefixEnd_379805 115568900729476589564927 := by
  unfold tailWord_379805
  simp only [CollatzResearch.WordTrace]
  refine ⟨13852626389038825374900869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9235084259359216916600579 13852626389038825374900869)
  ·
    refine ⟨2597367447944779757793913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13852626389038825374900869 2597367447944779757793913)
    ·
      refine ⟨1948025585958584818345435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2597367447944779757793913 1948025585958584818345435)
      ·
        refine ⟨2922038378937877227518153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948025585958584818345435 2922038378937877227518153)
        ·
          refine ⟨2191528784203407920638615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922038378937877227518153 2191528784203407920638615)
          ·
            refine ⟨3287293176305111880957923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191528784203407920638615 3287293176305111880957923)
            ·
              refine ⟨4930939764457667821436885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287293176305111880957923 4930939764457667821436885)
              ·
                refine ⟨115568900729476589564927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4930939764457667821436885 115568900729476589564927)
                ·
                  rfl

theorem cell19_379805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_379805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379805 prefixEnd_379805 := by exact prefixLift 379805
  have htrace : WordTrace (prefixWord ++ tailWord_379805) baseStart_379805 baseEnd_379805 := by
    simpa [prefixWord, tailWord_379805, baseEnd_379805] using wordTrace_append hprefix tailTrace_379805
  have hstable : (prefixWord ++ tailWord_379805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379805).length < 2 ^ (prefixWord ++ tailWord_379805).sum := by decide
  have hdescent : baseEnd_379805 < baseStart_379805 := by decide
  rcases family_descends (prefixWord ++ tailWord_379805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379822 : List Nat := [4, 1, 5, 9]
def baseStart_379822 : Nat := 118140960795 + 379822 * 2 ^ 59
def prefixEnd_379822 : Nat := 4983230072969 + 3 ^ 40 * 379822 * 2
def baseEnd_379822 : Nat := 1426840414464513422063

theorem tailTrace_379822 : CollatzResearch.WordTrace tailWord_379822 prefixEnd_379822 1426840414464513422063 := by
  unfold tailWord_379822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731655803747154659783715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9235497619984824852179813 1731655803747154659783715)
  ·
    refine ⟨2597483705620731989675573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1731655803747154659783715 2597483705620731989675573)
    ·
      refine ⟨243514097401943624032085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2597483705620731989675573 243514097401943624032085)
      ·
        refine ⟨1426840414464513422063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 243514097401943624032085 1426840414464513422063)
        ·
          rfl

theorem cell19_379822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 9].length) (baseStart_379822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379822 prefixEnd_379822 := by exact prefixLift 379822
  have htrace : WordTrace (prefixWord ++ tailWord_379822) baseStart_379822 baseEnd_379822 := by
    simpa [prefixWord, tailWord_379822, baseEnd_379822] using wordTrace_append hprefix tailTrace_379822
  have hstable : (prefixWord ++ tailWord_379822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379822).length < 2 ^ (prefixWord ++ tailWord_379822).sum := by decide
  have hdescent : baseEnd_379822 < baseStart_379822 := by decide
  rcases family_descends (prefixWord ++ tailWord_379822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379858 : List Nat := [3, 2, 2, 3, 1, 2, 3, 3]
def baseStart_379858 : Nat := 118140960795 + 379858 * 2 ^ 59
def prefixEnd_379858 : Nat := 4983230072969 + 3 ^ 40 * 379858 * 2
def baseEnd_379858 : Nat := 115585027825588170387005

theorem tailTrace_379858 : CollatzResearch.WordTrace tailWord_379858 prefixEnd_379858 115585027825588170387005 := by
  unfold tailWord_379858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3463639864461703856645057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9236372971897876951053485 3463639864461703856645057)
  ·
    refine ⟨2597729898346277892483793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3463639864461703856645057 2597729898346277892483793)
    ·
      refine ⟨1948297423759708419362845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2597729898346277892483793 1948297423759708419362845)
      ·
        refine ⟨730611533909890657261067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1948297423759708419362845 730611533909890657261067)
        ·
          refine ⟨1095917300864835985891601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730611533909890657261067 1095917300864835985891601)
          ·
            refine ⟨821937975648626989418701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095917300864835985891601 821937975648626989418701)
            ·
              refine ⟨308226740868235121032013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 821937975648626989418701 308226740868235121032013)
              ·
                refine ⟨115585027825588170387005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308226740868235121032013 115585027825588170387005)
                ·
                  rfl

theorem cell19_379858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_379858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379858 prefixEnd_379858 := by exact prefixLift 379858
  have htrace : WordTrace (prefixWord ++ tailWord_379858) baseStart_379858 baseEnd_379858 := by
    simpa [prefixWord, tailWord_379858, baseEnd_379858] using wordTrace_append hprefix tailTrace_379858
  have hstable : (prefixWord ++ tailWord_379858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379858).length < 2 ^ (prefixWord ++ tailWord_379858).sum := by decide
  have hdescent : baseEnd_379858 < baseStart_379858 := by decide
  rcases family_descends (prefixWord ++ tailWord_379858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379938 : List Nat := [3, 3, 1, 1, 1, 3, 7]
def baseStart_379938 : Nat := 118140960795 + 379938 * 2 ^ 59
def prefixEnd_379938 : Nat := 4983230072969 + 3 ^ 40 * 379938 * 2
def baseEnd_379938 : Nat := 38536456870723896203003

theorem tailTrace_379938 : CollatzResearch.WordTrace tailWord_379938 prefixEnd_379938 38536456870723896203003 := by
  unfold tailWord_379938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464369324389247272373117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9238318198371326059661645 3464369324389247272373117)
  ·
    refine ⟨1299138496645967727139919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3464369324389247272373117 1299138496645967727139919)
    ·
      refine ⟨1948707744968951590709879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299138496645967727139919 1948707744968951590709879)
      ·
        refine ⟨2923061617453427386064819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948707744968951590709879 2923061617453427386064819)
        ·
          refine ⟨4384592426180141079097229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923061617453427386064819 4384592426180141079097229)
          ·
            refine ⟨1644222159817552904661461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4384592426180141079097229 1644222159817552904661461)
            ·
              refine ⟨38536456870723896203003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1644222159817552904661461 38536456870723896203003)
              ·
                rfl

theorem cell19_379938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_379938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_379938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_379938 prefixEnd_379938 := by exact prefixLift 379938
  have htrace : WordTrace (prefixWord ++ tailWord_379938) baseStart_379938 baseEnd_379938 := by
    simpa [prefixWord, tailWord_379938, baseEnd_379938] using wordTrace_append hprefix tailTrace_379938
  have hstable : (prefixWord ++ tailWord_379938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379938).length < 2 ^ (prefixWord ++ tailWord_379938).sum := by decide
  have hdescent : baseEnd_379938 < baseStart_379938 := by decide
  rcases family_descends (prefixWord ++ tailWord_379938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380008 : List Nat := [2, 1, 4, 4, 2, 1, 1, 4]
def baseStart_380008 : Nat := 118140960795 + 380008 * 2 ^ 59
def prefixEnd_380008 : Nat := 4983230072969 + 3 ^ 40 * 380008 * 2
def baseEnd_380008 : Nat := 115630670550432267053263

theorem tailTrace_380008 : CollatzResearch.WordTrace tailWord_380008 prefixEnd_380008 115630670550432267053263 := by
  unfold tailWord_380008
  simp only [CollatzResearch.WordTrace]
  refine ⟨6930015203651695522270339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9240020271535594029693785 6930015203651695522270339)
  ·
    refine ⟨10395022805477543283405509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6930015203651695522270339 10395022805477543283405509)
    ·
      refine ⟨1949066776027039365638533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10395022805477543283405509 1949066776027039365638533)
      ·
        refine ⟨365450020505069881057225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1949066776027039365638533 365450020505069881057225)
        ·
          refine ⟨274087515378802410792919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365450020505069881057225 274087515378802410792919)
          ·
            refine ⟨411131273068203616189379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274087515378802410792919 411131273068203616189379)
            ·
              refine ⟨616696909602305424284069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411131273068203616189379 616696909602305424284069)
              ·
                refine ⟨115630670550432267053263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 616696909602305424284069 115630670550432267053263)
                ·
                  rfl

theorem cell19_380008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_380008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380008 prefixEnd_380008 := by exact prefixLift 380008
  have htrace : WordTrace (prefixWord ++ tailWord_380008) baseStart_380008 baseEnd_380008 := by
    simpa [prefixWord, tailWord_380008, baseEnd_380008] using wordTrace_append hprefix tailTrace_380008
  have hstable : (prefixWord ++ tailWord_380008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380008).length < 2 ^ (prefixWord ++ tailWord_380008).sum := by decide
  have hdescent : baseEnd_380008 < baseStart_380008 := by decide
  rcases family_descends (prefixWord ++ tailWord_380008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380128 : List Nat := [2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_380128 : Nat := 118140960795 + 380128 * 2 ^ 59
def prefixEnd_380128 : Nat := 4983230072969 + 3 ^ 40 * 380128 * 2
def baseEnd_380128 : Nat := 115667184730307544386269

theorem tailTrace_380128 : CollatzResearch.WordTrace tailWord_380128 prefixEnd_380128 115667184730307544386269 := by
  unfold tailWord_380128
  simp only [CollatzResearch.WordTrace]
  refine ⟨6932203583434325769454519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9242938111245767692606025 6932203583434325769454519)
  ·
    refine ⟨10398305375151488654181779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6932203583434325769454519 10398305375151488654181779)
    ·
      refine ⟨15597458062727232981272669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10398305375151488654181779 15597458062727232981272669)
      ·
        refine ⟨5849046773522712367977251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15597458062727232981272669 5849046773522712367977251)
        ·
          refine ⟨8773570160284068551965877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849046773522712367977251 8773570160284068551965877)
          ·
            refine ⟨822522202526631426746801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8773570160284068551965877 822522202526631426746801)
            ·
              refine ⟨616891651894973570060101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822522202526631426746801 616891651894973570060101)
              ·
                refine ⟨115667184730307544386269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 616891651894973570060101 115667184730307544386269)
                ·
                  rfl

theorem cell19_380128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_380128 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380128 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380128 prefixEnd_380128 := by exact prefixLift 380128
  have htrace : WordTrace (prefixWord ++ tailWord_380128) baseStart_380128 baseEnd_380128 := by
    simpa [prefixWord, tailWord_380128, baseEnd_380128] using wordTrace_append hprefix tailTrace_380128
  have hstable : (prefixWord ++ tailWord_380128).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380128).length < 2 ^ (prefixWord ++ tailWord_380128).sum := by decide
  have hdescent : baseEnd_380128 < baseStart_380128 := by decide
  rcases family_descends (prefixWord ++ tailWord_380128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380168 : List Nat := [2, 1, 3, 2, 11]
def baseStart_380168 : Nat := 118140960795 + 380168 * 2 ^ 59
def prefixEnd_380168 : Nat := 4983230072969 + 3 ^ 40 * 380168 * 2
def baseEnd_380168 : Nat := 4284420597170344573973

theorem tailTrace_380168 : CollatzResearch.WordTrace tailWord_380168 prefixEnd_380168 4284420597170344573973 := by
  unfold tailWord_380168
  simp only [CollatzResearch.WordTrace]
  refine ⟨6932933043361869185182579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9243910724482492246910105 6932933043361869185182579)
  ·
    refine ⟨10399399565042803777773869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6932933043361869185182579 10399399565042803777773869)
    ·
      refine ⟨3899774836891051416665201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10399399565042803777773869 3899774836891051416665201)
      ·
        refine ⟨2924831127668288562498901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3899774836891051416665201 2924831127668288562498901)
        ·
          refine ⟨4284420597170344573973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2924831127668288562498901 4284420597170344573973)
          ·
            rfl

theorem cell19_380168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 11].length) (baseStart_380168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380168 prefixEnd_380168 := by exact prefixLift 380168
  have htrace : WordTrace (prefixWord ++ tailWord_380168) baseStart_380168 baseEnd_380168 := by
    simpa [prefixWord, tailWord_380168, baseEnd_380168] using wordTrace_append hprefix tailTrace_380168
  have hstable : (prefixWord ++ tailWord_380168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380168).length < 2 ^ (prefixWord ++ tailWord_380168).sum := by decide
  have hdescent : baseEnd_380168 < baseStart_380168 := by decide
  rcases family_descends (prefixWord ++ tailWord_380168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380221 : List Nat := [1, 4, 1, 5, 1, 1, 6]
def baseStart_380221 : Nat := 118140960795 + 380221 * 2 ^ 59
def prefixEnd_380221 : Nat := 4983230072969 + 3 ^ 40 * 380221 * 2
def baseEnd_380221 : Nat := 38565161073236961439783

theorem tailTrace_380221 : CollatzResearch.WordTrace tailWord_380221 prefixEnd_380221 38565161073236961439783 := by
  unfold tailWord_380221
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867799155531728422044517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9245199437021152281363011 13867799155531728422044517)
  ·
    refine ⟨2600212341662199079133347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13867799155531728422044517 2600212341662199079133347)
    ·
      refine ⟨3900318512493298618700021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2600212341662199079133347 3900318512493298618700021)
      ·
        refine ⟨365654860546246745503127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3900318512493298618700021 365654860546246745503127)
        ·
          refine ⟨548482290819370118254691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365654860546246745503127 548482290819370118254691)
          ·
            refine ⟨822723436229055177382037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548482290819370118254691 822723436229055177382037)
            ·
              refine ⟨38565161073236961439783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 822723436229055177382037 38565161073236961439783)
              ·
                rfl

theorem cell19_380221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 6].length) (baseStart_380221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380221 prefixEnd_380221 := by exact prefixLift 380221
  have htrace : WordTrace (prefixWord ++ tailWord_380221) baseStart_380221 baseEnd_380221 := by
    simpa [prefixWord, tailWord_380221, baseEnd_380221] using wordTrace_append hprefix tailTrace_380221
  have hstable : (prefixWord ++ tailWord_380221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380221).length < 2 ^ (prefixWord ++ tailWord_380221).sum := by decide
  have hdescent : baseEnd_380221 < baseStart_380221 := by decide
  rcases family_descends (prefixWord ++ tailWord_380221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380253 : List Nat := [1, 4, 5, 1, 1, 2, 2, 3]
def baseStart_380253 : Nat := 118140960795 + 380253 * 2 ^ 59
def prefixEnd_380253 : Nat := 4983230072969 + 3 ^ 40 * 380253 * 2
def baseEnd_380253 : Nat := 115705220334344291608151

theorem tailTrace_380253 : CollatzResearch.WordTrace tailWord_380253 prefixEnd_380253 115705220334344291608151 := by
  unfold tailWord_380253
  simp only [CollatzResearch.WordTrace]
  refine ⟨13868966291415797887209413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9245977527610531924806275 13868966291415797887209413)
  ·
    refine ⟨2600431179640462103851765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13868966291415797887209413 2600431179640462103851765)
    ·
      refine ⟨243790423091293322236103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2600431179640462103851765 243790423091293322236103)
      ·
        refine ⟨365685634636939983354155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243790423091293322236103 365685634636939983354155)
        ·
          refine ⟨548528451955409975031233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365685634636939983354155 548528451955409975031233)
          ·
            refine ⟨411396338966557481273425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548528451955409975031233 411396338966557481273425)
            ·
              refine ⟨308547254224918110955069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411396338966557481273425 308547254224918110955069)
              ·
                refine ⟨115705220334344291608151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308547254224918110955069 115705220334344291608151)
                ·
                  rfl

theorem cell19_380253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 3].length) (baseStart_380253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380253 prefixEnd_380253 := by exact prefixLift 380253
  have htrace : WordTrace (prefixWord ++ tailWord_380253) baseStart_380253 baseEnd_380253 := by
    simpa [prefixWord, tailWord_380253, baseEnd_380253] using wordTrace_append hprefix tailTrace_380253
  have hstable : (prefixWord ++ tailWord_380253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380253).length < 2 ^ (prefixWord ++ tailWord_380253).sum := by decide
  have hdescent : baseEnd_380253 < baseStart_380253 := by decide
  rcases family_descends (prefixWord ++ tailWord_380253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380259 : List Nat := [1, 1, 1, 5, 2, 4, 2, 3]
def baseStart_380259 : Nat := 118140960795 + 380259 * 2 ^ 59
def prefixEnd_380259 : Nat := 4983230072969 + 3 ^ 40 * 380259 * 2
def baseEnd_380259 : Nat := 115707046043338055474801

theorem tailTrace_380259 : CollatzResearch.WordTrace tailWord_380259 prefixEnd_380259 115707046043338055474801 := by
  unfold tailWord_380259
  simp only [CollatzResearch.WordTrace]
  refine ⟨13869185129394060911927831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9246123419596040607951887 13869185129394060911927831)
  ·
    refine ⟨20803777694091091367891747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13869185129394060911927831 20803777694091091367891747)
    ·
      refine ⟨31205666541136637051837621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20803777694091091367891747 31205666541136637051837621)
      ·
        refine ⟨2925531238231559723609777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31205666541136637051837621 2925531238231559723609777)
        ·
          refine ⟨2194148428673669792707333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2925531238231559723609777 2194148428673669792707333)
          ·
            refine ⟨411402830376313086132625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2194148428673669792707333 411402830376313086132625)
            ·
              refine ⟨308552122782234814599469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411402830376313086132625 308552122782234814599469)
              ·
                refine ⟨115707046043338055474801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308552122782234814599469 115707046043338055474801)
                ·
                  rfl

theorem cell19_380259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 3].length) (baseStart_380259 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380259 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380259 prefixEnd_380259 := by exact prefixLift 380259
  have htrace : WordTrace (prefixWord ++ tailWord_380259) baseStart_380259 baseEnd_380259 := by
    simpa [prefixWord, tailWord_380259, baseEnd_380259] using wordTrace_append hprefix tailTrace_380259
  have hstable : (prefixWord ++ tailWord_380259).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380259).length < 2 ^ (prefixWord ++ tailWord_380259).sum := by decide
  have hdescent : baseEnd_380259 < baseStart_380259 := by decide
  rcases family_descends (prefixWord ++ tailWord_380259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380320 : List Nat := [2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_380320 : Nat := 118140960795 + 380320 * 2 ^ 59
def prefixEnd_380320 : Nat := 4983230072969 + 3 ^ 40 * 380320 * 2
def baseEnd_380320 : Nat := 115725607418107988119079

theorem tailTrace_380320 : CollatzResearch.WordTrace tailWord_380320 prefixEnd_380320 115725607418107988119079 := by
  unfold tailWord_380320
  simp only [CollatzResearch.WordTrace]
  refine ⟨6935704991086534164949207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9247606654782045553265609 6935704991086534164949207)
  ·
    refine ⟨10403557486629801247423811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6935704991086534164949207 10403557486629801247423811)
    ·
      refine ⟨15605336229944701871135717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10403557486629801247423811 15605336229944701871135717)
      ·
        refine ⟨2926000543114631600837947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15605336229944701871135717 2926000543114631600837947)
        ·
          refine ⟨4389000814671947401256921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2926000543114631600837947 4389000814671947401256921)
          ·
            refine ⟨3291750611003960550942691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4389000814671947401256921 3291750611003960550942691)
            ·
              refine ⟨4937625916505940826414037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291750611003960550942691 4937625916505940826414037)
              ·
                refine ⟨115725607418107988119079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4937625916505940826414037 115725607418107988119079)
                ·
                  rfl

theorem cell19_380320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_380320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380320 prefixEnd_380320 := by exact prefixLift 380320
  have htrace : WordTrace (prefixWord ++ tailWord_380320) baseStart_380320 baseEnd_380320 := by
    simpa [prefixWord, tailWord_380320, baseEnd_380320] using wordTrace_append hprefix tailTrace_380320
  have hstable : (prefixWord ++ tailWord_380320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380320).length < 2 ^ (prefixWord ++ tailWord_380320).sum := by decide
  have hdescent : baseEnd_380320 < baseStart_380320 := by decide
  rcases family_descends (prefixWord ++ tailWord_380320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380394 : List Nat := [3, 1, 3, 1, 4, 1, 6]
def baseStart_380394 : Nat := 118140960795 + 380394 * 2 ^ 59
def prefixEnd_380394 : Nat := 4983230072969 + 3 ^ 40 * 380394 * 2
def baseEnd_380394 : Nat := 38582708165232580824811

theorem tailTrace_380394 : CollatzResearch.WordTrace tailWord_380394 prefixEnd_380394 38582708165232580824811 := by
  unfold tailWord_380394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3468527245976244742023059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9249405989269985978728157 3468527245976244742023059)
  ·
    refine ⟨5202790868964367113034589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3468527245976244742023059 5202790868964367113034589)
    ·
      refine ⟨1951046575861637667387971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5202790868964367113034589 1951046575861637667387971)
      ·
        refine ⟨2926569863792456501081957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951046575861637667387971 2926569863792456501081957)
        ·
          refine ⟨548731849461085593952867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2926569863792456501081957 548731849461085593952867)
          ·
            refine ⟨823097774191628390929301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548731849461085593952867 823097774191628390929301)
            ·
              refine ⟨38582708165232580824811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 823097774191628390929301 38582708165232580824811)
              ·
                rfl

theorem cell19_380394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_380394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380394 prefixEnd_380394 := by exact prefixLift 380394
  have htrace : WordTrace (prefixWord ++ tailWord_380394) baseStart_380394 baseEnd_380394 := by
    simpa [prefixWord, tailWord_380394, baseEnd_380394] using wordTrace_append hprefix tailTrace_380394
  have hstable : (prefixWord ++ tailWord_380394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380394).length < 2 ^ (prefixWord ++ tailWord_380394).sum := by decide
  have hdescent : baseEnd_380394 < baseStart_380394 := by decide
  rcases family_descends (prefixWord ++ tailWord_380394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380422 : List Nat := [6, 2, 1, 1, 3, 1, 2, 3]
def baseStart_380422 : Nat := 118140960795 + 380422 * 2 ^ 59
def prefixEnd_380422 : Nat := 4983230072969 + 3 ^ 40 * 380422 * 2
def baseEnd_380422 : Nat := 115756644471001973852135

theorem tailTrace_380422 : CollatzResearch.WordTrace tailWord_380422 prefixEnd_380422 115756644471001973852135 := by
  unfold tailWord_380422
  simp only [CollatzResearch.WordTrace]
  refine ⟨433597819618860617190985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9250086818535693166741013 433597819618860617190985)
  ·
    refine ⟨325198364714145462893239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 433597819618860617190985 325198364714145462893239)
    ·
      refine ⟨487797547071218194339859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325198364714145462893239 487797547071218194339859)
      ·
        refine ⟨731696320606827291509789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487797547071218194339859 731696320606827291509789)
        ·
          refine ⟨274386120227560234316171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 731696320606827291509789 274386120227560234316171)
          ·
            refine ⟨411579180341340351474257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274386120227560234316171 411579180341340351474257)
            ·
              refine ⟨308684385256005263605693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411579180341340351474257 308684385256005263605693)
              ·
                refine ⟨115756644471001973852135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308684385256005263605693 115756644471001973852135)
                ·
                  rfl

theorem cell19_380422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_380422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380422 prefixEnd_380422 := by exact prefixLift 380422
  have htrace : WordTrace (prefixWord ++ tailWord_380422) baseStart_380422 baseEnd_380422 := by
    simpa [prefixWord, tailWord_380422, baseEnd_380422] using wordTrace_append hprefix tailTrace_380422
  have hstable : (prefixWord ++ tailWord_380422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380422).length < 2 ^ (prefixWord ++ tailWord_380422).sum := by decide
  have hdescent : baseEnd_380422 < baseStart_380422 := by decide
  rcases family_descends (prefixWord ++ tailWord_380422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380428 : List Nat := [2, 2, 1, 2, 6, 1, 2, 3]
def baseStart_380428 : Nat := 118140960795 + 380428 * 2 ^ 59
def prefixEnd_380428 : Nat := 4983230072969 + 3 ^ 40 * 380428 * 2
def baseEnd_380428 : Nat := 115758470179995737718785

theorem tailTrace_380428 : CollatzResearch.WordTrace tailWord_380428 prefixEnd_380428 115758470179995737718785 := by
  unfold tailWord_380428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937674532890901387414969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9250232710521201849886625 6937674532890901387414969)
  ·
    refine ⟨5203255899668176040561227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6937674532890901387414969 5203255899668176040561227)
    ·
      refine ⟨7804883849502264060841841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5203255899668176040561227 7804883849502264060841841)
      ·
        refine ⟨5853662887126698045631381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7804883849502264060841841 5853662887126698045631381)
        ·
          refine ⟨274390447834063970888971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5853662887126698045631381 274390447834063970888971)
          ·
            refine ⟨411585671751095956333457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274390447834063970888971 411585671751095956333457)
            ·
              refine ⟨308689253813321967250093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411585671751095956333457 308689253813321967250093)
              ·
                refine ⟨115758470179995737718785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308689253813321967250093 115758470179995737718785)
                ·
                  rfl

theorem cell19_380428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_380428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380428 prefixEnd_380428 := by exact prefixLift 380428
  have htrace : WordTrace (prefixWord ++ tailWord_380428) baseStart_380428 baseEnd_380428 := by
    simpa [prefixWord, tailWord_380428, baseEnd_380428] using wordTrace_append hprefix tailTrace_380428
  have hstable : (prefixWord ++ tailWord_380428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380428).length < 2 ^ (prefixWord ++ tailWord_380428).sum := by decide
  have hdescent : baseEnd_380428 < baseStart_380428 := by decide
  rcases family_descends (prefixWord ++ tailWord_380428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380451 : List Nat := [1, 1, 1, 4, 5, 2, 5]
def baseStart_380451 : Nat := 118140960795 + 380451 * 2 ^ 59
def prefixEnd_380451 : Nat := 4983230072969 + 3 ^ 40 * 380451 * 2
def baseEnd_380451 : Nat := 38588489577046166402537

theorem tailTrace_380451 : CollatzResearch.WordTrace tailWord_380451 prefixEnd_380451 38588489577046166402537 := by
  unfold tailWord_380451
  simp only [CollatzResearch.WordTrace]
  refine ⟨13876187944698477702917207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9250791963132318468611471 13876187944698477702917207)
  ·
    refine ⟨20814281917047716554375811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13876187944698477702917207 20814281917047716554375811)
    ·
      refine ⟨31221422875571574831563717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20814281917047716554375811 31221422875571574831563717)
      ·
        refine ⟨5854016789169670280918197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31221422875571574831563717 5854016789169670280918197)
        ·
          refine ⟨548814073984656588836081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5854016789169670280918197 548814073984656588836081)
          ·
            refine ⟨411610555488492441627061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548814073984656588836081 411610555488492441627061)
            ·
              refine ⟨38588489577046166402537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 411610555488492441627061 38588489577046166402537)
              ·
                rfl

theorem cell19_380451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_380451 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380451 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380451 prefixEnd_380451 := by exact prefixLift 380451
  have htrace : WordTrace (prefixWord ++ tailWord_380451) baseStart_380451 baseEnd_380451 := by
    simpa [prefixWord, tailWord_380451, baseEnd_380451] using wordTrace_append hprefix tailTrace_380451
  have hstable : (prefixWord ++ tailWord_380451).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380451).length < 2 ^ (prefixWord ++ tailWord_380451).sum := by decide
  have hdescent : baseEnd_380451 < baseStart_380451 := by decide
  rcases family_descends (prefixWord ++ tailWord_380451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380472 : List Nat := [2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_380472 : Nat := 118140960795 + 380472 * 2 ^ 59
def prefixEnd_380472 : Nat := 4983230072969 + 3 ^ 40 * 380472 * 2
def baseEnd_380472 : Nat := 115771858712616672740887

theorem tailTrace_380472 : CollatzResearch.WordTrace tailWord_380472 prefixEnd_380472 115771858712616672740887 := by
  unfold tailWord_380472
  simp only [CollatzResearch.WordTrace]
  refine ⟨6938476938811199144715835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9251302585081598859621113 6938476938811199144715835)
  ·
    refine ⟨10407715408216798717073753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6938476938811199144715835 10407715408216798717073753)
    ·
      refine ⟨7805786556162599037805315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10407715408216798717073753 7805786556162599037805315)
      ·
        refine ⟨11708679834243898556707973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7805786556162599037805315 11708679834243898556707973)
        ·
          refine ⟨2195377468920730979382745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11708679834243898556707973 2195377468920730979382745)
          ·
            refine ⟨1646533101690548234537059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2195377468920730979382745 1646533101690548234537059)
            ·
              refine ⟨2469799652535822351805589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646533101690548234537059 2469799652535822351805589)
              ·
                refine ⟨115771858712616672740887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2469799652535822351805589 115771858712616672740887)
                ·
                  rfl

theorem cell19_380472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_380472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380472 prefixEnd_380472 := by exact prefixLift 380472
  have htrace : WordTrace (prefixWord ++ tailWord_380472) baseStart_380472 baseEnd_380472 := by
    simpa [prefixWord, tailWord_380472, baseEnd_380472] using wordTrace_append hprefix tailTrace_380472
  have hstable : (prefixWord ++ tailWord_380472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380472).length < 2 ^ (prefixWord ++ tailWord_380472).sum := by decide
  have hdescent : baseEnd_380472 < baseStart_380472 := by decide
  rcases family_descends (prefixWord ++ tailWord_380472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380525 : List Nat := [1, 5, 1, 1, 4, 2, 1, 4]
def baseStart_380525 : Nat := 118140960795 + 380525 * 2 ^ 59
def prefixEnd_380525 : Nat := 4983230072969 + 3 ^ 40 * 380525 * 2
def baseEnd_380525 : Nat := 115787985808728253562965

theorem tailTrace_380525 : CollatzResearch.WordTrace tailWord_380525 prefixEnd_380525 115787985808728253562965 := by
  unfold tailWord_380525
  simp only [CollatzResearch.WordTrace]
  refine ⟨13878886946430388341111029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9252591297620258894074019 13878886946430388341111029)
  ·
    refine ⟨1301145651227848906979159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13878886946430388341111029 1301145651227848906979159)
    ·
      refine ⟨1951718476841773360468739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301145651227848906979159 1951718476841773360468739)
      ·
        refine ⟨2927577715262660040703109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951718476841773360468739 2927577715262660040703109)
        ·
          refine ⟨548920821611748757631833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2927577715262660040703109 548920821611748757631833)
          ·
            refine ⟨411690616208811568223875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548920821611748757631833 411690616208811568223875)
            ·
              refine ⟨617535924313217352335813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411690616208811568223875 617535924313217352335813)
              ·
                refine ⟨115787985808728253562965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 617535924313217352335813 115787985808728253562965)
                ·
                  rfl

theorem cell19_380525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_380525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380525 prefixEnd_380525 := by exact prefixLift 380525
  have htrace : WordTrace (prefixWord ++ tailWord_380525) baseStart_380525 baseEnd_380525 := by
    simpa [prefixWord, tailWord_380525, baseEnd_380525] using wordTrace_append hprefix tailTrace_380525
  have hstable : (prefixWord ++ tailWord_380525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380525).length < 2 ^ (prefixWord ++ tailWord_380525).sum := by decide
  have hdescent : baseEnd_380525 < baseStart_380525 := by decide
  rcases family_descends (prefixWord ++ tailWord_380525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380567 : List Nat := [1, 1, 3, 3, 2, 3, 6]
def baseStart_380567 : Nat := 118140960795 + 380567 * 2 ^ 59
def prefixEnd_380567 : Nat := 4983230072969 + 3 ^ 40 * 380567 * 2
def baseEnd_380567 : Nat := 38600255257228200209839

theorem tailTrace_380567 : CollatzResearch.WordTrace tailWord_380567 prefixEnd_380567 38600255257228200209839 := by
  unfold tailWord_380567
  simp only [CollatzResearch.WordTrace]
  refine ⟨13880418812278229514139955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9253612541518819676093303 13880418812278229514139955)
  ·
    refine ⟨20820628218417344271209933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13880418812278229514139955 20820628218417344271209933)
    ·
      refine ⟨7807735581906504101703725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20820628218417344271209933 7807735581906504101703725)
      ·
        refine ⟨2927900843214939038138897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7807735581906504101703725 2927900843214939038138897)
        ·
          refine ⟨2195925632411204278604173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2927900843214939038138897 2195925632411204278604173)
          ·
            refine ⟨823472112154201604476565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2195925632411204278604173 823472112154201604476565)
            ·
              refine ⟨38600255257228200209839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 823472112154201604476565 38600255257228200209839)
              ·
                rfl

theorem cell19_380567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_380567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380567 prefixEnd_380567 := by exact prefixLift 380567
  have htrace : WordTrace (prefixWord ++ tailWord_380567) baseStart_380567 baseEnd_380567 := by
    simpa [prefixWord, tailWord_380567, baseEnd_380567] using wordTrace_append hprefix tailTrace_380567
  have hstable : (prefixWord ++ tailWord_380567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380567).length < 2 ^ (prefixWord ++ tailWord_380567).sum := by decide
  have hdescent : baseEnd_380567 < baseStart_380567 := by decide
  rcases family_descends (prefixWord ++ tailWord_380567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380605 : List Nat := [1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_380605 : Nat := 118140960795 + 380605 * 2 ^ 59
def prefixEnd_380605 : Nat := 4983230072969 + 3 ^ 40 * 380605 * 2
def baseEnd_380605 : Nat := 115812328595311771784969

theorem tailTrace_380605 : CollatzResearch.WordTrace tailWord_380605 prefixEnd_380605 115812328595311771784969 := by
  unfold tailWord_380605
  simp only [CollatzResearch.WordTrace]
  refine ⟨13881804786140562004023269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9254536524093708002682179 13881804786140562004023269)
  ·
    refine ⟨2602838397401355375754363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13881804786140562004023269 2602838397401355375754363)
    ·
      refine ⟨3904257596102033063631545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2602838397401355375754363 3904257596102033063631545)
      ·
        refine ⟨2928193197076524797723659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3904257596102033063631545 2928193197076524797723659)
        ·
          refine ⟨4392289795614787196585489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2928193197076524797723659 4392289795614787196585489)
          ·
            refine ⟨3294217346711090397439117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4392289795614787196585489 3294217346711090397439117)
            ·
              refine ⟨1235331505016658899039669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3294217346711090397439117 1235331505016658899039669)
              ·
                refine ⟨115812328595311771784969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1235331505016658899039669 115812328595311771784969)
                ·
                  rfl

theorem cell19_380605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_380605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380605 prefixEnd_380605 := by exact prefixLift 380605
  have htrace : WordTrace (prefixWord ++ tailWord_380605) baseStart_380605 baseEnd_380605 := by
    simpa [prefixWord, tailWord_380605, baseEnd_380605] using wordTrace_append hprefix tailTrace_380605
  have hstable : (prefixWord ++ tailWord_380605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380605).length < 2 ^ (prefixWord ++ tailWord_380605).sum := by decide
  have hdescent : baseEnd_380605 < baseStart_380605 := by decide
  rcases family_descends (prefixWord ++ tailWord_380605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380620 : List Nat := [2, 2, 1, 5, 3, 1, 5]
def baseStart_380620 : Nat := 118140960795 + 380620 * 2 ^ 59
def prefixEnd_380620 : Nat := 4983230072969 + 3 ^ 40 * 380620 * 2
def baseEnd_380620 : Nat := 38605630955932060483865

theorem tailTrace_380620 : CollatzResearch.WordTrace tailWord_380620 prefixEnd_380620 38605630955932060483865 := by
  unfold tailWord_380620
  simp only [CollatzResearch.WordTrace]
  refine ⟨6941175940543109782909657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9254901254057479710546209 6941175940543109782909657)
  ·
    refine ⟨5205881955407332337182243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6941175940543109782909657 5205881955407332337182243)
    ·
      refine ⟨7808822933110998505773365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5205881955407332337182243 7808822933110998505773365)
      ·
        refine ⟨732077149979156109916253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7808822933110998505773365 732077149979156109916253)
        ·
          refine ⟨274528931242183541218595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 732077149979156109916253 274528931242183541218595)
          ·
            refine ⟨411793396863275311827893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274528931242183541218595 411793396863275311827893)
            ·
              refine ⟨38605630955932060483865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 411793396863275311827893 38605630955932060483865)
              ·
                rfl

theorem cell19_380620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 5].length) (baseStart_380620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380620 prefixEnd_380620 := by exact prefixLift 380620
  have htrace : WordTrace (prefixWord ++ tailWord_380620) baseStart_380620 baseEnd_380620 := by
    simpa [prefixWord, tailWord_380620, baseEnd_380620] using wordTrace_append hprefix tailTrace_380620
  have hstable : (prefixWord ++ tailWord_380620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380620).length < 2 ^ (prefixWord ++ tailWord_380620).sum := by decide
  have hdescent : baseEnd_380620 < baseStart_380620 := by decide
  rcases family_descends (prefixWord ++ tailWord_380620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380641 : List Nat := [1, 2, 3, 1, 5, 1, 2, 4]
def baseStart_380641 : Nat := 118140960795 + 380641 * 2 ^ 59
def prefixEnd_380641 : Nat := 4983230072969 + 3 ^ 40 * 380641 * 2
def baseEnd_380641 : Nat := 115823282849274354984871

theorem tailTrace_380641 : CollatzResearch.WordTrace tailWord_380641 prefixEnd_380641 115823282849274354984871 := by
  unfold tailWord_380641
  simp only [CollatzResearch.WordTrace]
  refine ⟨13883117814010140152333777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9255411876006760101555851 13883117814010140152333777)
  ·
    refine ⟨10412338360507605114250333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13883117814010140152333777 10412338360507605114250333)
    ·
      refine ⟨3904626885190351917843875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10412338360507605114250333 3904626885190351917843875)
      ·
        refine ⟨5856940327785527876765813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904626885190351917843875 5856940327785527876765813)
        ·
          refine ⟨549088155729893238446795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5856940327785527876765813 549088155729893238446795)
          ·
            refine ⟨823632233594839857670193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549088155729893238446795 823632233594839857670193)
            ·
              refine ⟨617724175196129893252645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823632233594839857670193 617724175196129893252645)
              ·
                refine ⟨115823282849274354984871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 617724175196129893252645 115823282849274354984871)
                ·
                  rfl

theorem cell19_380641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_380641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380641 prefixEnd_380641 := by exact prefixLift 380641
  have htrace : WordTrace (prefixWord ++ tailWord_380641) baseStart_380641 baseEnd_380641 := by
    simpa [prefixWord, tailWord_380641, baseEnd_380641] using wordTrace_append hprefix tailTrace_380641
  have hstable : (prefixWord ++ tailWord_380641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380641).length < 2 ^ (prefixWord ++ tailWord_380641).sum := by decide
  have hdescent : baseEnd_380641 < baseStart_380641 := by decide
  rcases family_descends (prefixWord ++ tailWord_380641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380679 : List Nat := [1, 1, 4, 4, 3, 6]
def baseStart_380679 : Nat := 118140960795 + 380679 * 2 ^ 59
def prefixEnd_380679 : Nat := 4983230072969 + 3 ^ 40 * 380679 * 2
def baseEnd_380679 : Nat := 12870538408100169571147

theorem tailTrace_380679 : CollatzResearch.WordTrace tailWord_380679 prefixEnd_380679 12870538408100169571147 := by
  unfold tailWord_380679
  simp only [CollatzResearch.WordTrace]
  refine ⟨13884503787872472642217091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9256335858581648428144727 13884503787872472642217091)
  ·
    refine ⟨20826755681808708963325637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13884503787872472642217091 20826755681808708963325637)
    ·
      refine ⟨3905016690339132930623557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20826755681808708963325637 3905016690339132930623557)
      ·
        refine ⟨732190629438587424491917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3905016690339132930623557 732190629438587424491917)
        ·
          refine ⟨274571486039470284184469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 732190629438587424491917 274571486039470284184469)
          ·
            refine ⟨12870538408100169571147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 274571486039470284184469 12870538408100169571147)
            ·
              rfl

theorem cell19_380679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 6].length) (baseStart_380679 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380679 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380679 prefixEnd_380679 := by exact prefixLift 380679
  have htrace : WordTrace (prefixWord ++ tailWord_380679) baseStart_380679 baseEnd_380679 := by
    simpa [prefixWord, tailWord_380679, baseEnd_380679] using wordTrace_append hprefix tailTrace_380679
  have hstable : (prefixWord ++ tailWord_380679).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380679).length < 2 ^ (prefixWord ++ tailWord_380679).sum := by decide
  have hdescent : baseEnd_380679 < baseStart_380679 := by decide
  rcases family_descends (prefixWord ++ tailWord_380679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380692 : List Nat := [2, 4, 4, 1, 1, 2, 1, 4]
def baseStart_380692 : Nat := 118140960795 + 380692 * 2 ^ 59
def prefixEnd_380692 : Nat := 4983230072969 + 3 ^ 40 * 380692 * 2
def baseEnd_380692 : Nat := 115838801375721347851399

theorem tailTrace_380692 : CollatzResearch.WordTrace tailWord_380692 prefixEnd_380692 115838801375721347851399 := by
  unfold tailWord_380692
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942488968412687931220165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9256651957883583908293553 6942488968412687931220165)
  ·
    refine ⟨1301716681577378987103781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6942488968412687931220165 1301716681577378987103781)
    ·
      refine ⟨244071877795758560081959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1301716681577378987103781 244071877795758560081959)
      ·
        refine ⟨366107816693637840122939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244071877795758560081959 366107816693637840122939)
        ·
          refine ⟨549161725040456760184409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366107816693637840122939 549161725040456760184409)
          ·
            refine ⟨411871293780342570138307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549161725040456760184409 411871293780342570138307)
            ·
              refine ⟨617806940670513855207461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411871293780342570138307 617806940670513855207461)
              ·
                refine ⟨115838801375721347851399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 617806940670513855207461 115838801375721347851399)
                ·
                  rfl

theorem cell19_380692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_380692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380692 prefixEnd_380692 := by exact prefixLift 380692
  have htrace : WordTrace (prefixWord ++ tailWord_380692) baseStart_380692 baseEnd_380692 := by
    simpa [prefixWord, tailWord_380692, baseEnd_380692] using wordTrace_append hprefix tailTrace_380692
  have hstable : (prefixWord ++ tailWord_380692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380692).length < 2 ^ (prefixWord ++ tailWord_380692).sum := by decide
  have hdescent : baseEnd_380692 < baseStart_380692 := by decide
  rcases family_descends (prefixWord ++ tailWord_380692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380698 : List Nat := [3, 1, 1, 3, 2, 4, 1, 4]
def baseStart_380698 : Nat := 118140960795 + 380698 * 2 ^ 59
def prefixEnd_380698 : Nat := 4983230072969 + 3 ^ 40 * 380698 * 2
def baseEnd_380698 : Nat := 115840627084715111718049

theorem tailTrace_380698 : CollatzResearch.WordTrace tailWord_380698 prefixEnd_380698 115840627084715111718049 := by
  unfold tailWord_380698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3471299193700909721789687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9256797849869092591439165 3471299193700909721789687)
  ·
    refine ⟨5206948790551364582684531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3471299193700909721789687 5206948790551364582684531)
    ·
      refine ⟨7810423185827046874026797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5206948790551364582684531 7810423185827046874026797)
      ·
        refine ⟨2928908694685142577760049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7810423185827046874026797 2928908694685142577760049)
        ·
          refine ⟨2196681521013856933320037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2928908694685142577760049 2196681521013856933320037)
          ·
            refine ⟨411877785190098174997507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2196681521013856933320037 411877785190098174997507)
            ·
              refine ⟨617816677785147262496261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411877785190098174997507 617816677785147262496261)
              ·
                refine ⟨115840627084715111718049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 617816677785147262496261 115840627084715111718049)
                ·
                  rfl

theorem cell19_380698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_380698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380698 prefixEnd_380698 := by exact prefixLift 380698
  have htrace : WordTrace (prefixWord ++ tailWord_380698) baseStart_380698 baseEnd_380698 := by
    simpa [prefixWord, tailWord_380698, baseEnd_380698] using wordTrace_append hprefix tailTrace_380698
  have hstable : (prefixWord ++ tailWord_380698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380698).length < 2 ^ (prefixWord ++ tailWord_380698).sum := by decide
  have hdescent : baseEnd_380698 < baseStart_380698 := by decide
  rcases family_descends (prefixWord ++ tailWord_380698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380772 : List Nat := [2, 3, 1, 1, 5, 2, 2, 3]
def baseStart_380772 : Nat := 118140960795 + 380772 * 2 ^ 59
def prefixEnd_380772 : Nat := 4983230072969 + 3 ^ 40 * 380772 * 2
def baseEnd_380772 : Nat := 115863144162304866073403

theorem tailTrace_380772 : CollatzResearch.WordTrace tailWord_380772 prefixEnd_380772 115863144162304866073403 := by
  unfold tailWord_380772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6943947888267774762676285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9258597184357033016901713 6943947888267774762676285)
  ·
    refine ⟨2603980458100415536003607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6943947888267774762676285 2603980458100415536003607)
    ·
      refine ⟨3905970687150623304005411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603980458100415536003607 3905970687150623304005411)
      ·
        refine ⟨5858956030725934956008117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905970687150623304005411 5858956030725934956008117)
        ·
          refine ⟨549277127880556402125761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5858956030725934956008117 549277127880556402125761)
          ·
            refine ⟨411957845910417301594321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549277127880556402125761 411957845910417301594321)
            ·
              refine ⟨308968384432812976195741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411957845910417301594321 308968384432812976195741)
              ·
                refine ⟨115863144162304866073403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308968384432812976195741 115863144162304866073403)
                ·
                  rfl

theorem cell19_380772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_380772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380772 prefixEnd_380772 := by exact prefixLift 380772
  have htrace : WordTrace (prefixWord ++ tailWord_380772) baseStart_380772 baseEnd_380772 := by
    simpa [prefixWord, tailWord_380772, baseEnd_380772] using wordTrace_append hprefix tailTrace_380772
  have hstable : (prefixWord ++ tailWord_380772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380772).length < 2 ^ (prefixWord ++ tailWord_380772).sum := by decide
  have hdescent : baseEnd_380772 < baseStart_380772 := by decide
  rcases family_descends (prefixWord ++ tailWord_380772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380776 : List Nat := [2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_380776 : Nat := 118140960795 + 380776 * 2 ^ 59
def prefixEnd_380776 : Nat := 4983230072969 + 3 ^ 40 * 380776 * 2
def baseEnd_380776 : Nat := 115864361301634041984503

theorem tailTrace_380776 : CollatzResearch.WordTrace tailWord_380776 prefixEnd_380776 115864361301634041984503 := by
  unfold tailWord_380776
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944020834260529104249091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9258694445680705472332121 6944020834260529104249091)
  ·
    refine ⟨10416031251390793656373637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6944020834260529104249091 10416031251390793656373637)
    ·
      refine ⟨1953005859635773810570057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10416031251390793656373637 1953005859635773810570057)
      ·
        refine ⟨1464754394726830357927543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1953005859635773810570057 1464754394726830357927543)
        ·
          refine ⟨2197131592090245536891315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464754394726830357927543 2197131592090245536891315)
          ·
            refine ⟨3295697388135368305336973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197131592090245536891315 3295697388135368305336973)
            ·
              refine ⟨1235886520550763114501365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3295697388135368305336973 1235886520550763114501365)
              ·
                refine ⟨115864361301634041984503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1235886520550763114501365 115864361301634041984503)
                ·
                  rfl

theorem cell19_380776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_380776 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380776 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380776 prefixEnd_380776 := by exact prefixLift 380776
  have htrace : WordTrace (prefixWord ++ tailWord_380776) baseStart_380776 baseEnd_380776 := by
    simpa [prefixWord, tailWord_380776, baseEnd_380776] using wordTrace_append hprefix tailTrace_380776
  have hstable : (prefixWord ++ tailWord_380776).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380776).length < 2 ^ (prefixWord ++ tailWord_380776).sum := by decide
  have hdescent : baseEnd_380776 < baseStart_380776 := by decide
  rcases family_descends (prefixWord ++ tailWord_380776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380816 : List Nat := [2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_380816 : Nat := 118140960795 + 380816 * 2 ^ 59
def prefixEnd_380816 : Nat := 4983230072969 + 3 ^ 40 * 380816 * 2
def baseEnd_380816 : Nat := 115876532694925801095505

theorem tailTrace_380816 : CollatzResearch.WordTrace tailWord_380816 prefixEnd_380816 115876532694925801095505 := by
  unfold tailWord_380816
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944750294188072519977151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9259667058917430026636201 6944750294188072519977151)
  ·
    refine ⟨10417125441282108779965727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6944750294188072519977151 10417125441282108779965727)
    ·
      refine ⟨15625688161923163169948591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10417125441282108779965727 15625688161923163169948591)
      ·
        refine ⟨23438532242884744754922887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15625688161923163169948591 23438532242884744754922887)
        ·
          refine ⟨35157798364327117132384331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23438532242884744754922887 35157798364327117132384331)
          ·
            refine ⟨52736697546490675698576497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35157798364327117132384331 52736697546490675698576497)
            ·
              refine ⟨39552523159868006773932373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52736697546490675698576497 39552523159868006773932373)
              ·
                refine ⟨115876532694925801095505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39552523159868006773932373 115876532694925801095505)
                ·
                  rfl

theorem cell19_380816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_380816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380816 prefixEnd_380816 := by exact prefixLift 380816
  have htrace : WordTrace (prefixWord ++ tailWord_380816) baseStart_380816 baseEnd_380816 := by
    simpa [prefixWord, tailWord_380816, baseEnd_380816] using wordTrace_append hprefix tailTrace_380816
  have hstable : (prefixWord ++ tailWord_380816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380816).length < 2 ^ (prefixWord ++ tailWord_380816).sum := by decide
  have hdescent : baseEnd_380816 < baseStart_380816 := by decide
  rcases family_descends (prefixWord ++ tailWord_380816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380846 : List Nat := [4, 1, 5, 1, 2, 6]
def baseStart_380846 : Nat := 118140960795 + 380846 * 2 ^ 59
def prefixEnd_380846 : Nat := 4983230072969 + 3 ^ 40 * 380846 * 2
def baseEnd_380846 : Nat := 12876184582210513380973

theorem tailTrace_380846 : CollatzResearch.WordTrace tailWord_380846 prefixEnd_380846 12876184582210513380973 := by
  unfold tailWord_380846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1736324347283432520443299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9260396518844973442364261 1736324347283432520443299)
  ·
    refine ⟨2604486520925148780664949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1736324347283432520443299 2604486520925148780664949)
    ·
      refine ⟨244170611336732698187339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2604486520925148780664949 244170611336732698187339)
      ·
        refine ⟨366255917005099047281009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244170611336732698187339 366255917005099047281009)
        ·
          refine ⟨274691937753824285460757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366255917005099047281009 274691937753824285460757)
          ·
            refine ⟨12876184582210513380973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 274691937753824285460757 12876184582210513380973)
            ·
              rfl

theorem cell19_380846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 6].length) (baseStart_380846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380846 prefixEnd_380846 := by exact prefixLift 380846
  have htrace : WordTrace (prefixWord ++ tailWord_380846) baseStart_380846 baseEnd_380846 := by
    simpa [prefixWord, tailWord_380846, baseEnd_380846] using wordTrace_append hprefix tailTrace_380846
  have hstable : (prefixWord ++ tailWord_380846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380846).length < 2 ^ (prefixWord ++ tailWord_380846).sum := by decide
  have hdescent : baseEnd_380846 < baseStart_380846 := by decide
  rcases family_descends (prefixWord ++ tailWord_380846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380911 : List Nat := [1, 1, 2, 1, 4, 2, 8]
def baseStart_380911 : Nat := 118140960795 + 380911 * 2 ^ 59
def prefixEnd_380911 : Nat := 4983230072969 + 3 ^ 40 * 380911 * 2
def baseEnd_380911 : Nat := 38635146584664576328045

theorem tailTrace_380911 : CollatzResearch.WordTrace tailWord_380911 prefixEnd_380911 38635146584664576328045 := by
  unfold tailWord_380911
  simp only [CollatzResearch.WordTrace]
  refine ⟨13892965523031976264662587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9261977015354650843108391 13892965523031976264662587)
  ·
    refine ⟨20839448284547964396993881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13892965523031976264662587 20839448284547964396993881)
    ·
      refine ⟨15629586213410973297745411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20839448284547964396993881 15629586213410973297745411)
      ·
        refine ⟨23444379320116459946618117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15629586213410973297745411 23444379320116459946618117)
        ·
          refine ⟨4395821122521836239990897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23444379320116459946618117 4395821122521836239990897)
          ·
            refine ⟨3296865841891377179993173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4395821122521836239990897 3296865841891377179993173)
            ·
              refine ⟨38635146584664576328045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3296865841891377179993173 38635146584664576328045)
              ·
                rfl

theorem cell19_380911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_380911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380911 prefixEnd_380911 := by exact prefixLift 380911
  have htrace : WordTrace (prefixWord ++ tailWord_380911) baseStart_380911 baseEnd_380911 := by
    simpa [prefixWord, tailWord_380911, baseEnd_380911] using wordTrace_append hprefix tailTrace_380911
  have hstable : (prefixWord ++ tailWord_380911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380911).length < 2 ^ (prefixWord ++ tailWord_380911).sum := by decide
  have hdescent : baseEnd_380911 < baseStart_380911 := by decide
  rcases family_descends (prefixWord ++ tailWord_380911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380941 : List Nat := [1, 7, 1, 2, 1, 1, 1, 5]
def baseStart_380941 : Nat := 118140960795 + 380941 * 2 ^ 59
def prefixEnd_380941 : Nat := 4983230072969 + 3 ^ 40 * 380941 * 2
def baseEnd_380941 : Nat := 115914568298962548317387

theorem tailTrace_380941 : CollatzResearch.WordTrace tailWord_380941 prefixEnd_380941 115914568298962548317387 := by
  unfold tailWord_380941
  simp only [CollatzResearch.WordTrace]
  refine ⟨13894059712923291388254677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9262706475282194258836451 13894059712923291388254677)
  ·
    refine ⟨325642024521639641912219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13894059712923291388254677 325642024521639641912219)
    ·
      refine ⟨488463036782459462868329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325642024521639641912219 488463036782459462868329)
      ·
        refine ⟨366347277586844597151247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488463036782459462868329 366347277586844597151247)
        ·
          refine ⟨549520916380266895726871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366347277586844597151247 549520916380266895726871)
          ·
            refine ⟨824281374570400343590307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549520916380266895726871 824281374570400343590307)
            ·
              refine ⟨1236422061855600515385461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824281374570400343590307 1236422061855600515385461)
              ·
                refine ⟨115914568298962548317387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1236422061855600515385461 115914568298962548317387)
                ·
                  rfl

theorem cell19_380941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 5].length) (baseStart_380941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380941 prefixEnd_380941 := by exact prefixLift 380941
  have htrace : WordTrace (prefixWord ++ tailWord_380941) baseStart_380941 baseEnd_380941 := by
    simpa [prefixWord, tailWord_380941, baseEnd_380941] using wordTrace_append hprefix tailTrace_380941
  have hstable : (prefixWord ++ tailWord_380941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380941).length < 2 ^ (prefixWord ++ tailWord_380941).sum := by decide
  have hdescent : baseEnd_380941 < baseStart_380941 := by decide
  rcases family_descends (prefixWord ++ tailWord_380941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380947 : List Nat := [1, 1, 1, 2, 1, 4, 6, 3]
def baseStart_380947 : Nat := 118140960795 + 380947 * 2 ^ 59
def prefixEnd_380947 : Nat := 4983230072969 + 3 ^ 40 * 380947 * 2
def baseEnd_380947 : Nat := 115916394007956312184037

theorem tailTrace_380947 : CollatzResearch.WordTrace tailWord_380947 prefixEnd_380947 115916394007956312184037 := by
  unfold tailWord_380947
  simp only [CollatzResearch.WordTrace]
  refine ⟨13894278550901554412973095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9262852367267702941982063 13894278550901554412973095)
  ·
    refine ⟨20841417826352331619459643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13894278550901554412973095 20841417826352331619459643)
    ·
      refine ⟨31262126739528497429189465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20841417826352331619459643 31262126739528497429189465)
      ·
        refine ⟨23446595054646373071892099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31262126739528497429189465 23446595054646373071892099)
        ·
          refine ⟨35169892581969559607838149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23446595054646373071892099 35169892581969559607838149)
          ·
            refine ⟨6594354859119292426469653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35169892581969559607838149 6594354859119292426469653)
            ·
              refine ⟨309110384021216832490765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6594354859119292426469653 309110384021216832490765)
              ·
                refine ⟨115916394007956312184037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309110384021216832490765 115916394007956312184037)
                ·
                  rfl

theorem cell19_380947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 3].length) (baseStart_380947 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380947 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380947 prefixEnd_380947 := by exact prefixLift 380947
  have htrace : WordTrace (prefixWord ++ tailWord_380947) baseStart_380947 baseEnd_380947 := by
    simpa [prefixWord, tailWord_380947, baseEnd_380947] using wordTrace_append hprefix tailTrace_380947
  have hstable : (prefixWord ++ tailWord_380947).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380947).length < 2 ^ (prefixWord ++ tailWord_380947).sum := by decide
  have hdescent : baseEnd_380947 < baseStart_380947 := by decide
  rcases family_descends (prefixWord ++ tailWord_380947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380964 : List Nat := [2, 3, 1, 4, 2, 2, 5]
def baseStart_380964 : Nat := 118140960795 + 380964 * 2 ^ 59
def prefixEnd_380964 : Nat := 4983230072969 + 3 ^ 40 * 380964 * 2
def baseEnd_380964 : Nat := 38640522283368436602071

theorem tailTrace_380964 : CollatzResearch.WordTrace tailWord_380964 prefixEnd_380964 38640522283368436602071 := by
  unfold tailWord_380964
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947449295919983158170973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9263265727893310877561297 6947449295919983158170973)
  ·
    refine ⟨2605293485969993684314115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6947449295919983158170973 2605293485969993684314115)
    ·
      refine ⟨3907940228954990526471173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2605293485969993684314115 3907940228954990526471173)
      ·
        refine ⟨732738792929060723713345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3907940228954990526471173 732738792929060723713345)
        ·
          refine ⟨549554094696795542785009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732738792929060723713345 549554094696795542785009)
          ·
            refine ⟨412165571022596657088757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549554094696795542785009 412165571022596657088757)
            ·
              refine ⟨38640522283368436602071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 412165571022596657088757 38640522283368436602071)
              ·
                rfl

theorem cell19_380964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_380964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_380964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_380964 prefixEnd_380964 := by exact prefixLift 380964
  have htrace : WordTrace (prefixWord ++ tailWord_380964) baseStart_380964 baseEnd_380964 := by
    simpa [prefixWord, tailWord_380964, baseEnd_380964] using wordTrace_append hprefix tailTrace_380964
  have hstable : (prefixWord ++ tailWord_380964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380964).length < 2 ^ (prefixWord ++ tailWord_380964).sum := by decide
  have hdescent : baseEnd_380964 < baseStart_380964 := by decide
  rcases family_descends (prefixWord ++ tailWord_380964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381042 : List Nat := [3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_381042 : Nat := 118140960795 + 381042 * 2 ^ 59
def prefixEnd_381042 : Nat := 4983230072969 + 3 ^ 40 * 381042 * 2
def baseEnd_381042 : Nat := 115945301067024240072667

theorem tailTrace_381042 : CollatzResearch.WordTrace tailWord_381042 prefixEnd_381042 115945301067024240072667 := by
  unfold tailWord_381042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3474435871389346409420345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9265162323704923758454253 3474435871389346409420345)
  ·
    refine ⟨2605826903542009807065259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3474435871389346409420345 2605826903542009807065259)
    ·
      refine ⟨3908740355313014710597889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2605826903542009807065259 3908740355313014710597889)
      ·
        refine ⟨2931555266484761032948417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3908740355313014710597889 2931555266484761032948417)
        ·
          refine ⟨2198666449863570774711313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2931555266484761032948417 2198666449863570774711313)
          ·
            refine ⟨1648999837397678081033485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2198666449863570774711313 1648999837397678081033485)
            ·
              refine ⟨618374939024129280387557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1648999837397678081033485 618374939024129280387557)
              ·
                refine ⟨115945301067024240072667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 618374939024129280387557 115945301067024240072667)
                ·
                  rfl

theorem cell19_381042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_381042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381042 prefixEnd_381042 := by exact prefixLift 381042
  have htrace : WordTrace (prefixWord ++ tailWord_381042) baseStart_381042 baseEnd_381042 := by
    simpa [prefixWord, tailWord_381042, baseEnd_381042] using wordTrace_append hprefix tailTrace_381042
  have hstable : (prefixWord ++ tailWord_381042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381042).length < 2 ^ (prefixWord ++ tailWord_381042).sum := by decide
  have hdescent : baseEnd_381042 < baseStart_381042 := by decide
  rcases family_descends (prefixWord ++ tailWord_381042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381063 : List Nat := [1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_381063 : Nat := 118140960795 + 381063 * 2 ^ 59
def prefixEnd_381063 : Nat := 4983230072969 + 3 ^ 40 * 381063 * 2
def baseEnd_381063 : Nat := 115951691048502413605943

theorem tailTrace_381063 : CollatzResearch.WordTrace tailWord_381063 prefixEnd_381063 115951691048502413605943 := by
  unfold tailWord_381063
  simp only [CollatzResearch.WordTrace]
  refine ⟨13898509418481306224195843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9265672945654204149463895 13898509418481306224195843)
  ·
    refine ⟨20847764127721959336293765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13898509418481306224195843 20847764127721959336293765)
    ·
      refine ⟨3908955773947867375555081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20847764127721959336293765 3908955773947867375555081)
      ·
        refine ⟨2931716830460900531666311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3908955773947867375555081 2931716830460900531666311)
        ·
          refine ⟨4397575245691350797499467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2931716830460900531666311 4397575245691350797499467)
          ·
            refine ⟨6596362868537026196249201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4397575245691350797499467 6596362868537026196249201)
            ·
              refine ⟨4947272151402769647186901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6596362868537026196249201 4947272151402769647186901)
              ·
                refine ⟨115951691048502413605943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4947272151402769647186901 115951691048502413605943)
                ·
                  rfl

theorem cell19_381063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_381063 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381063 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381063 prefixEnd_381063 := by exact prefixLift 381063
  have htrace : WordTrace (prefixWord ++ tailWord_381063) baseStart_381063 baseEnd_381063 := by
    simpa [prefixWord, tailWord_381063, baseEnd_381063] using wordTrace_append hprefix tailTrace_381063
  have hstable : (prefixWord ++ tailWord_381063).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381063).length < 2 ^ (prefixWord ++ tailWord_381063).sum := by decide
  have hdescent : baseEnd_381063 < baseStart_381063 := by decide
  rcases family_descends (prefixWord ++ tailWord_381063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381080 : List Nat := [2, 1, 2, 4, 3, 1, 6]
def baseStart_381080 : Nat := 118140960795 + 381080 * 2 ^ 59
def prefixEnd_381080 : Nat := 4983230072969 + 3 ^ 40 * 381080 * 2
def baseEnd_381080 : Nat := 38652287963550470409373

theorem tailTrace_381080 : CollatzResearch.WordTrace tailWord_381080 prefixEnd_381080 38652287963550470409373 := by
  unfold tailWord_381080
  simp only [CollatzResearch.WordTrace]
  refine ⟨6949564729709859063782347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9266086306279812085043129 6949564729709859063782347)
  ·
    refine ⟨10424347094564788595673521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6949564729709859063782347 10424347094564788595673521)
    ·
      refine ⟨7818260320923591446755141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10424347094564788595673521 7818260320923591446755141)
      ·
        refine ⟨1465923810173173396266589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7818260320923591446755141 1465923810173173396266589)
        ·
          refine ⟨549721428814940023599971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1465923810173173396266589 549721428814940023599971)
          ·
            refine ⟨824582143222410035399957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549721428814940023599971 824582143222410035399957)
            ·
              refine ⟨38652287963550470409373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 824582143222410035399957 38652287963550470409373)
              ·
                rfl

theorem cell19_381080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_381080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381080 prefixEnd_381080 := by exact prefixLift 381080
  have htrace : WordTrace (prefixWord ++ tailWord_381080) baseStart_381080 baseEnd_381080 := by
    simpa [prefixWord, tailWord_381080, baseEnd_381080] using wordTrace_append hprefix tailTrace_381080
  have hstable : (prefixWord ++ tailWord_381080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381080).length < 2 ^ (prefixWord ++ tailWord_381080).sum := by decide
  have hdescent : baseEnd_381080 < baseStart_381080 := by decide
  rcases family_descends (prefixWord ++ tailWord_381080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381108 : List Nat := [2, 5, 3, 1, 2, 1, 2, 3]
def baseStart_381108 : Nat := 118140960795 + 381108 * 2 ^ 59
def prefixEnd_381108 : Nat := 4983230072969 + 3 ^ 40 * 381108 * 2
def baseEnd_381108 : Nat := 115965383865955642605821

theorem tailTrace_381108 : CollatzResearch.WordTrace tailWord_381108 prefixEnd_381108 115965383865955642605821 := by
  unfold tailWord_381108
  simp only [CollatzResearch.WordTrace]
  refine ⟨6950075351659139454791989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9266767135545519273055985 6950075351659139454791989)
  ·
    refine ⟨651569564218044323886749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6950075351659139454791989 651569564218044323886749)
    ·
      refine ⟨244338586581766621457531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 651569564218044323886749 244338586581766621457531)
      ·
        refine ⟨366507879872649932186297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244338586581766621457531 366507879872649932186297)
        ·
          refine ⟨274880909904487449139723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366507879872649932186297 274880909904487449139723)
          ·
            refine ⟨412321364856731173709585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274880909904487449139723 412321364856731173709585)
            ·
              refine ⟨309241023642548380282189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412321364856731173709585 309241023642548380282189)
              ·
                refine ⟨115965383865955642605821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309241023642548380282189 115965383865955642605821)
                ·
                  rfl

theorem cell19_381108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_381108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381108 prefixEnd_381108 := by exact prefixLift 381108
  have htrace : WordTrace (prefixWord ++ tailWord_381108) baseStart_381108 baseEnd_381108 := by
    simpa [prefixWord, tailWord_381108, baseEnd_381108] using wordTrace_append hprefix tailTrace_381108
  have hstable : (prefixWord ++ tailWord_381108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381108).length < 2 ^ (prefixWord ++ tailWord_381108).sum := by decide
  have hdescent : baseEnd_381108 < baseStart_381108 := by decide
  rcases family_descends (prefixWord ++ tailWord_381108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381287 : List Nat := [1, 1, 5, 1, 3, 3, 2, 3]
def baseStart_381287 : Nat := 118140960795 + 381287 * 2 ^ 59
def prefixEnd_381287 : Nat := 4983230072969 + 3 ^ 40 * 381287 * 2
def baseEnd_381287 : Nat := 116019850850936264627555

theorem tailTrace_381287 : CollatzResearch.WordTrace tailWord_381287 prefixEnd_381287 116019850850936264627555 := by
  unfold tailWord_381287
  simp only [CollatzResearch.WordTrace]
  refine ⟨13906679369669792480350115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9271119579779861653566743 13906679369669792480350115)
  ·
    refine ⟨20860019054504688720525173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13906679369669792480350115 20860019054504688720525173)
    ·
      refine ⟨1955626786359814567549235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20860019054504688720525173 1955626786359814567549235)
      ·
        refine ⟨2933440179539721851323853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955626786359814567549235 2933440179539721851323853)
        ·
          refine ⟨1100040067327395694246445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2933440179539721851323853 1100040067327395694246445)
          ·
            refine ⟨412515025247773385342417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1100040067327395694246445 412515025247773385342417)
            ·
              refine ⟨309386268935830039006813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412515025247773385342417 309386268935830039006813)
              ·
                refine ⟨116019850850936264627555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309386268935830039006813 116019850850936264627555)
                ·
                  rfl

theorem cell19_381287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 3].length) (baseStart_381287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381287 prefixEnd_381287 := by exact prefixLift 381287
  have htrace : WordTrace (prefixWord ++ tailWord_381287) baseStart_381287 baseEnd_381287 := by
    simpa [prefixWord, tailWord_381287, baseEnd_381287] using wordTrace_append hprefix tailTrace_381287
  have hstable : (prefixWord ++ tailWord_381287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381287).length < 2 ^ (prefixWord ++ tailWord_381287).sum := by decide
  have hdescent : baseEnd_381287 < baseStart_381287 := by decide
  rcases family_descends (prefixWord ++ tailWord_381287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381348 : List Nat := [2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_381348 : Nat := 118140960795 + 381348 * 2 ^ 59
def prefixEnd_381348 : Nat := 4983230072969 + 3 ^ 40 * 381348 * 2
def baseEnd_381348 : Nat := 116038412225706197271833

theorem tailTrace_381348 : CollatzResearch.WordTrace tailWord_381348 prefixEnd_381348 116038412225706197271833 := by
  unfold tailWord_381348
  simp only [CollatzResearch.WordTrace]
  refine ⟨6954452111224399949160349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9272602814965866598880465 6954452111224399949160349)
  ·
    refine ⟨2607919541709149980935131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6954452111224399949160349 2607919541709149980935131)
    ·
      refine ⟨3911879312563724971402697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2607919541709149980935131 3911879312563724971402697)
      ·
        refine ⟨2933909484422793728552023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3911879312563724971402697 2933909484422793728552023)
        ·
          refine ⟨4400864226634190592828035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2933909484422793728552023 4400864226634190592828035)
          ·
            refine ⟨6601296339951285889242053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4400864226634190592828035 6601296339951285889242053)
            ·
              refine ⟨1237743063740866104232885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6601296339951285889242053 1237743063740866104232885)
              ·
                refine ⟨116038412225706197271833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1237743063740866104232885 116038412225706197271833)
                ·
                  rfl

theorem cell19_381348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_381348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381348 prefixEnd_381348 := by exact prefixLift 381348
  have htrace : WordTrace (prefixWord ++ tailWord_381348) baseStart_381348 baseEnd_381348 := by
    simpa [prefixWord, tailWord_381348, baseEnd_381348] using wordTrace_append hprefix tailTrace_381348
  have hstable : (prefixWord ++ tailWord_381348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381348).length < 2 ^ (prefixWord ++ tailWord_381348).sum := by decide
  have hdescent : baseEnd_381348 < baseStart_381348 := by decide
  rcases family_descends (prefixWord ++ tailWord_381348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381365 : List Nat := [1, 3, 3, 2, 4, 6]
def baseStart_381365 : Nat := 118140960795 + 381365 * 2 ^ 59
def prefixEnd_381365 : Nat := 4983230072969 + 3 ^ 40 * 381365 * 2
def baseEnd_381365 : Nat := 12893731674206132766001

theorem tailTrace_381365 : CollatzResearch.WordTrace tailWord_381365 prefixEnd_381365 12893731674206132766001 := by
  unfold tailWord_381365
  simp only [CollatzResearch.WordTrace]
  refine ⟨13909524263387211801689549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9273016175591474534459699 13909524263387211801689549)
  ·
    refine ⟨5216071598770204425633581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13909524263387211801689549 5216071598770204425633581)
    ·
      refine ⟨1956026849538826659612593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5216071598770204425633581 1956026849538826659612593)
      ·
        refine ⟨1467020137154119994709445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1956026849538826659612593 1467020137154119994709445)
        ·
          refine ⟨275066275716397499008021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1467020137154119994709445 275066275716397499008021)
          ·
            refine ⟨12893731674206132766001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 275066275716397499008021 12893731674206132766001)
            ·
              rfl

theorem cell19_381365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 6].length) (baseStart_381365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381365 prefixEnd_381365 := by exact prefixLift 381365
  have htrace : WordTrace (prefixWord ++ tailWord_381365) baseStart_381365 baseEnd_381365 := by
    simpa [prefixWord, tailWord_381365, baseEnd_381365] using wordTrace_append hprefix tailTrace_381365
  have hstable : (prefixWord ++ tailWord_381365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381365).length < 2 ^ (prefixWord ++ tailWord_381365).sum := by decide
  have hdescent : baseEnd_381365 < baseStart_381365 := by decide
  rcases family_descends (prefixWord ++ tailWord_381365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381380 : List Nat := [2, 3, 3, 2, 3, 1, 1, 4]
def baseStart_381380 : Nat := 118140960795 + 381380 * 2 ^ 59
def prefixEnd_381380 : Nat := 4983230072969 + 3 ^ 40 * 381380 * 2
def baseEnd_381380 : Nat := 116048149340339604560635

theorem tailTrace_381380 : CollatzResearch.WordTrace tailWord_381380 prefixEnd_381380 116048149340339604560635 := by
  unfold tailWord_381380
  simp only [CollatzResearch.WordTrace]
  refine ⟨6955035679166434681742797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9273380905555246242323729 6955035679166434681742797)
  ·
    refine ⟨2608138379687413005653549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6955035679166434681742797 2608138379687413005653549)
    ·
      refine ⟨978051892382779877120081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2608138379687413005653549 978051892382779877120081)
      ·
        refine ⟨733538919287084907840061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 978051892382779877120081 733538919287084907840061)
        ·
          refine ⟨275077094732656840440023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 733538919287084907840061 275077094732656840440023)
          ·
            refine ⟨412615642098985260660035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275077094732656840440023 412615642098985260660035)
            ·
              refine ⟨618923463148477890990053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412615642098985260660035 618923463148477890990053)
              ·
                refine ⟨116048149340339604560635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 618923463148477890990053 116048149340339604560635)
                ·
                  rfl

theorem cell19_381380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_381380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381380 prefixEnd_381380 := by exact prefixLift 381380
  have htrace : WordTrace (prefixWord ++ tailWord_381380) baseStart_381380 baseEnd_381380 := by
    simpa [prefixWord, tailWord_381380, baseEnd_381380] using wordTrace_append hprefix tailTrace_381380
  have hstable : (prefixWord ++ tailWord_381380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381380).length < 2 ^ (prefixWord ++ tailWord_381380).sum := by decide
  have hdescent : baseEnd_381380 < baseStart_381380 := by decide
  rcases family_descends (prefixWord ++ tailWord_381380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381384 : List Nat := [2, 1, 3, 1, 3, 4, 1, 4]
def baseStart_381384 : Nat := 118140960795 + 381384 * 2 ^ 59
def prefixEnd_381384 : Nat := 4983230072969 + 3 ^ 40 * 381384 * 2
def baseEnd_381384 : Nat := 116049366479668780471735

theorem tailTrace_381384 : CollatzResearch.WordTrace tailWord_381384 prefixEnd_381384 116049366479668780471735 := by
  unfold tailWord_381384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6955108625159189023315603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9273478166878918697754137 6955108625159189023315603)
  ·
    refine ⟨10432662937738783534973405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6955108625159189023315603 10432662937738783534973405)
    ·
      refine ⟨3912248601652043825615027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10432662937738783534973405 3912248601652043825615027)
      ·
        refine ⟨5868372902478065738422541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3912248601652043825615027 5868372902478065738422541)
        ·
          refine ⟨2200639838429274651908453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5868372902478065738422541 2200639838429274651908453)
          ·
            refine ⟨412619969705488997232835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2200639838429274651908453 412619969705488997232835)
            ·
              refine ⟨618929954558233495849253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412619969705488997232835 618929954558233495849253)
              ·
                refine ⟨116049366479668780471735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 618929954558233495849253 116049366479668780471735)
                ·
                  rfl

theorem cell19_381384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_381384 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381384 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381384 prefixEnd_381384 := by exact prefixLift 381384
  have htrace : WordTrace (prefixWord ++ tailWord_381384) baseStart_381384 baseEnd_381384 := by
    simpa [prefixWord, tailWord_381384, baseEnd_381384] using wordTrace_append hprefix tailTrace_381384
  have hstable : (prefixWord ++ tailWord_381384).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381384).length < 2 ^ (prefixWord ++ tailWord_381384).sum := by decide
  have hdescent : baseEnd_381384 < baseStart_381384 := by decide
  rcases family_descends (prefixWord ++ tailWord_381384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381500 : List Nat := [2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_381500 : Nat := 118140960795 + 381500 * 2 ^ 59
def prefixEnd_381500 : Nat := 4983230072969 + 3 ^ 40 * 381500 * 2
def baseEnd_381500 : Nat := 116084663520214881893641

theorem tailTrace_381500 : CollatzResearch.WordTrace tailWord_381500 prefixEnd_381500 116084663520214881893641 := by
  unfold tailWord_381500
  simp only [CollatzResearch.WordTrace]
  refine ⟨6957224058949064928926977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9276298745265419905235969 6957224058949064928926977)
  ·
    refine ⟨5217918044211798696695233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6957224058949064928926977 5217918044211798696695233)
    ·
      refine ⟨3913438533158849022521425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5217918044211798696695233 3913438533158849022521425)
      ·
        refine ⟨2935078899869136766891069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3913438533158849022521425 2935078899869136766891069)
        ·
          refine ⟨1100654587450926287584151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2935078899869136766891069 1100654587450926287584151)
          ·
            refine ⟨1650981881176389431376227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100654587450926287584151 1650981881176389431376227)
            ·
              refine ⟨2476472821764584147064341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650981881176389431376227 2476472821764584147064341)
              ·
                refine ⟨116084663520214881893641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2476472821764584147064341 116084663520214881893641)
                ·
                  rfl

theorem cell19_381500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_381500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381500 prefixEnd_381500 := by exact prefixLift 381500
  have htrace : WordTrace (prefixWord ++ tailWord_381500) baseStart_381500 baseEnd_381500 := by
    simpa [prefixWord, tailWord_381500, baseEnd_381500] using wordTrace_append hprefix tailTrace_381500
  have hstable : (prefixWord ++ tailWord_381500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381500).length < 2 ^ (prefixWord ++ tailWord_381500).sum := by decide
  have hdescent : baseEnd_381500 < baseStart_381500 := by decide
  rcases family_descends (prefixWord ++ tailWord_381500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381517 : List Nat := [1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_381517 : Nat := 118140960795 + 381517 * 2 ^ 59
def prefixEnd_381517 : Nat := 4983230072969 + 3 ^ 40 * 381517 * 2
def baseEnd_381517 : Nat := 116089836362363879515817

theorem tailTrace_381517 : CollatzResearch.WordTrace tailWord_381517 prefixEnd_381517 116089836362363879515817 := by
  unfold tailWord_381517
  simp only [CollatzResearch.WordTrace]
  refine ⟨13915068158836541761222805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9276712105891027840815203 13915068158836541761222805)
  ·
    refine ⟨652268819945462895057319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13915068158836541761222805 652268819945462895057319)
    ·
      refine ⟨978403229918194342585979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652268819945462895057319 978403229918194342585979)
      ·
        refine ⟨1467604844877291513878969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978403229918194342585979 1467604844877291513878969)
        ·
          refine ⟨1100703633657968635409227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1467604844877291513878969 1100703633657968635409227)
          ·
            refine ⟨1651055450486952953113841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100703633657968635409227 1651055450486952953113841)
            ·
              refine ⟨1238291587865214714835381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1651055450486952953113841 1238291587865214714835381)
              ·
                refine ⟨116089836362363879515817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1238291587865214714835381 116089836362363879515817)
                ·
                  rfl

theorem cell19_381517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_381517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381517 prefixEnd_381517 := by exact prefixLift 381517
  have htrace : WordTrace (prefixWord ++ tailWord_381517) baseStart_381517 baseEnd_381517 := by
    simpa [prefixWord, tailWord_381517, baseEnd_381517] using wordTrace_append hprefix tailTrace_381517
  have hstable : (prefixWord ++ tailWord_381517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381517).length < 2 ^ (prefixWord ++ tailWord_381517).sum := by decide
  have hdescent : baseEnd_381517 < baseStart_381517 := by decide
  rcases family_descends (prefixWord ++ tailWord_381517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381534 : List Nat := [4, 4, 1, 2, 8]
def baseStart_381534 : Nat := 118140960795 + 381534 * 2 ^ 59
def prefixEnd_381534 : Nat := 4983230072969 + 3 ^ 40 * 381534 * 2
def baseEnd_381534 : Nat := 4299815155722699153259

theorem tailTrace_381534 : CollatzResearch.WordTrace tailWord_381534 prefixEnd_381534 4299815155722699153259 := by
  unfold tailWord_381534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739461024971869208073957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9277125466516635776394437 1739461024971869208073957)
  ·
    refine ⟨326148942182225476513867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1739461024971869208073957 326148942182225476513867)
    ·
      refine ⟨489223413273338214770801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326148942182225476513867 489223413273338214770801)
      ·
        refine ⟨366917559955003661078101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489223413273338214770801 366917559955003661078101)
        ·
          refine ⟨4299815155722699153259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 366917559955003661078101 4299815155722699153259)
          ·
            rfl

theorem cell19_381534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 8].length) (baseStart_381534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381534 prefixEnd_381534 := by exact prefixLift 381534
  have htrace : WordTrace (prefixWord ++ tailWord_381534) baseStart_381534 baseEnd_381534 := by
    simpa [prefixWord, tailWord_381534, baseEnd_381534] using wordTrace_append hprefix tailTrace_381534
  have hstable : (prefixWord ++ tailWord_381534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381534).length < 2 ^ (prefixWord ++ tailWord_381534).sum := by decide
  have hdescent : baseEnd_381534 < baseStart_381534 := by decide
  rcases family_descends (prefixWord ++ tailWord_381534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381616 : List Nat := [2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_381616 : Nat := 118140960795 + 381616 * 2 ^ 59
def prefixEnd_381616 : Nat := 4983230072969 + 3 ^ 40 * 381616 * 2
def baseEnd_381616 : Nat := 116119960560760983315547

theorem tailTrace_381616 : CollatzResearch.WordTrace tailWord_381616 prefixEnd_381616 116119960560760983315547 := by
  unfold tailWord_381616
  simp only [CollatzResearch.WordTrace]
  refine ⟨6959339492738940834538351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9279119323651921112717801 6959339492738940834538351)
  ·
    refine ⟨10439009239108411251807527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6959339492738940834538351 10439009239108411251807527)
    ·
      refine ⟨15658513858662616877711291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10439009239108411251807527 15658513858662616877711291)
      ·
        refine ⟨23487770787993925316566937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15658513858662616877711291 23487770787993925316566937)
        ·
          refine ⟨17615828090995443987425203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23487770787993925316566937 17615828090995443987425203)
          ·
            refine ⟨26423742136493165981137805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17615828090995443987425203 26423742136493165981137805)
            ·
              refine ⟨9908903301184937242926677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26423742136493165981137805 9908903301184937242926677)
              ·
                refine ⟨116119960560760983315547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9908903301184937242926677 116119960560760983315547)
                ·
                  rfl

theorem cell19_381616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_381616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381616 prefixEnd_381616 := by exact prefixLift 381616
  have htrace : WordTrace (prefixWord ++ tailWord_381616) baseStart_381616 baseEnd_381616 := by
    simpa [prefixWord, tailWord_381616, baseEnd_381616] using wordTrace_append hprefix tailTrace_381616
  have hstable : (prefixWord ++ tailWord_381616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381616).length < 2 ^ (prefixWord ++ tailWord_381616).sum := by decide
  have hdescent : baseEnd_381616 < baseStart_381616 := by decide
  rcases family_descends (prefixWord ++ tailWord_381616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381631 : List Nat := [1, 1, 2, 2, 2, 6, 2, 3]
def baseStart_381631 : Nat := 118140960795 + 381631 * 2 ^ 59
def prefixEnd_381631 : Nat := 4983230072969 + 3 ^ 40 * 381631 * 2
def baseEnd_381631 : Nat := 116124524833245392982173

theorem tailTrace_381631 : CollatzResearch.WordTrace tailWord_381631 prefixEnd_381631 116124524833245392982173 := by
  unfold tailWord_381631
  simp only [CollatzResearch.WordTrace]
  refine ⟨13919226080423539230872747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9279484053615692820581831 13919226080423539230872747)
  ·
    refine ⟨20878839120635308846309121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13919226080423539230872747 20878839120635308846309121)
    ·
      refine ⟨15659129340476481634731841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20878839120635308846309121 15659129340476481634731841)
      ·
        refine ⟨11744347005357361226048881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15659129340476481634731841 11744347005357361226048881)
        ·
          refine ⟨8808260254018020919536661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11744347005357361226048881 8808260254018020919536661)
          ·
            refine ⟨412887199407094730603281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8808260254018020919536661 412887199407094730603281)
            ·
              refine ⟨309665399555321047952461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412887199407094730603281 309665399555321047952461)
              ·
                refine ⟨116124524833245392982173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309665399555321047952461 116124524833245392982173)
                ·
                  rfl

theorem cell19_381631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 3].length) (baseStart_381631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381631 prefixEnd_381631 := by exact prefixLift 381631
  have htrace : WordTrace (prefixWord ++ tailWord_381631) baseStart_381631 baseEnd_381631 := by
    simpa [prefixWord, tailWord_381631, baseEnd_381631] using wordTrace_append hprefix tailTrace_381631
  have hstable : (prefixWord ++ tailWord_381631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381631).length < 2 ^ (prefixWord ++ tailWord_381631).sum := by decide
  have hdescent : baseEnd_381631 < baseStart_381631 := by decide
  rcases family_descends (prefixWord ++ tailWord_381631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381650 : List Nat := [3, 2, 2, 2, 3, 2, 5]
def baseStart_381650 : Nat := 118140960795 + 381650 * 2 ^ 59
def prefixEnd_381650 : Nat := 4983230072969 + 3 ^ 40 * 381650 * 2
def baseEnd_381650 : Nat := 38710102081686326186633

theorem tailTrace_381650 : CollatzResearch.WordTrace tailWord_381650 prefixEnd_381650 38710102081686326186633 := by
  unfold tailWord_381650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479979766838676368953601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9279946044903136983876269 3479979766838676368953601)
  ·
    refine ⟨2609984825129007276715201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3479979766838676368953601 2609984825129007276715201)
    ·
      refine ⟨1957488618846755457536401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2609984825129007276715201 1957488618846755457536401)
      ·
        refine ⟨1468116464135066593152301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1957488618846755457536401 1468116464135066593152301)
        ·
          refine ⟨550543674050649972432113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1468116464135066593152301 550543674050649972432113)
          ·
            refine ⟨412907755537987479324085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550543674050649972432113 412907755537987479324085)
            ·
              refine ⟨38710102081686326186633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 412907755537987479324085 38710102081686326186633)
              ·
                rfl

theorem cell19_381650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_381650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381650 prefixEnd_381650 := by exact prefixLift 381650
  have htrace : WordTrace (prefixWord ++ tailWord_381650) baseStart_381650 baseEnd_381650 := by
    simpa [prefixWord, tailWord_381650, baseEnd_381650] using wordTrace_append hprefix tailTrace_381650
  have hstable : (prefixWord ++ tailWord_381650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381650).length < 2 ^ (prefixWord ++ tailWord_381650).sum := by decide
  have hdescent : baseEnd_381650 < baseStart_381650 := by decide
  rcases family_descends (prefixWord ++ tailWord_381650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381673 : List Nat := [1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_381673 : Nat := 118140960795 + 381673 * 2 ^ 59
def prefixEnd_381673 : Nat := 4983230072969 + 3 ^ 40 * 381673 * 2
def baseEnd_381673 : Nat := 116137304796201740048725

theorem tailTrace_381673 : CollatzResearch.WordTrace tailWord_381673 prefixEnd_381673 116137304796201740048725 := by
  unfold tailWord_381673
  simp only [CollatzResearch.WordTrace]
  refine ⟨13920757946271380403901673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9280505297514253602601115 13920757946271380403901673)
  ·
    refine ⟨10440568459703535302926255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13920757946271380403901673 10440568459703535302926255)
    ·
      refine ⟨15660852689555302954389383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10440568459703535302926255 15660852689555302954389383)
      ·
        refine ⟨23491279034332954431584075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15660852689555302954389383 23491279034332954431584075)
        ·
          refine ⟨35236918551499431647376113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23491279034332954431584075 35236918551499431647376113)
          ·
            refine ⟨26427688913624573735532085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35236918551499431647376113 26427688913624573735532085)
            ·
              refine ⟨2477595835652303787706133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26427688913624573735532085 2477595835652303787706133)
              ·
                refine ⟨116137304796201740048725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2477595835652303787706133 116137304796201740048725)
                ·
                  rfl

theorem cell19_381673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_381673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381673 prefixEnd_381673 := by exact prefixLift 381673
  have htrace : WordTrace (prefixWord ++ tailWord_381673) baseStart_381673 baseEnd_381673 := by
    simpa [prefixWord, tailWord_381673, baseEnd_381673] using wordTrace_append hprefix tailTrace_381673
  have hstable : (prefixWord ++ tailWord_381673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381673).length < 2 ^ (prefixWord ++ tailWord_381673).sum := by decide
  have hdescent : baseEnd_381673 < baseStart_381673 := by decide
  rcases family_descends (prefixWord ++ tailWord_381673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381728 : List Nat := [2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_381728 : Nat := 118140960795 + 381728 * 2 ^ 59
def prefixEnd_381728 : Nat := 4983230072969 + 3 ^ 40 * 381728 * 2
def baseEnd_381728 : Nat := 116154040461977908826353

theorem tailTrace_381728 : CollatzResearch.WordTrace tailWord_381728 prefixEnd_381728 116154040461977908826353 := by
  unfold tailWord_381728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6961381980536062398576919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9281842640714749864769225 6961381980536062398576919)
  ·
    refine ⟨10442072970804093597865379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6961381980536062398576919 10442072970804093597865379)
    ·
      refine ⟨15663109456206140396798069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10442072970804093597865379 15663109456206140396798069)
      ·
        refine ⟨1468416511519325662199819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15663109456206140396798069 1468416511519325662199819)
        ·
          refine ⟨2202624767278988493299729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468416511519325662199819 2202624767278988493299729)
          ·
            refine ⟨1651968575459241369974797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202624767278988493299729 1651968575459241369974797)
            ·
              refine ⟨619488215797215513740549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1651968575459241369974797 619488215797215513740549)
              ·
                refine ⟨116154040461977908826353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619488215797215513740549 116154040461977908826353)
                ·
                  rfl

theorem cell19_381728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_381728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381728 prefixEnd_381728 := by exact prefixLift 381728
  have htrace : WordTrace (prefixWord ++ tailWord_381728) baseStart_381728 baseEnd_381728 := by
    simpa [prefixWord, tailWord_381728, baseEnd_381728] using wordTrace_append hprefix tailTrace_381728
  have hstable : (prefixWord ++ tailWord_381728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381728).length < 2 ^ (prefixWord ++ tailWord_381728).sum := by decide
  have hdescent : baseEnd_381728 < baseStart_381728 := by decide
  rcases family_descends (prefixWord ++ tailWord_381728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381741 : List Nat := [1, 5, 3, 2, 1, 1, 3, 3]
def baseStart_381741 : Nat := 118140960795 + 381741 * 2 ^ 59
def prefixEnd_381741 : Nat := 4983230072969 + 3 ^ 40 * 381741 * 2
def baseEnd_381741 : Nat := 116157996164797730537429

theorem tailTrace_381741 : CollatzResearch.WordTrace tailWord_381741 prefixEnd_381741 116157996164797730537429 := by
  unfold tailWord_381741
  simp only [CollatzResearch.WordTrace]
  refine ⟨13923238110025028017377077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9282158740016685344918051 13923238110025028017377077)
  ·
    refine ⟨1305303572814846376629101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13923238110025028017377077 1305303572814846376629101)
    ·
      refine ⟨489488839805567391235913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1305303572814846376629101 489488839805567391235913)
      ·
        refine ⟨367116629854175543426935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489488839805567391235913 367116629854175543426935)
        ·
          refine ⟨550674944781263315140403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367116629854175543426935 550674944781263315140403)
          ·
            refine ⟨826012417171894972710605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550674944781263315140403 826012417171894972710605)
            ·
              refine ⟨309754656439460614766477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 826012417171894972710605 309754656439460614766477)
              ·
                refine ⟨116157996164797730537429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309754656439460614766477 116157996164797730537429)
                ·
                  rfl

theorem cell19_381741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 3].length) (baseStart_381741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381741 prefixEnd_381741 := by exact prefixLift 381741
  have htrace : WordTrace (prefixWord ++ tailWord_381741) baseStart_381741 baseEnd_381741 := by
    simpa [prefixWord, tailWord_381741, baseEnd_381741] using wordTrace_append hprefix tailTrace_381741
  have hstable : (prefixWord ++ tailWord_381741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381741).length < 2 ^ (prefixWord ++ tailWord_381741).sum := by decide
  have hdescent : baseEnd_381741 < baseStart_381741 := by decide
  rcases family_descends (prefixWord ++ tailWord_381741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381768 : List Nat := [2, 1, 3, 1, 1, 3, 8]
def baseStart_381768 : Nat := 118140960795 + 381768 * 2 ^ 59
def prefixEnd_381768 : Nat := 4983230072969 + 3 ^ 40 * 381768 * 2
def baseEnd_381768 : Nat := 38722070618423222645785

theorem tailTrace_381768 : CollatzResearch.WordTrace tailWord_381768 prefixEnd_381768 38722070618423222645785 := by
  unfold tailWord_381768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6962111440463605814304979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9282815253951474419073305 6962111440463605814304979)
  ·
    refine ⟨10443167160695408721457469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6962111440463605814304979 10443167160695408721457469)
    ·
      refine ⟨3916187685260778270546551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10443167160695408721457469 3916187685260778270546551)
      ·
        refine ⟨5874281527891167405819827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3916187685260778270546551 5874281527891167405819827)
        ·
          refine ⟨8811422291836751108729741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5874281527891167405819827 8811422291836751108729741)
          ·
            refine ⟨3304283359438781665773653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8811422291836751108729741 3304283359438781665773653)
            ·
              refine ⟨38722070618423222645785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3304283359438781665773653 38722070618423222645785)
              ·
                rfl

theorem cell19_381768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_381768 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381768 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381768 prefixEnd_381768 := by exact prefixLift 381768
  have htrace : WordTrace (prefixWord ++ tailWord_381768) baseStart_381768 baseEnd_381768 := by
    simpa [prefixWord, tailWord_381768, baseEnd_381768] using wordTrace_append hprefix tailTrace_381768
  have hstable : (prefixWord ++ tailWord_381768).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381768).length < 2 ^ (prefixWord ++ tailWord_381768).sum := by decide
  have hdescent : baseEnd_381768 < baseStart_381768 := by decide
  rcases family_descends (prefixWord ++ tailWord_381768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381899 : List Nat := [1, 1, 1, 1, 3, 7, 1, 4]
def baseStart_381899 : Nat := 118140960795 + 381899 * 2 ^ 59
def prefixEnd_381899 : Nat := 4983230072969 + 3 ^ 40 * 381899 * 2
def baseEnd_381899 : Nat := 116206073168300179025887

theorem tailTrace_381899 : CollatzResearch.WordTrace tailWord_381899 prefixEnd_381899 116206073168300179025887 := by
  unfold tailWord_381899
  simp only [CollatzResearch.WordTrace]
  refine ⟨13929000843452621001628751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9286000562301747334419167 13929000843452621001628751)
  ·
    refine ⟨20893501265178931502443127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13929000843452621001628751 20893501265178931502443127)
    ·
      refine ⟨31340251897768397253664691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20893501265178931502443127 31340251897768397253664691)
      ·
        refine ⟨47010377846652595880497037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31340251897768397253664691 47010377846652595880497037)
        ·
          refine ⟨17628891692494723455186389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47010377846652595880497037 17628891692494723455186389)
          ·
            refine ⟨413177149042845080980931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17628891692494723455186389 413177149042845080980931)
            ·
              refine ⟨619765723564267621471397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413177149042845080980931 619765723564267621471397)
              ·
                refine ⟨116206073168300179025887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619765723564267621471397 116206073168300179025887)
                ·
                  rfl

theorem cell19_381899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_381899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381899 prefixEnd_381899 := by exact prefixLift 381899
  have htrace : WordTrace (prefixWord ++ tailWord_381899) baseStart_381899 baseEnd_381899 := by
    simpa [prefixWord, tailWord_381899, baseEnd_381899] using wordTrace_append hprefix tailTrace_381899
  have hstable : (prefixWord ++ tailWord_381899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381899).length < 2 ^ (prefixWord ++ tailWord_381899).sum := by decide
  have hdescent : baseEnd_381899 < baseStart_381899 := by decide
  rcases family_descends (prefixWord ++ tailWord_381899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381973 : List Nat := [1, 3, 2, 1, 4, 3, 2, 3]
def baseStart_381973 : Nat := 118140960795 + 381973 * 2 ^ 59
def prefixEnd_381973 : Nat := 4983230072969 + 3 ^ 40 * 381973 * 2
def baseEnd_381973 : Nat := 116228590245889933381241

theorem tailTrace_381973 : CollatzResearch.WordTrace tailWord_381973 prefixEnd_381973 116228590245889933381241 := by
  unfold tailWord_381973
  simp only [CollatzResearch.WordTrace]
  refine ⟨13931699845184531639822573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9287799896789687759881715 13931699845184531639822573)
  ·
    refine ⟨5224387441944199364933465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13931699845184531639822573 5224387441944199364933465)
    ·
      refine ⟨3918290581458149523700099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5224387441944199364933465 3918290581458149523700099)
      ·
        refine ⟨5877435872187224285550149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918290581458149523700099 5877435872187224285550149)
        ·
          refine ⟨1102019226035104553540653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5877435872187224285550149 1102019226035104553540653)
          ·
            refine ⟨413257209763164207577745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1102019226035104553540653 413257209763164207577745)
            ·
              refine ⟨309942907322373155683309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413257209763164207577745 309942907322373155683309)
              ·
                refine ⟨116228590245889933381241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309942907322373155683309 116228590245889933381241)
                ·
                  rfl

theorem cell19_381973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 3].length) (baseStart_381973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381973 prefixEnd_381973 := by exact prefixLift 381973
  have htrace : WordTrace (prefixWord ++ tailWord_381973) baseStart_381973 baseEnd_381973 := by
    simpa [prefixWord, tailWord_381973, baseEnd_381973] using wordTrace_append hprefix tailTrace_381973
  have hstable : (prefixWord ++ tailWord_381973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381973).length < 2 ^ (prefixWord ++ tailWord_381973).sum := by decide
  have hdescent : baseEnd_381973 < baseStart_381973 := by decide
  rcases family_descends (prefixWord ++ tailWord_381973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
