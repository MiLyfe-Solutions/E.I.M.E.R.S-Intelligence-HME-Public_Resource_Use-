import V185TrunkScan23Chunk0454

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2692324 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_2692324 : Nat := 118140960795 + 2692324 * 2 ^ 59
def prefixEnd_2692324 : Nat := 4983230072969 + 3 ^ 40 * 2692324 * 2
def baseEnd_2692324 : Nat := 1382456289635629503668233

theorem tailTrace_2692324 : CollatzResearch.WordTrace tailWord_2692324 prefixEnd_2692324 1382456289635629503668233 := by
  unfold tailWord_2692324
  simp only [CollatzResearch.WordTrace]
  refine ⟨49098561749088717588390013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65464748998784956784520017 49098561749088717588390013)
  ·
    refine ⟨18411960655908269095646255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49098561749088717588390013 18411960655908269095646255)
    ·
      refine ⟨27617940983862403643469383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18411960655908269095646255 27617940983862403643469383)
      ·
        refine ⟨41426911475793605465204075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27617940983862403643469383 41426911475793605465204075)
        ·
          refine ⟨62140367213690408197806113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41426911475793605465204075 62140367213690408197806113)
          ·
            refine ⟨46605275410267806148354585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62140367213690408197806113 46605275410267806148354585)
            ·
              refine ⟨34953956557700854611265939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46605275410267806148354585 34953956557700854611265939)
              ·
                refine ⟨52430934836551281916898909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34953956557700854611265939 52430934836551281916898909)
                ·
                  refine ⟨19661600563706730718837091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52430934836551281916898909 19661600563706730718837091)
                  ·
                    refine ⟨29492400845560096078255637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19661600563706730718837091 29492400845560096078255637)
                    ·
                      refine ⟨1382456289635629503668233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29492400845560096078255637 1382456289635629503668233)
                      ·
                        rfl

theorem cell23_2692324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_2692324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692324 prefixEnd_2692324 := by exact prefixLift 2692324
  have htrace : WordTrace (prefixWord ++ tailWord_2692324) baseStart_2692324 baseEnd_2692324 := by
    simpa [prefixWord, tailWord_2692324, baseEnd_2692324] using wordTrace_append hprefix tailTrace_2692324
  have hstable : (prefixWord ++ tailWord_2692324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692324).length < 2 ^ (prefixWord ++ tailWord_2692324).sum := by decide
  have hdescent : baseEnd_2692324 < baseStart_2692324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692331 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 3]
def baseStart_2692331 : Nat := 118140960795 + 2692331 * 2 ^ 59
def prefixEnd_2692331 : Nat := 4983230072969 + 3 ^ 40 * 2692331 * 2
def baseEnd_2692331 : Nat := 1382459884000210976280701

theorem tailTrace_2692331 : CollatzResearch.WordTrace tailWord_2692331 prefixEnd_2692331 1382459884000210976280701 := by
  unfold tailWord_2692331
  simp only [CollatzResearch.WordTrace]
  refine ⟨98197378809152075372284847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65464919206101383581523231 98197378809152075372284847)
  ·
    refine ⟨147296068213728113058427271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98197378809152075372284847 147296068213728113058427271)
    ·
      refine ⟨220944102320592169587640907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147296068213728113058427271 220944102320592169587640907)
      ·
        refine ⟨331416153480888254381461361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220944102320592169587640907 331416153480888254381461361)
        ·
          refine ⟨248562115110666190786096021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331416153480888254381461361 248562115110666190786096021)
          ·
            refine ⟨11651349145812477693098251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 248562115110666190786096021 11651349145812477693098251)
            ·
              refine ⟨17477023718718716539647377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11651349145812477693098251 17477023718718716539647377)
              ·
                refine ⟨13107767789039037404735533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17477023718718716539647377 13107767789039037404735533)
                ·
                  refine ⟨4915412920889639026775825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13107767789039037404735533 4915412920889639026775825)
                  ·
                    refine ⟨3686559690667229270081869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4915412920889639026775825 3686559690667229270081869)
                    ·
                      refine ⟨1382459884000210976280701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3686559690667229270081869 1382459884000210976280701)
                      ·
                        rfl

theorem cell23_2692331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 3].length) (baseStart_2692331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692331 prefixEnd_2692331 := by exact prefixLift 2692331
  have htrace : WordTrace (prefixWord ++ tailWord_2692331) baseStart_2692331 baseEnd_2692331 := by
    simpa [prefixWord, tailWord_2692331, baseEnd_2692331] using wordTrace_append hprefix tailTrace_2692331
  have hstable : (prefixWord ++ tailWord_2692331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692331).length < 2 ^ (prefixWord ++ tailWord_2692331).sum := by decide
  have hdescent : baseEnd_2692331 < baseStart_2692331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692338 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_2692338 : Nat := 118140960795 + 2692338 * 2 ^ 59
def prefixEnd_2692338 : Nat := 4983230072969 + 3 ^ 40 * 2692338 * 2
def baseEnd_2692338 : Nat := 460821159454930816297723

theorem tailTrace_2692338 : CollatzResearch.WordTrace tailWord_2692338 prefixEnd_2692338 460821159454930816297723 := by
  unfold tailWord_2692338
  simp only [CollatzResearch.WordTrace]
  refine ⟨24549408530031678891947417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65465089413417810378526445 24549408530031678891947417)
  ·
    refine ⟨18412056397523759168960563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24549408530031678891947417 18412056397523759168960563)
    ·
      refine ⟨27618084596285638753440845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18412056397523759168960563 27618084596285638753440845)
      ·
        refine ⟨10356781723607114532540317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27618084596285638753440845 10356781723607114532540317)
        ·
          refine ⟨3883793146352667949702619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10356781723607114532540317 3883793146352667949702619)
          ·
            refine ⟨5825689719529001924553929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883793146352667949702619 5825689719529001924553929)
            ·
              refine ⟨4369267289646751443415447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5825689719529001924553929 4369267289646751443415447)
              ·
                refine ⟨6553900934470127165123171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4369267289646751443415447 6553900934470127165123171)
                ·
                  refine ⟨9830851401705190747684757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6553900934470127165123171 9830851401705190747684757)
                  ·
                    refine ⟨460821159454930816297723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9830851401705190747684757 460821159454930816297723)
                    ·
                      rfl

theorem cell23_2692338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_2692338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692338 prefixEnd_2692338 := by exact prefixLift 2692338
  have htrace : WordTrace (prefixWord ++ tailWord_2692338) baseStart_2692338 baseEnd_2692338 := by
    simpa [prefixWord, tailWord_2692338, baseEnd_2692338] using wordTrace_append hprefix tailTrace_2692338
  have hstable : (prefixWord ++ tailWord_2692338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692338).length < 2 ^ (prefixWord ++ tailWord_2692338).sum := by decide
  have hdescent : baseEnd_2692338 < baseStart_2692338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692351 : List Nat := [1, 1, 2, 2, 1, 6, 3, 7]
def baseStart_2692351 : Nat := 118140960795 + 2692351 * 2 ^ 59
def prefixEnd_2692351 : Nat := 4983230072969 + 3 ^ 40 * 2692351 * 2
def baseEnd_2692351 : Nat := 51202598281974107334467

theorem tailTrace_2692351 : CollatzResearch.WordTrace tailWord_2692351 prefixEnd_2692351 51202598281974107334467 := by
  unfold tailWord_2692351
  simp only [CollatzResearch.WordTrace]
  refine ⟨98198108269079618788012907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65465405512719745858675271 98198108269079618788012907)
  ·
    refine ⟨147297162403619428182019361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98198108269079618788012907 147297162403619428182019361)
    ·
      refine ⟨110472871802714571136514521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147297162403619428182019361 110472871802714571136514521)
      ·
        refine ⟨82854653852035928352385891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110472871802714571136514521 82854653852035928352385891)
        ·
          refine ⟨124281980778053892528578837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82854653852035928352385891 124281980778053892528578837)
          ·
            refine ⟨5825717848971276212277133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124281980778053892528578837 5825717848971276212277133)
            ·
              refine ⟨2184644193364228579603925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5825717848971276212277133 2184644193364228579603925)
              ·
                refine ⟨51202598281974107334467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2184644193364228579603925 51202598281974107334467)
                ·
                  rfl

theorem cell23_2692351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 7].length) (baseStart_2692351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692351 prefixEnd_2692351 := by exact prefixLift 2692351
  have htrace : WordTrace (prefixWord ++ tailWord_2692351) baseStart_2692351 baseEnd_2692351 := by
    simpa [prefixWord, tailWord_2692351, baseEnd_2692351] using wordTrace_append hprefix tailTrace_2692351
  have hstable : (prefixWord ++ tailWord_2692351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692351).length < 2 ^ (prefixWord ++ tailWord_2692351).sum := by decide
  have hdescent : baseEnd_2692351 < baseStart_2692351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692361 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 1, 3, 3]
def baseStart_2692361 : Nat := 118140960795 + 2692361 * 2 ^ 59
def prefixEnd_2692361 : Nat := 4983230072969 + 3 ^ 40 * 2692361 * 2
def baseEnd_2692361 : Nat := 1382475288419845858905563

theorem tailTrace_2692361 : CollatzResearch.WordTrace tailWord_2692361 prefixEnd_2692361 1382475288419845858905563 := by
  unfold tailWord_2692361
  simp only [CollatzResearch.WordTrace]
  refine ⟨98198472999043390495876937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65465648666028926997251291 98198472999043390495876937)
  ·
    refine ⟨73648854749282542871907703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98198472999043390495876937 73648854749282542871907703)
    ·
      refine ⟨110473282123923814307861555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73648854749282542871907703 110473282123923814307861555)
      ·
        refine ⟨165709923185885721461792333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110473282123923814307861555 165709923185885721461792333)
        ·
          refine ⟨62141221194707145548172125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165709923185885721461792333 62141221194707145548172125)
          ·
            refine ⟨23302957948015179580564547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62141221194707145548172125 23302957948015179580564547)
            ·
              refine ⟨34954436922022769370846821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23302957948015179580564547 34954436922022769370846821)
              ·
                refine ⟨6553956922879269257033779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34954436922022769370846821 6553956922879269257033779)
                ·
                  refine ⟨9830935384318903885550669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6553956922879269257033779 9830935384318903885550669)
                  ·
                    refine ⟨3686600769119588957081501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9830935384318903885550669 3686600769119588957081501)
                    ·
                      refine ⟨1382475288419845858905563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3686600769119588957081501 1382475288419845858905563)
                      ·
                        rfl

theorem cell23_2692361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3, 3].length) (baseStart_2692361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692361 prefixEnd_2692361 := by exact prefixLift 2692361
  have htrace : WordTrace (prefixWord ++ tailWord_2692361) baseStart_2692361 baseEnd_2692361 := by
    simpa [prefixWord, tailWord_2692361, baseEnd_2692361] using wordTrace_append hprefix tailTrace_2692361
  have hstable : (prefixWord ++ tailWord_2692361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692361).length < 2 ^ (prefixWord ++ tailWord_2692361).sum := by decide
  have hdescent : baseEnd_2692361 < baseStart_2692361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692405 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_2692405 : Nat := 118140960795 + 2692405 * 2 ^ 59
def prefixEnd_2692405 : Nat := 4983230072969 + 3 ^ 40 * 2692405 * 2
def baseEnd_2692405 : Nat := 1382497881568643686755361

theorem tailTrace_2692405 : CollatzResearch.WordTrace tailWord_2692405 prefixEnd_2692405 1382497881568643686755361 := by
  unfold tailWord_2692405
  simp only [CollatzResearch.WordTrace]
  refine ⟨98200077810883986010478669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65466718540589324006985779 98200077810883986010478669)
  ·
    refine ⟨36825029179081494753929501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98200077810883986010478669 36825029179081494753929501)
    ·
      refine ⟨13809385942155560532723563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36825029179081494753929501 13809385942155560532723563)
      ·
        refine ⟨20714078913233340799085345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13809385942155560532723563 20714078913233340799085345)
        ·
          refine ⟨15535559184925005599314009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20714078913233340799085345 15535559184925005599314009)
          ·
            refine ⟨11651669388693754199485507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15535559184925005599314009 11651669388693754199485507)
            ·
              refine ⟨17477504083040631299228261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11651669388693754199485507 17477504083040631299228261)
              ·
                refine ⟨3277032015570118368605299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17477504083040631299228261 3277032015570118368605299)
                ·
                  refine ⟨4915548023355177552907949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277032015570118368605299 4915548023355177552907949)
                  ·
                    refine ⟨1843330508758191582340481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4915548023355177552907949 1843330508758191582340481)
                    ·
                      refine ⟨1382497881568643686755361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843330508758191582340481 1382497881568643686755361)
                      ·
                        rfl

theorem cell23_2692405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_2692405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692405 prefixEnd_2692405 := by exact prefixLift 2692405
  have htrace : WordTrace (prefixWord ++ tailWord_2692405) baseStart_2692405 baseEnd_2692405 := by
    simpa [prefixWord, tailWord_2692405, baseEnd_2692405] using wordTrace_append hprefix tailTrace_2692405
  have hstable : (prefixWord ++ tailWord_2692405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692405).length < 2 ^ (prefixWord ++ tailWord_2692405).sum := by decide
  have hdescent : baseEnd_2692405 < baseStart_2692405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692413 : List Nat := [1, 4, 1, 5, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2692413 : Nat := 118140960795 + 2692413 * 2 ^ 59
def prefixEnd_2692413 : Nat := 4983230072969 + 3 ^ 40 * 2692413 * 2
def baseEnd_2692413 : Nat := 1382501989413879655455325

theorem tailTrace_2692413 : CollatzResearch.WordTrace tailWord_2692413 prefixEnd_2692413 1382501989413879655455325 := by
  unfold tailWord_2692413
  simp only [CollatzResearch.WordTrace]
  refine ⟨98200369594855003376769893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65466913063236668917846595 98200369594855003376769893)
  ·
    refine ⟨18412569299035313133144355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98200369594855003376769893 18412569299035313133144355)
    ·
      refine ⟨27618853948552969699716533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18412569299035313133144355 27618853948552969699716533)
      ·
        refine ⟨2589267557676840909348425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27618853948552969699716533 2589267557676840909348425)
        ·
          refine ⟨1941950668257630682011319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2589267557676840909348425 1941950668257630682011319)
          ·
            refine ⟨2912926002386446023016979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941950668257630682011319 2912926002386446023016979)
            ·
              refine ⟨4369389003579669034525469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2912926002386446023016979 4369389003579669034525469)
              ·
                refine ⟨1638520876342375887947051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4369389003579669034525469 1638520876342375887947051)
                ·
                  refine ⟨2457781314513563831920577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638520876342375887947051 2457781314513563831920577)
                  ·
                    refine ⟨1843335985885172873940433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2457781314513563831920577 1843335985885172873940433)
                    ·
                      refine ⟨1382501989413879655455325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843335985885172873940433 1382501989413879655455325)
                      ·
                        rfl

theorem cell23_2692413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2692413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692413 prefixEnd_2692413 := by exact prefixLift 2692413
  have htrace : WordTrace (prefixWord ++ tailWord_2692413) baseStart_2692413 baseEnd_2692413 := by
    simpa [prefixWord, tailWord_2692413, baseEnd_2692413] using wordTrace_append hprefix tailTrace_2692413
  have hstable : (prefixWord ++ tailWord_2692413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692413).length < 2 ^ (prefixWord ++ tailWord_2692413).sum := by decide
  have hdescent : baseEnd_2692413 < baseStart_2692413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692435 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 2, 2, 2]
def baseStart_2692435 : Nat := 118140960795 + 2692435 * 2 ^ 59
def prefixEnd_2692435 : Nat := 4983230072969 + 3 ^ 40 * 2692435 * 2
def baseEnd_2692435 : Nat := 1382513285988278569380223

theorem tailTrace_2692435 : CollatzResearch.WordTrace tailWord_2692435 prefixEnd_2692435 1382513285988278569380223 := by
  unfold tailWord_2692435
  simp only [CollatzResearch.WordTrace]
  refine ⟨98201172000775301134070759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65467448000516867422713839 98201172000775301134070759)
  ·
    refine ⟨147301758001162951701106139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98201172000775301134070759 147301758001162951701106139)
    ·
      refine ⟨220952637001744427551659209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147301758001162951701106139 220952637001744427551659209)
      ·
        refine ⟨165714477751308320663744407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220952637001744427551659209 165714477751308320663744407)
        ·
          refine ⟨248571716626962480995616611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165714477751308320663744407 248571716626962480995616611)
          ·
            refine ⟨372857574940443721493424917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248571716626962480995616611 372857574940443721493424917)
            ·
              refine ⟨17477698825333299445004293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 372857574940443721493424917 17477698825333299445004293)
              ·
                refine ⟨3277068529749993645938305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17477698825333299445004293 3277068529749993645938305)
                ·
                  refine ⟨2457801397312495234453729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3277068529749993645938305 2457801397312495234453729)
                  ·
                    refine ⟨1843351047984371425840297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2457801397312495234453729 1843351047984371425840297)
                    ·
                      refine ⟨1382513285988278569380223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843351047984371425840297 1382513285988278569380223)
                      ·
                        rfl

theorem cell23_2692435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 2, 2].length) (baseStart_2692435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692435 prefixEnd_2692435 := by exact prefixLift 2692435
  have htrace : WordTrace (prefixWord ++ tailWord_2692435) baseStart_2692435 baseEnd_2692435 := by
    simpa [prefixWord, tailWord_2692435, baseEnd_2692435] using wordTrace_append hprefix tailTrace_2692435
  have hstable : (prefixWord ++ tailWord_2692435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692435).length < 2 ^ (prefixWord ++ tailWord_2692435).sum := by decide
  have hdescent : baseEnd_2692435 < baseStart_2692435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692441 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 7]
def baseStart_2692441 : Nat := 118140960795 + 2692441 * 2 ^ 59
def prefixEnd_2692441 : Nat := 4983230072969 + 3 ^ 40 * 2692441 * 2
def baseEnd_2692441 : Nat := 153612929652467282878355

theorem tailTrace_2692441 : CollatzResearch.WordTrace tailWord_2692441 prefixEnd_2692441 153612929652467282878355 := by
  unfold tailWord_2692441
  simp only [CollatzResearch.WordTrace]
  refine ⟨98201390838753564158789177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65467593892502376105859451 98201390838753564158789177)
  ·
    refine ⟨73651043129065173119091883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98201390838753564158789177 73651043129065173119091883)
    ·
      refine ⟨110476564693597759678637825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73651043129065173119091883 110476564693597759678637825)
      ·
        refine ⟨82857423520198319758978369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110476564693597759678637825 82857423520198319758978369)
        ·
          refine ⟨62143067640148739819233777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82857423520198319758978369 62143067640148739819233777)
          ·
            refine ⟨46607300730111554864425333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62143067640148739819233777 46607300730111554864425333)
            ·
              refine ⟨4369434443447958268539875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46607300730111554864425333 4369434443447958268539875)
              ·
                refine ⟨6554151665171937402809813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4369434443447958268539875 6554151665171937402809813)
                ·
                  refine ⟨153612929652467282878355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6554151665171937402809813 153612929652467282878355)
                  ·
                    rfl

theorem cell23_2692441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 7].length) (baseStart_2692441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692441 prefixEnd_2692441 := by exact prefixLift 2692441
  have htrace : WordTrace (prefixWord ++ tailWord_2692441) baseStart_2692441 baseEnd_2692441 := by
    simpa [prefixWord, tailWord_2692441, baseEnd_2692441] using wordTrace_append hprefix tailTrace_2692441
  have hstable : (prefixWord ++ tailWord_2692441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692441).length < 2 ^ (prefixWord ++ tailWord_2692441).sum := by decide
  have hdescent : baseEnd_2692441 < baseStart_2692441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692452 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 2, 2, 2]
def baseStart_2692452 : Nat := 118140960795 + 2692452 * 2 ^ 59
def prefixEnd_2692452 : Nat := 4983230072969 + 3 ^ 40 * 2692452 * 2
def baseEnd_2692452 : Nat := 1382522015159405002867645

theorem tailTrace_2692452 : CollatzResearch.WordTrace tailWord_2692452 prefixEnd_2692452 1382522015159405002867645 := by
  unfold tailWord_2692452
  simp only [CollatzResearch.WordTrace]
  refine ⟨49100896020856856518719805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65467861361142475358293073 49100896020856856518719805)
  ·
    refine ⟨18412836007821321194519927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49100896020856856518719805 18412836007821321194519927)
    ·
      refine ⟨27619254011731981791779891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18412836007821321194519927 27619254011731981791779891)
      ·
        refine ⟨41428881017597972687669837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27619254011731981791779891 41428881017597972687669837)
        ·
          refine ⟨15535830381599239757876189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41428881017597972687669837 15535830381599239757876189)
          ·
            refine ⟨5825936393099714909203571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15535830381599239757876189 5825936393099714909203571)
            ·
              refine ⟨8738904589649572363805357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825936393099714909203571 8738904589649572363805357)
              ·
                refine ⟨3277089221118589636427009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8738904589649572363805357 3277089221118589636427009)
                ·
                  refine ⟨2457816915838942227320257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3277089221118589636427009 2457816915838942227320257)
                  ·
                    refine ⟨1843362686879206670490193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2457816915838942227320257 1843362686879206670490193)
                    ·
                      refine ⟨1382522015159405002867645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843362686879206670490193 1382522015159405002867645)
                      ·
                        rfl

theorem cell23_2692452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_2692452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692452 prefixEnd_2692452 := by exact prefixLift 2692452
  have htrace : WordTrace (prefixWord ++ tailWord_2692452) baseStart_2692452 baseEnd_2692452 := by
    simpa [prefixWord, tailWord_2692452, baseEnd_2692452] using wordTrace_append hprefix tailTrace_2692452
  have hstable : (prefixWord ++ tailWord_2692452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692452).length < 2 ^ (prefixWord ++ tailWord_2692452).sum := by decide
  have hdescent : baseEnd_2692452 < baseStart_2692452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692488 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 2, 5]
def baseStart_2692488 : Nat := 118140960795 + 2692488 * 2 ^ 59
def prefixEnd_2692488 : Nat := 4983230072969 + 3 ^ 40 * 2692488 * 2
def baseEnd_2692488 : Nat := 460846833487655620672493

theorem tailTrace_2692488 : CollatzResearch.WordTrace tailWord_2692488 prefixEnd_2692488 460846833487655620672493 := by
  unfold tailWord_2692488
  simp only [CollatzResearch.WordTrace]
  refine ⟨49101552534791645592875059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65468736713055527457166745 49101552534791645592875059)
  ·
    refine ⟨73652328802187468389312589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49101552534791645592875059 73652328802187468389312589)
    ·
      refine ⟨27619623300820300645992221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73652328802187468389312589 27619623300820300645992221)
      ·
        refine ⟨10357358737807612742247083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27619623300820300645992221 10357358737807612742247083)
        ·
          refine ⟨15536038106711419113370625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10357358737807612742247083 15536038106711419113370625)
          ·
            refine ⟨11652028580033564335027969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15536038106711419113370625 11652028580033564335027969)
            ·
              refine ⟨8739021435025173251270977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11652028580033564335027969 8739021435025173251270977)
              ·
                refine ⟨6554266076268879938453233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8739021435025173251270977 6554266076268879938453233)
                ·
                  refine ⟨4915699557201659953839925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6554266076268879938453233 4915699557201659953839925)
                  ·
                    refine ⟨460846833487655620672493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4915699557201659953839925 460846833487655620672493)
                    ·
                      rfl

theorem cell23_2692488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_2692488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692488 prefixEnd_2692488 := by exact prefixLift 2692488
  have htrace : WordTrace (prefixWord ++ tailWord_2692488) baseStart_2692488 baseEnd_2692488 := by
    simpa [prefixWord, tailWord_2692488, baseEnd_2692488] using wordTrace_append hprefix tailTrace_2692488
  have hstable : (prefixWord ++ tailWord_2692488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692488).length < 2 ^ (prefixWord ++ tailWord_2692488).sum := by decide
  have hdescent : baseEnd_2692488 < baseStart_2692488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692525 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2692525 : Nat := 118140960795 + 2692525 * 2 ^ 59
def prefixEnd_2692525 : Nat := 4983230072969 + 3 ^ 40 * 2692525 * 2
def baseEnd_2692525 : Nat := 1382559499247183217254809

theorem tailTrace_2692525 : CollatzResearch.WordTrace tailWord_2692525 prefixEnd_2692525 1382559499247183217254809 := by
  unfold tailWord_2692525
  simp only [CollatzResearch.WordTrace]
  refine ⟨98204454570449246504847029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65469636380299497669898019 98204454570449246504847029)
  ·
    refine ⟨9206667615979616859829409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98204454570449246504847029 9206667615979616859829409)
    ·
      refine ⟨6905000711984712644872057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9206667615979616859829409 6905000711984712644872057)
      ·
        refine ⟨5178750533988534483654043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6905000711984712644872057 5178750533988534483654043)
        ·
          refine ⟨7768125800982801725481065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5178750533988534483654043 7768125800982801725481065)
          ·
            refine ⟨5826094350737101294110799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7768125800982801725481065 5826094350737101294110799)
            ·
              refine ⟨8739141526105651941166199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826094350737101294110799 8739141526105651941166199)
              ·
                refine ⟨13108712289158477911749299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8739141526105651941166199 13108712289158477911749299)
                ·
                  refine ⟨19663068433737716867623949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13108712289158477911749299 19663068433737716867623949)
                  ·
                    refine ⟨7373650662651643825358981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19663068433737716867623949 7373650662651643825358981)
                    ·
                      refine ⟨1382559499247183217254809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7373650662651643825358981 1382559499247183217254809)
                      ·
                        rfl

theorem cell23_2692525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2692525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692525 prefixEnd_2692525 := by exact prefixLift 2692525
  have htrace : WordTrace (prefixWord ++ tailWord_2692525) baseStart_2692525 baseEnd_2692525 := by
    simpa [prefixWord, tailWord_2692525, baseEnd_2692525] using wordTrace_append hprefix tailTrace_2692525
  have hstable : (prefixWord ++ tailWord_2692525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692525).length < 2 ^ (prefixWord ++ tailWord_2692525).sum := by decide
  have hdescent : baseEnd_2692525 < baseStart_2692525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692528 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 3]
def baseStart_2692528 : Nat := 118140960795 + 2692528 * 2 ^ 59
def prefixEnd_2692528 : Nat := 4983230072969 + 3 ^ 40 * 2692528 * 2
def baseEnd_2692528 : Nat := 1382561039689146705517295

theorem tailTrace_2692528 : CollatzResearch.WordTrace tailWord_2692528 prefixEnd_2692528 1382561039689146705517295 := by
  unfold tailWord_2692528
  simp only [CollatzResearch.WordTrace]
  refine ⟨49102281994719189008603119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65469709326292252011470825 49102281994719189008603119)
  ·
    refine ⟨73653422992078783512904679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49102281994719189008603119 73653422992078783512904679)
    ·
      refine ⟨110480134488118175269357019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73653422992078783512904679 110480134488118175269357019)
      ·
        refine ⟨165720201732177262904035529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110480134488118175269357019 165720201732177262904035529)
        ·
          refine ⟨124290151299132947178026647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165720201732177262904035529 124290151299132947178026647)
          ·
            refine ⟨186435226948699420767039971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124290151299132947178026647 186435226948699420767039971)
            ·
              refine ⟨279652840423049131150559957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186435226948699420767039971 279652840423049131150559957)
              ·
                refine ⟨6554363447415214011341249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 279652840423049131150559957 6554363447415214011341249)
                ·
                  refine ⟨4915772585561410508505937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6554363447415214011341249 4915772585561410508505937)
                  ·
                    refine ⟨3686829439171057881379453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4915772585561410508505937 3686829439171057881379453)
                    ·
                      refine ⟨1382561039689146705517295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3686829439171057881379453 1382561039689146705517295)
                      ·
                        rfl

theorem cell23_2692528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 3].length) (baseStart_2692528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692528 prefixEnd_2692528 := by exact prefixLift 2692528
  have htrace : WordTrace (prefixWord ++ tailWord_2692528) baseStart_2692528 baseEnd_2692528 := by
    simpa [prefixWord, tailWord_2692528, baseEnd_2692528] using wordTrace_append hprefix tailTrace_2692528
  have hstable : (prefixWord ++ tailWord_2692528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692528).length < 2 ^ (prefixWord ++ tailWord_2692528).sum := by decide
  have hdescent : baseEnd_2692528 < baseStart_2692528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692551 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_2692551 : Nat := 118140960795 + 2692551 * 2 ^ 59
def prefixEnd_2692551 : Nat := 4983230072969 + 3 ^ 40 * 2692551 * 2
def baseEnd_2692551 : Nat := 1382572849744200115529689

theorem tailTrace_2692551 : CollatzResearch.WordTrace tailWord_2692551 prefixEnd_2692551 1382572849744200115529689 := by
  unfold tailWord_2692551
  simp only [CollatzResearch.WordTrace]
  refine ⟨98205402868355052945293507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65470268578903368630195671 98205402868355052945293507)
  ·
    refine ⟨147308104302532579417940261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98205402868355052945293507 147308104302532579417940261)
    ·
      refine ⟨27620269556724858640863799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147308104302532579417940261 27620269556724858640863799)
      ·
        refine ⟨41430404335087287961295699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27620269556724858640863799 41430404335087287961295699)
        ·
          refine ⟨62145606502630931941943549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41430404335087287961295699 62145606502630931941943549)
          ·
            refine ⟨23304602438486599478228831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62145606502630931941943549 23304602438486599478228831)
            ·
              refine ⟨34956903657729899217343247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23304602438486599478228831 34956903657729899217343247)
              ·
                refine ⟨52435355486594848826014871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34956903657729899217343247 52435355486594848826014871)
                ·
                  refine ⟨78653033229892273239022307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52435355486594848826014871 78653033229892273239022307)
                  ·
                    refine ⟨117979549844838409858533461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78653033229892273239022307 117979549844838409858533461)
                    ·
                      refine ⟨1382572849744200115529689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 117979549844838409858533461 1382572849744200115529689)
                      ·
                        rfl

theorem cell23_2692551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_2692551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692551 prefixEnd_2692551 := by exact prefixLift 2692551
  have htrace : WordTrace (prefixWord ++ tailWord_2692551) baseStart_2692551 baseEnd_2692551 := by
    simpa [prefixWord, tailWord_2692551, baseEnd_2692551] using wordTrace_append hprefix tailTrace_2692551
  have hstable : (prefixWord ++ tailWord_2692551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692551).length < 2 ^ (prefixWord ++ tailWord_2692551).sum := by decide
  have hdescent : baseEnd_2692551 < baseStart_2692551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692565 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 6]
def baseStart_2692565 : Nat := 118140960795 + 2692565 * 2 ^ 59
def prefixEnd_2692565 : Nat := 4983230072969 + 3 ^ 40 * 2692565 * 2
def baseEnd_2692565 : Nat := 153620004274818117861625

theorem tailTrace_2692565 : CollatzResearch.WordTrace tailWord_2692565 prefixEnd_2692565 153620004274818117861625 := by
  unfold tailWord_2692565
  simp only [CollatzResearch.WordTrace]
  refine ⟨98205913490304333336303149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65470608993536222224202099 98205913490304333336303149)
  ·
    refine ⟨36827217558864125001113681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98205913490304333336303149 36827217558864125001113681)
    ·
      refine ⟨27620413169148093750835261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36827217558864125001113681 27620413169148093750835261)
      ·
        refine ⟨10357654938430535156563223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27620413169148093750835261 10357654938430535156563223)
        ·
          refine ⟨15536482407645802734844835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10357654938430535156563223 15536482407645802734844835)
          ·
            refine ⟨23304723611468704102267253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15536482407645802734844835 23304723611468704102267253)
            ·
              refine ⟨2184817838575191009587555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23304723611468704102267253 2184817838575191009587555)
              ·
                refine ⟨3277226757862786514381333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184817838575191009587555 3277226757862786514381333)
                ·
                  refine ⟨153620004274818117861625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3277226757862786514381333 153620004274818117861625)
                  ·
                    rfl

theorem cell23_2692565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_2692565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692565 prefixEnd_2692565 := by exact prefixLift 2692565
  have htrace : WordTrace (prefixWord ++ tailWord_2692565) baseStart_2692565 baseEnd_2692565 := by
    simpa [prefixWord, tailWord_2692565, baseEnd_2692565] using wordTrace_append hprefix tailTrace_2692565
  have hstable : (prefixWord ++ tailWord_2692565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692565).length < 2 ^ (prefixWord ++ tailWord_2692565).sum := by decide
  have hdescent : baseEnd_2692565 < baseStart_2692565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692575 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 3, 1, 3]
def baseStart_2692575 : Nat := 118140960795 + 2692575 * 2 ^ 59
def prefixEnd_2692575 : Nat := 4983230072969 + 3 ^ 40 * 2692575 * 2
def baseEnd_2692575 : Nat := 1382585173279908021629579

theorem tailTrace_2692575 : CollatzResearch.WordTrace tailWord_2692575 prefixEnd_2692575 1382585173279908021629579 := by
  unfold tailWord_2692575
  simp only [CollatzResearch.WordTrace]
  refine ⟨98206278220268105044167179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65470852146845403362778119 98206278220268105044167179)
  ·
    refine ⟨147309417330402157566250769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98206278220268105044167179 147309417330402157566250769)
    ·
      refine ⟨110482062997801618174688077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147309417330402157566250769 110482062997801618174688077)
      ·
        refine ⟨41430773624175606815508029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110482062997801618174688077 41430773624175606815508029)
        ·
          refine ⟨15536540109065852555815511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41430773624175606815508029 15536540109065852555815511)
          ·
            refine ⟨23304810163598778833723267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15536540109065852555815511 23304810163598778833723267)
            ·
              refine ⟨34957215245398168250584901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23304810163598778833723267 34957215245398168250584901)
              ·
                refine ⟨6554477858512156546984669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34957215245398168250584901 6554477858512156546984669)
                ·
                  refine ⟨2457929196942058705119251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6554477858512156546984669 2457929196942058705119251)
                  ·
                    refine ⟨3686893795413088057678877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2457929196942058705119251 3686893795413088057678877)
                    ·
                      refine ⟨1382585173279908021629579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3686893795413088057678877 1382585173279908021629579)
                      ·
                        rfl

theorem cell23_2692575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_2692575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692575 prefixEnd_2692575 := by exact prefixLift 2692575
  have htrace : WordTrace (prefixWord ++ tailWord_2692575) baseStart_2692575 baseEnd_2692575 := by
    simpa [prefixWord, tailWord_2692575, baseEnd_2692575] using wordTrace_append hprefix tailTrace_2692575
  have hstable : (prefixWord ++ tailWord_2692575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692575).length < 2 ^ (prefixWord ++ tailWord_2692575).sum := by decide
  have hdescent : baseEnd_2692575 < baseStart_2692575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692586 : List Nat := [3, 1, 3, 1, 5, 1, 1, 3, 1, 4]
def baseStart_2692586 : Nat := 118140960795 + 2692586 * 2 ^ 59
def prefixEnd_2692586 : Nat := 4983230072969 + 3 ^ 40 * 2692586 * 2
def baseEnd_2692586 : Nat := 460863607189035826197343

theorem tailTrace_2692586 : CollatzResearch.WordTrace tailWord_2692586 prefixEnd_2692586 460863607189035826197343 := by
  unfold tailWord_2692586
  simp only [CollatzResearch.WordTrace]
  refine ⟨24551669855807063480704403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65471119615485502615211741 24551669855807063480704403)
  ·
    refine ⟨36827504783710595221056605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24551669855807063480704403 36827504783710595221056605)
    ·
      refine ⟨13810314293891473207896227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36827504783710595221056605 13810314293891473207896227)
      ·
        refine ⟨20715471440837209811844341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13810314293891473207896227 20715471440837209811844341)
        ·
          refine ⟨1942075447578488419860407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20715471440837209811844341 1942075447578488419860407)
          ·
            refine ⟨2913113171367732629790611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942075447578488419860407 2913113171367732629790611)
            ·
              refine ⟨4369669757051598944685917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913113171367732629790611 4369669757051598944685917)
              ·
                refine ⟨1638626158894349604257219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4369669757051598944685917 1638626158894349604257219)
                ·
                  refine ⟨2457939238341524406385829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638626158894349604257219 2457939238341524406385829)
                  ·
                    refine ⟨460863607189035826197343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2457939238341524406385829 460863607189035826197343)
                    ·
                      rfl

theorem cell23_2692586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_2692586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692586 prefixEnd_2692586 := by exact prefixLift 2692586
  have htrace : WordTrace (prefixWord ++ tailWord_2692586) baseStart_2692586 baseEnd_2692586 := by
    simpa [prefixWord, tailWord_2692586, baseEnd_2692586] using wordTrace_append hprefix tailTrace_2692586
  have hstable : (prefixWord ++ tailWord_2692586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692586).length < 2 ^ (prefixWord ++ tailWord_2692586).sum := by decide
  have hdescent : baseEnd_2692586 < baseStart_2692586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692609 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_2692609 : Nat := 118140960795 + 2692609 * 2 ^ 59
def prefixEnd_2692609 : Nat := 4983230072969 + 3 ^ 40 * 2692609 * 2
def baseEnd_2692609 : Nat := 1382602631622160888604423

theorem tailTrace_2692609 : CollatzResearch.WordTrace tailWord_2692609 prefixEnd_2692609 1382602631622160888604423 := by
  unfold tailWord_2692609
  simp only [CollatzResearch.WordTrace]
  refine ⟨98207518302144928850904881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65471678868096619233936587 98207518302144928850904881)
  ·
    refine ⟨73655638726608696638178661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98207518302144928850904881 73655638726608696638178661)
    ·
      refine ⟨13810432261239130619658499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73655638726608696638178661 13810432261239130619658499)
      ·
        refine ⟨20715648391858695929487749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13810432261239130619658499 20715648391858695929487749)
        ·
          refine ⟨3884184073473505486778953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20715648391858695929487749 3884184073473505486778953)
          ·
            refine ⟨2913138055105129115084215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3884184073473505486778953 2913138055105129115084215)
            ·
              refine ⟨4369707082657693672626323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913138055105129115084215 4369707082657693672626323)
              ·
                refine ⟨6554560623986540508939485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4369707082657693672626323 6554560623986540508939485)
                ·
                  refine ⟨2457960233994952690852307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6554560623986540508939485 2457960233994952690852307)
                  ·
                    refine ⟨3686940350992429036278461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2457960233994952690852307 3686940350992429036278461)
                    ·
                      refine ⟨1382602631622160888604423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3686940350992429036278461 1382602631622160888604423)
                      ·
                        rfl

theorem cell23_2692609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_2692609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692609 prefixEnd_2692609 := by exact prefixLift 2692609
  have htrace : WordTrace (prefixWord ++ tailWord_2692609) baseStart_2692609 baseEnd_2692609 := by
    simpa [prefixWord, tailWord_2692609, baseEnd_2692609] using wordTrace_append hprefix tailTrace_2692609
  have hstable : (prefixWord ++ tailWord_2692609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692609).length < 2 ^ (prefixWord ++ tailWord_2692609).sum := by decide
  have hdescent : baseEnd_2692609 < baseStart_2692609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692625 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 2, 4]
def baseStart_2692625 : Nat := 118140960795 + 2692625 * 2 ^ 59
def prefixEnd_2692625 : Nat := 4983230072969 + 3 ^ 40 * 2692625 * 2
def baseEnd_2692625 : Nat := 460870282437544275334783

theorem tailTrace_2692625 : CollatzResearch.WordTrace tailWord_2692625 prefixEnd_2692625 460870282437544275334783 := by
  unfold tailWord_2692625
  simp only [CollatzResearch.WordTrace]
  refine ⟨98208101870086963583487329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65472067913391309055658219 98208101870086963583487329)
  ·
    refine ⟨73656076402565222687615497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98208101870086963583487329 73656076402565222687615497)
    ·
      refine ⟨55242057301923917015711623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73656076402565222687615497 55242057301923917015711623)
      ·
        refine ⟨82863085952885875523567435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55242057301923917015711623 82863085952885875523567435)
        ·
          refine ⟨124294628929328813285351153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82863085952885875523567435 124294628929328813285351153)
          ·
            refine ⟨93220971696996609964013365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124294628929328813285351153 93220971696996609964013365)
            ·
              refine ⟨8739466096593432184126253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93220971696996609964013365 8739466096593432184126253)
              ·
                refine ⟨3277299786222537069047345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8739466096593432184126253 3277299786222537069047345)
                ·
                  refine ⟨2457974839666902801785509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3277299786222537069047345 2457974839666902801785509)
                  ·
                    refine ⟨460870282437544275334783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2457974839666902801785509 460870282437544275334783)
                    ·
                      rfl

theorem cell23_2692625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_2692625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692625 prefixEnd_2692625 := by exact prefixLift 2692625
  have htrace : WordTrace (prefixWord ++ tailWord_2692625) baseStart_2692625 baseEnd_2692625 := by
    simpa [prefixWord, tailWord_2692625, baseEnd_2692625] using wordTrace_append hprefix tailTrace_2692625
  have hstable : (prefixWord ++ tailWord_2692625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692625).length < 2 ^ (prefixWord ++ tailWord_2692625).sum := by decide
  have hdescent : baseEnd_2692625 < baseStart_2692625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692682 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_2692682 : Nat := 118140960795 + 2692682 * 2 ^ 59
def prefixEnd_2692682 : Nat := 4983230072969 + 3 ^ 40 * 2692682 * 2
def baseEnd_2692682 : Nat := 1382640115709939102991587

theorem tailTrace_2692682 : CollatzResearch.WordTrace tailWord_2692682 prefixEnd_2692682 1382640115709939102991587 := by
  unfold tailWord_2692682
  simp only [CollatzResearch.WordTrace]
  refine ⟨24552545207720115579578075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65473453887253641545541533 24552545207720115579578075)
  ·
    refine ⟨36828817811580173369367113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24552545207720115579578075 36828817811580173369367113)
    ·
      refine ⟨27621613358685130027025335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36828817811580173369367113 27621613358685130027025335)
      ·
        refine ⟨41432420038027695040538003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27621613358685130027025335 41432420038027695040538003)
        ·
          refine ⟨62148630057041542560807005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41432420038027695040538003 62148630057041542560807005)
          ·
            refine ⟨23305736271390578460302627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62148630057041542560807005 23305736271390578460302627)
            ·
              refine ⟨34958604407085867690453941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23305736271390578460302627 34958604407085867690453941)
              ·
                refine ⟨3277369163164300095980057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34958604407085867690453941 3277369163164300095980057)
                ·
                  refine ⟨2458026872373225071985043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3277369163164300095980057 2458026872373225071985043)
                  ·
                    refine ⟨3687040308559837607977565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2458026872373225071985043 3687040308559837607977565)
                    ·
                      refine ⟨1382640115709939102991587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3687040308559837607977565 1382640115709939102991587)
                      ·
                        rfl

theorem cell23_2692682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_2692682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692682 prefixEnd_2692682 := by exact prefixLift 2692682
  have htrace : WordTrace (prefixWord ++ tailWord_2692682) baseStart_2692682 baseEnd_2692682 := by
    simpa [prefixWord, tailWord_2692682, baseEnd_2692682] using wordTrace_append hprefix tailTrace_2692682
  have hstable : (prefixWord ++ tailWord_2692682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692682).length < 2 ^ (prefixWord ++ tailWord_2692682).sum := by decide
  have hdescent : baseEnd_2692682 < baseStart_2692682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692688 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_2692688 : Nat := 118140960795 + 2692688 * 2 ^ 59
def prefixEnd_2692688 : Nat := 4983230072969 + 3 ^ 40 * 2692688 * 2
def baseEnd_2692688 : Nat := 1382643196593866079516559

theorem tailTrace_2692688 : CollatzResearch.WordTrace tailWord_2692688 prefixEnd_2692688 1382643196593866079516559 := by
  unfold tailWord_2692688
  simp only [CollatzResearch.WordTrace]
  refine ⟨49105199834429362671515359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65473599779239150228687145 49105199834429362671515359)
  ·
    refine ⟨73657799751644044007273039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49105199834429362671515359 73657799751644044007273039)
    ·
      refine ⟨110486699627466066010909559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73657799751644044007273039 110486699627466066010909559)
      ·
        refine ⟨165730049441199099016364339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110486699627466066010909559 165730049441199099016364339)
        ·
          refine ⟨248595074161798648524546509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165730049441199099016364339 248595074161798648524546509)
          ·
            refine ⟨93223152810674493196704941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248595074161798648524546509 93223152810674493196704941)
            ·
              refine ⟨34958682304002934948764353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93223152810674493196704941 34958682304002934948764353)
              ·
                refine ⟨26219011728002201211573265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34958682304002934948764353 26219011728002201211573265)
                ·
                  refine ⟨19664258796001650908679949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26219011728002201211573265 19664258796001650908679949)
                  ·
                    refine ⟨7374097048500619090754981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19664258796001650908679949 7374097048500619090754981)
                    ·
                      refine ⟨1382643196593866079516559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7374097048500619090754981 1382643196593866079516559)
                      ·
                        rfl

theorem cell23_2692688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_2692688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692688 prefixEnd_2692688 := by exact prefixLift 2692688
  have htrace : WordTrace (prefixWord ++ tailWord_2692688) baseStart_2692688 baseEnd_2692688 := by
    simpa [prefixWord, tailWord_2692688, baseEnd_2692688] using wordTrace_append hprefix tailTrace_2692688
  have hstable : (prefixWord ++ tailWord_2692688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692688).length < 2 ^ (prefixWord ++ tailWord_2692688).sum := by decide
  have hdescent : baseEnd_2692688 < baseStart_2692688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692692 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_2692692 : Nat := 118140960795 + 2692692 * 2 ^ 59
def prefixEnd_2692692 : Nat := 4983230072969 + 3 ^ 40 * 2692692 * 2
def baseEnd_2692692 : Nat := 1382645250516484063866541

theorem tailTrace_2692692 : CollatzResearch.WordTrace tailWord_2692692 prefixEnd_2692692 1382645250516484063866541 := by
  unfold tailWord_2692692
  simp only [CollatzResearch.WordTrace]
  refine ⟨49105272780422117013088165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65473697040562822684117553 49105272780422117013088165)
  ·
    refine ⟨9207238646329146939954031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49105272780422117013088165 9207238646329146939954031)
    ·
      refine ⟨13810857969493720409931047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9207238646329146939954031 13810857969493720409931047)
      ·
        refine ⟨20716286954240580614896571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13810857969493720409931047 20716286954240580614896571)
        ·
          refine ⟨31074430431360870922344857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20716286954240580614896571 31074430431360870922344857)
          ·
            refine ⟨23305822823520653191758643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31074430431360870922344857 23305822823520653191758643)
            ·
              refine ⟨34958734235280979787637965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23305822823520653191758643 34958734235280979787637965)
              ·
                refine ⟨13109525338230367420364237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34958734235280979787637965 13109525338230367420364237)
                ·
                  refine ⟨4916072001836387782636589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13109525338230367420364237 4916072001836387782636589)
                  ·
                    refine ⟨1843527000688645418488721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4916072001836387782636589 1843527000688645418488721)
                    ·
                      refine ⟨1382645250516484063866541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843527000688645418488721 1382645250516484063866541)
                      ·
                        rfl

theorem cell23_2692692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_2692692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692692 prefixEnd_2692692 := by exact prefixLift 2692692
  have htrace : WordTrace (prefixWord ++ tailWord_2692692) baseStart_2692692 baseEnd_2692692 := by
    simpa [prefixWord, tailWord_2692692, baseEnd_2692692] using wordTrace_append hprefix tailTrace_2692692
  have hstable : (prefixWord ++ tailWord_2692692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692692).length < 2 ^ (prefixWord ++ tailWord_2692692).sum := by decide
  have hdescent : baseEnd_2692692 < baseStart_2692692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692709 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 1, 3, 2]
def baseStart_2692709 : Nat := 118140960795 + 2692709 * 2 ^ 59
def prefixEnd_2692709 : Nat := 4983230072969 + 3 ^ 40 * 2692709 * 2
def baseEnd_2692709 : Nat := 1382653979687610497353963

theorem tailTrace_2692709 : CollatzResearch.WordTrace tailWord_2692709 prefixEnd_2692709 1382653979687610497353963 := by
  unfold tailWord_2692709
  simp only [CollatzResearch.WordTrace]
  refine ⟨98211165601782645929545181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65474110401188430619696787 98211165601782645929545181)
  ·
    refine ⟨36829187100668492223579443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98211165601782645929545181 36829187100668492223579443)
    ·
      refine ⟨55243780651002738335369165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36829187100668492223579443 55243780651002738335369165)
      ·
        refine ⟨20716417744126026875763437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55243780651002738335369165 20716417744126026875763437)
        ·
          refine ⟨7768656654047260078411289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20716417744126026875763437 7768656654047260078411289)
          ·
            refine ⟨5826492490535445058808467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7768656654047260078411289 5826492490535445058808467)
            ·
              refine ⟨8739738735803167588212701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826492490535445058808467 8739738735803167588212701)
              ·
                refine ⟨3277402025926187845579763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8739738735803167588212701 3277402025926187845579763)
                ·
                  refine ⟨4916103038889281768369645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277402025926187845579763 4916103038889281768369645)
                  ·
                    refine ⟨1843538639583480663138617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4916103038889281768369645 1843538639583480663138617)
                    ·
                      refine ⟨1382653979687610497353963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843538639583480663138617 1382653979687610497353963)
                      ·
                        rfl

theorem cell23_2692709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_2692709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692709 prefixEnd_2692709 := by exact prefixLift 2692709
  have htrace : WordTrace (prefixWord ++ tailWord_2692709) baseStart_2692709 baseEnd_2692709 := by
    simpa [prefixWord, tailWord_2692709, baseEnd_2692709] using wordTrace_append hprefix tailTrace_2692709
  have hstable : (prefixWord ++ tailWord_2692709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692709).length < 2 ^ (prefixWord ++ tailWord_2692709).sum := by decide
  have hdescent : baseEnd_2692709 < baseStart_2692709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692790 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_2692790 : Nat := 118140960795 + 2692790 * 2 ^ 59
def prefixEnd_2692790 : Nat := 4983230072969 + 3 ^ 40 * 2692790 * 2
def baseEnd_2692790 : Nat := 1382695571620624680441091

theorem tailTrace_2692790 : CollatzResearch.WordTrace tailWord_2692790 prefixEnd_2692790 1382695571620624680441091 := by
  unfold tailWord_2692790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6138382494655574797702739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65476079942992797842162549 6138382494655574797702739)
  ·
    refine ⟨9207573741983362196554109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6138382494655574797702739 9207573741983362196554109)
    ·
      refine ⟨3452840153243760823707791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9207573741983362196554109 3452840153243760823707791)
      ·
        refine ⟨5179260229865641235561687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3452840153243760823707791 5179260229865641235561687)
        ·
          refine ⟨7768890344798461853342531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5179260229865641235561687 7768890344798461853342531)
          ·
            refine ⟨11653335517197692780013797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7768890344798461853342531 11653335517197692780013797)
            ·
              refine ⟨2185000409474567396252587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11653335517197692780013797 2185000409474567396252587)
              ·
                refine ⟨3277500614211851094378881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185000409474567396252587 3277500614211851094378881)
                ·
                  refine ⟨2458125460658888320784161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3277500614211851094378881 2458125460658888320784161)
                  ·
                    refine ⟨1843594095494166240588121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2458125460658888320784161 1843594095494166240588121)
                    ·
                      refine ⟨1382695571620624680441091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843594095494166240588121 1382695571620624680441091)
                      ·
                        rfl

theorem cell23_2692790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_2692790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692790 prefixEnd_2692790 := by exact prefixLift 2692790
  have htrace : WordTrace (prefixWord ++ tailWord_2692790) baseStart_2692790 baseEnd_2692790 := by
    simpa [prefixWord, tailWord_2692790, baseEnd_2692790] using wordTrace_append hprefix tailTrace_2692790
  have hstable : (prefixWord ++ tailWord_2692790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692790).length < 2 ^ (prefixWord ++ tailWord_2692790).sum := by decide
  have hdescent : baseEnd_2692790 < baseStart_2692790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692815 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 3]
def baseStart_2692815 : Nat := 118140960795 + 2692815 * 2 ^ 59
def prefixEnd_2692815 : Nat := 4983230072969 + 3 ^ 40 * 2692815 * 2
def baseEnd_2692815 : Nat := 1382708408636987082628475

theorem tailTrace_2692815 : CollatzResearch.WordTrace tailWord_2692815 prefixEnd_2692815 1382708408636987082628475 := by
  unfold tailWord_2692815
  simp only [CollatzResearch.WordTrace]
  refine ⟨98215031739398626032903899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65476687826265750688602599 98215031739398626032903899)
  ·
    refine ⟨147322547609097939049355849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98215031739398626032903899 147322547609097939049355849)
    ·
      refine ⟨110491910706823454287016887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147322547609097939049355849 110491910706823454287016887)
      ·
        refine ⟨165737866060235181430525331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110491910706823454287016887 165737866060235181430525331)
        ·
          refine ⟨248606799090352772145787997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165737866060235181430525331 248606799090352772145787997)
          ·
            refine ⟨93227549658882289554670499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248606799090352772145787997 93227549658882289554670499)
            ·
              refine ⟨139841324488323434332005749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93227549658882289554670499 139841324488323434332005749)
              ·
                refine ⟨13110124170780321968625539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139841324488323434332005749 13110124170780321968625539)
                ·
                  refine ⟨19665186256170482952938309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13110124170780321968625539 19665186256170482952938309)
                  ·
                    refine ⟨3687222423031965553675933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19665186256170482952938309 3687222423031965553675933)
                    ·
                      refine ⟨1382708408636987082628475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3687222423031965553675933 1382708408636987082628475)
                      ·
                        rfl

theorem cell23_2692815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 3].length) (baseStart_2692815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692815 prefixEnd_2692815 := by exact prefixLift 2692815
  have htrace : WordTrace (prefixWord ++ tailWord_2692815) baseStart_2692815 baseEnd_2692815 := by
    simpa [prefixWord, tailWord_2692815, baseEnd_2692815] using wordTrace_append hprefix tailTrace_2692815
  have hstable : (prefixWord ++ tailWord_2692815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692815).length < 2 ^ (prefixWord ++ tailWord_2692815).sum := by decide
  have hdescent : baseEnd_2692815 < baseStart_2692815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692832 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 3]
def baseStart_2692832 : Nat := 118140960795 + 2692832 * 2 ^ 59
def prefixEnd_2692832 : Nat := 4983230072969 + 3 ^ 40 * 2692832 * 2
def baseEnd_2692832 : Nat := 1382717137808113516115897

theorem tailTrace_2692832 : CollatzResearch.WordTrace tailWord_2692832 prefixEnd_2692832 1382717137808113516115897 := by
  unfold tailWord_2692832
  simp only [CollatzResearch.WordTrace]
  refine ⟨49107825890168518968136375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65477101186891358624181833 49107825890168518968136375)
  ·
    refine ⟨73661738835252778452204563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49107825890168518968136375 73661738835252778452204563)
    ·
      refine ⟨110492608252879167678306845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73661738835252778452204563 110492608252879167678306845)
      ·
        refine ⟨41434728094829687879365067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110492608252879167678306845 41434728094829687879365067)
        ·
          refine ⟨62152092142244531819047601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41434728094829687879365067 62152092142244531819047601)
          ·
            refine ⟨46614069106683398864285701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62152092142244531819047601 46614069106683398864285701)
            ·
              refine ⟨8740137957503137287053569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46614069106683398864285701 8740137957503137287053569)
              ·
                refine ⟨6555103468127352965290177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8740137957503137287053569 6555103468127352965290177)
                ·
                  refine ⟨4916327601095514723967633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6555103468127352965290177 4916327601095514723967633)
                  ·
                    refine ⟨3687245700821636042975725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916327601095514723967633 3687245700821636042975725)
                    ·
                      refine ⟨1382717137808113516115897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3687245700821636042975725 1382717137808113516115897)
                      ·
                        rfl

theorem cell23_2692832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_2692832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692832 prefixEnd_2692832 := by exact prefixLift 2692832
  have htrace : WordTrace (prefixWord ++ tailWord_2692832) baseStart_2692832 baseEnd_2692832 := by
    simpa [prefixWord, tailWord_2692832, baseEnd_2692832] using wordTrace_append hprefix tailTrace_2692832
  have hstable : (prefixWord ++ tailWord_2692832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692832).length < 2 ^ (prefixWord ++ tailWord_2692832).sum := by decide
  have hdescent : baseEnd_2692832 < baseStart_2692832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692896 : List Nat := [2, 1, 1, 5, 1, 1, 1, 6, 1, 1, 3]
def baseStart_2692896 : Nat := 118140960795 + 2692896 * 2 ^ 59
def prefixEnd_2692896 : Nat := 4983230072969 + 3 ^ 40 * 2692896 * 2
def baseEnd_2692896 : Nat := 1382750000570001265715603

theorem tailTrace_2692896 : CollatzResearch.WordTrace tailWord_2692896 prefixEnd_2692896 1382750000570001265715603 := by
  unfold tailWord_2692896
  simp only [CollatzResearch.WordTrace]
  refine ⟨49108993026052588433301271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65478657368070117911068361 49108993026052588433301271)
  ·
    refine ⟨73663489539078882649951907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49108993026052588433301271 73663489539078882649951907)
    ·
      refine ⟨110495234308618323974927861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73663489539078882649951907 110495234308618323974927861)
      ·
        refine ⟨10358928216432967872649487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110495234308618323974927861 10358928216432967872649487)
        ·
          refine ⟨15538392324649451808974231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10358928216432967872649487 15538392324649451808974231)
          ·
            refine ⟨23307588486974177713461347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15538392324649451808974231 23307588486974177713461347)
            ·
              refine ⟨34961382730461266570192021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23307588486974177713461347 34961382730461266570192021)
              ·
                refine ⟨1638814815490371870477751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34961382730461266570192021 1638814815490371870477751)
                ·
                  refine ⟨2458222223235557805716627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638814815490371870477751 2458222223235557805716627)
                  ·
                    refine ⟨3687333334853336708574941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2458222223235557805716627 3687333334853336708574941)
                    ·
                      refine ⟨1382750000570001265715603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3687333334853336708574941 1382750000570001265715603)
                      ·
                        rfl

theorem cell23_2692896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_2692896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692896 prefixEnd_2692896 := by exact prefixLift 2692896
  have htrace : WordTrace (prefixWord ++ tailWord_2692896) baseStart_2692896 baseEnd_2692896 := by
    simpa [prefixWord, tailWord_2692896, baseEnd_2692896] using wordTrace_append hprefix tailTrace_2692896
  have hstable : (prefixWord ++ tailWord_2692896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692896).length < 2 ^ (prefixWord ++ tailWord_2692896).sum := by decide
  have hdescent : baseEnd_2692896 < baseStart_2692896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692916 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2692916 : Nat := 118140960795 + 2692916 * 2 ^ 59
def prefixEnd_2692916 : Nat := 4983230072969 + 3 ^ 40 * 2692916 * 2
def baseEnd_2692916 : Nat := 460920090061030395821837

theorem tailTrace_2692916 : CollatzResearch.WordTrace tailWord_2692916 prefixEnd_2692916 460920090061030395821837 := by
  unfold tailWord_2692916
  simp only [CollatzResearch.WordTrace]
  refine ⟨49109357756016360141165301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65479143674688480188220401 49109357756016360141165301)
  ·
    refine ⟨4604002289626533763234247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49109357756016360141165301 4604002289626533763234247)
    ·
      refine ⟨6906003434439800644851371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4604002289626533763234247 6906003434439800644851371)
      ·
        refine ⟨10359005151659700967277057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6906003434439800644851371 10359005151659700967277057)
        ·
          refine ⟨7769253863744775725457793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10359005151659700967277057 7769253863744775725457793)
          ·
            refine ⟨5826940397808581794093345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7769253863744775725457793 5826940397808581794093345)
            ·
              refine ⟨4370205298356436345570009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5826940397808581794093345 4370205298356436345570009)
              ·
                refine ⟨3277653973767327259177507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4370205298356436345570009 3277653973767327259177507)
                ·
                  refine ⟨4916480960650990888766261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277653973767327259177507 4916480960650990888766261)
                  ·
                    refine ⟨460920090061030395821837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4916480960650990888766261 460920090061030395821837)
                    ·
                      rfl

theorem cell23_2692916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2692916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692916 prefixEnd_2692916 := by exact prefixLift 2692916
  have htrace : WordTrace (prefixWord ++ tailWord_2692916) baseStart_2692916 baseEnd_2692916 := by
    simpa [prefixWord, tailWord_2692916, baseEnd_2692916] using wordTrace_append hprefix tailTrace_2692916
  have hstable : (prefixWord ++ tailWord_2692916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692916).length < 2 ^ (prefixWord ++ tailWord_2692916).sum := by decide
  have hdescent : baseEnd_2692916 < baseStart_2692916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692919 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 5, 2, 2]
def baseStart_2692919 : Nat := 118140960795 + 2692919 * 2 ^ 59
def prefixEnd_2692919 : Nat := 4983230072969 + 3 ^ 40 * 2692919 * 2
def baseEnd_2692919 : Nat := 1382761810625054675727997

theorem tailTrace_2692919 : CollatzResearch.WordTrace tailWord_2692919 prefixEnd_2692919 1382761810625054675727997 := by
  unfold tailWord_2692919
  simp only [CollatzResearch.WordTrace]
  refine ⟨98218824931021851794689811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65479216620681234529793207 98218824931021851794689811)
  ·
    refine ⟨147328237396532777692034717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98218824931021851794689811 147328237396532777692034717)
    ·
      refine ⟨55248089023699791634513019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147328237396532777692034717 55248089023699791634513019)
      ·
        refine ⟨82872133535549687451769529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55248089023699791634513019 82872133535549687451769529)
        ·
          refine ⟨62154100151662265588827147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82872133535549687451769529 62154100151662265588827147)
          ·
            refine ⟨93231150227493398383240721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62154100151662265588827147 93231150227493398383240721)
            ·
              refine ⟨69923362670620048787430541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93231150227493398383240721 69923362670620048787430541)
              ·
                refine ⟨26221261001482518295286453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69923362670620048787430541 26221261001482518295286453)
                ·
                  refine ⟨2458243218888986090183105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26221261001482518295286453 2458243218888986090183105)
                  ·
                    refine ⟨1843682414166739567637329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2458243218888986090183105 1843682414166739567637329)
                    ·
                      refine ⟨1382761810625054675727997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843682414166739567637329 1382761810625054675727997)
                      ·
                        rfl

theorem cell23_2692919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_2692919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692919 prefixEnd_2692919 := by exact prefixLift 2692919
  have htrace : WordTrace (prefixWord ++ tailWord_2692919) baseStart_2692919 baseEnd_2692919 := by
    simpa [prefixWord, tailWord_2692919, baseEnd_2692919] using wordTrace_append hprefix tailTrace_2692919
  have hstable : (prefixWord ++ tailWord_2692919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692919).length < 2 ^ (prefixWord ++ tailWord_2692919).sum := by decide
  have hdescent : baseEnd_2692919 < baseStart_2692919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692963 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 2, 4]
def baseStart_2692963 : Nat := 118140960795 + 2692963 * 2 ^ 59
def prefixEnd_2692963 : Nat := 4983230072969 + 3 ^ 40 * 2692963 * 2
def baseEnd_2692963 : Nat := 460928134591284167859265

theorem tailTrace_2692963 : CollatzResearch.WordTrace tailWord_2692963 prefixEnd_2692963 460928134591284167859265 := by
  unfold tailWord_2692963
  simp only [CollatzResearch.WordTrace]
  refine ⟨98220429742862447309291543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65480286495241631539527695 98220429742862447309291543)
  ·
    refine ⟨147330644614293670963937315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98220429742862447309291543 147330644614293670963937315)
    ·
      refine ⟨220995966921440506445905973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147330644614293670963937315 220995966921440506445905973)
      ·
        refine ⟨20718371898885047479303685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220995966921440506445905973 20718371898885047479303685)
        ·
          refine ⟨3884694731040946402369441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20718371898885047479303685 3884694731040946402369441)
          ·
            refine ⟨2913521048280709801777081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3884694731040946402369441 2913521048280709801777081)
            ·
              refine ⟨2185140786210532351332811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2913521048280709801777081 2185140786210532351332811)
              ·
                refine ⟨3277711179315798526999217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185140786210532351332811 3277711179315798526999217)
                ·
                  refine ⟨2458283384486848895249413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3277711179315798526999217 2458283384486848895249413)
                  ·
                    refine ⟨460928134591284167859265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2458283384486848895249413 460928134591284167859265)
                    ·
                      rfl

theorem cell23_2692963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 2, 4].length) (baseStart_2692963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692963 prefixEnd_2692963 := by exact prefixLift 2692963
  have htrace : WordTrace (prefixWord ++ tailWord_2692963) baseStart_2692963 baseEnd_2692963 := by
    simpa [prefixWord, tailWord_2692963, baseEnd_2692963] using wordTrace_append hprefix tailTrace_2692963
  have hstable : (prefixWord ++ tailWord_2692963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692963).length < 2 ^ (prefixWord ++ tailWord_2692963).sum := by decide
  have hdescent : baseEnd_2692963 < baseStart_2692963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692970 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_2692970 : Nat := 118140960795 + 2692970 * 2 ^ 59
def prefixEnd_2692970 : Nat := 4983230072969 + 3 ^ 40 * 2692970 * 2
def baseEnd_2692970 : Nat := 1382787998138433976190263

theorem tailTrace_2692970 : CollatzResearch.WordTrace tailWord_2692970 prefixEnd_2692970 1382787998138433976190263 := by
  unfold tailWord_2692970
  simp only [CollatzResearch.WordTrace]
  refine ⟨24555171263459271876199091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65480456702558058336530909 24555171263459271876199091)
  ·
    refine ⟨36832756895188907814298637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24555171263459271876199091 36832756895188907814298637)
    ·
      refine ⟨13812283835695840430361989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36832756895188907814298637 13812283835695840430361989)
      ·
        refine ⟨2589803219192970080692873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13812283835695840430361989 2589803219192970080692873)
        ·
          refine ⟨1942352414394727560519655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2589803219192970080692873 1942352414394727560519655)
          ·
            refine ⟨2913528621592091340779483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942352414394727560519655 2913528621592091340779483)
            ·
              refine ⟨4370292932388137011169225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913528621592091340779483 4370292932388137011169225)
              ·
                refine ⟨3277719699291102758376919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4370292932388137011169225 3277719699291102758376919)
                ·
                  refine ⟨4916579548936654137565379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277719699291102758376919 4916579548936654137565379)
                  ·
                    refine ⟨7374869323404981206348069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4916579548936654137565379 7374869323404981206348069)
                    ·
                      refine ⟨1382787998138433976190263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7374869323404981206348069 1382787998138433976190263)
                      ·
                        rfl

theorem cell23_2692970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_2692970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692970 prefixEnd_2692970 := by exact prefixLift 2692970
  have htrace : WordTrace (prefixWord ++ tailWord_2692970) baseStart_2692970 baseEnd_2692970 := by
    simpa [prefixWord, tailWord_2692970, baseEnd_2692970] using wordTrace_append hprefix tailTrace_2692970
  have hstable : (prefixWord ++ tailWord_2692970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692970).length < 2 ^ (prefixWord ++ tailWord_2692970).sum := by decide
  have hdescent : baseEnd_2692970 < baseStart_2692970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692975 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_2692975 : Nat := 118140960795 + 2692975 * 2 ^ 59
def prefixEnd_2692975 : Nat := 4983230072969 + 3 ^ 40 * 2692975 * 2
def baseEnd_2692975 : Nat := 1382790565541706456627739

theorem tailTrace_2692975 : CollatzResearch.WordTrace tailWord_2692975 prefixEnd_2692975 1382790565541706456627739 := by
  unfold tailWord_2692975
  simp only [CollatzResearch.WordTrace]
  refine ⟨98220867418818973358728379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65480578279212648905818919 98220867418818973358728379)
  ·
    refine ⟨147331301128228460038092569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98220867418818973358728379 147331301128228460038092569)
    ·
      refine ⟨110498475846171345028569427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147331301128228460038092569 110498475846171345028569427)
      ·
        refine ⟨165747713769257017542854141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110498475846171345028569427 165747713769257017542854141)
        ·
          refine ⟨62155392663471381578570303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165747713769257017542854141 62155392663471381578570303)
          ·
            refine ⟨93233088995207072367855455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62155392663471381578570303 93233088995207072367855455)
            ·
              refine ⟨139849633492810608551783183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93233088995207072367855455 139849633492810608551783183)
              ·
                refine ⟨209774450239215912827674775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139849633492810608551783183 209774450239215912827674775)
                ·
                  refine ⟨314661675358823869241512163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209774450239215912827674775 314661675358823869241512163)
                  ·
                    refine ⟨471992513038235803862268245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 314661675358823869241512163 471992513038235803862268245)
                    ·
                      refine ⟨1382790565541706456627739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 471992513038235803862268245 1382790565541706456627739)
                      ·
                        rfl

theorem cell23_2692975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_2692975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692975 prefixEnd_2692975 := by exact prefixLift 2692975
  have htrace : WordTrace (prefixWord ++ tailWord_2692975) baseStart_2692975 baseEnd_2692975 := by
    simpa [prefixWord, tailWord_2692975, baseEnd_2692975] using wordTrace_append hprefix tailTrace_2692975
  have hstable : (prefixWord ++ tailWord_2692975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692975).length < 2 ^ (prefixWord ++ tailWord_2692975).sum := by decide
  have hdescent : baseEnd_2692975 < baseStart_2692975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692990 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2692990 : Nat := 118140960795 + 2692990 * 2 ^ 59
def prefixEnd_2692990 : Nat := 4983230072969 + 3 ^ 40 * 2692990 * 2
def baseEnd_2692990 : Nat := 1382798267751523897940171

theorem tailTrace_2692990 : CollatzResearch.WordTrace tailWord_2692990 prefixEnd_2692990 1382798267751523897940171 := by
  unfold tailWord_2692990
  simp only [CollatzResearch.WordTrace]
  refine ⟨12277676814220578865065553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65480943009176420613682949 12277676814220578865065553)
  ·
    refine ⟨9208257610665434148799165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12277676814220578865065553 9208257610665434148799165)
    ·
      refine ⟨3453096603999537805799687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9208257610665434148799165 3453096603999537805799687)
      ·
        refine ⟨5179644905999306708699531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3453096603999537805799687 5179644905999306708699531)
        ·
          refine ⟨7769467358998960063049297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5179644905999306708699531 7769467358998960063049297)
          ·
            refine ⟨5827100519249220047286973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7769467358998960063049297 5827100519249220047286973)
            ·
              refine ⟨2185162694718457517732615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5827100519249220047286973 2185162694718457517732615)
              ·
                refine ⟨3277744042077686276598923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185162694718457517732615 3277744042077686276598923)
                ·
                  refine ⟨4916616063116529414898385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277744042077686276598923 4916616063116529414898385)
                  ·
                    refine ⟨3687462047337397061173789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916616063116529414898385 3687462047337397061173789)
                    ·
                      refine ⟨1382798267751523897940171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3687462047337397061173789 1382798267751523897940171)
                      ·
                        rfl

theorem cell23_2692990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2692990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692990 prefixEnd_2692990 := by exact prefixLift 2692990
  have htrace : WordTrace (prefixWord ++ tailWord_2692990) baseStart_2692990 baseEnd_2692990 := by
    simpa [prefixWord, tailWord_2692990, baseEnd_2692990] using wordTrace_append hprefix tailTrace_2692990
  have hstable : (prefixWord ++ tailWord_2692990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692990).length < 2 ^ (prefixWord ++ tailWord_2692990).sum := by decide
  have hdescent : baseEnd_2692990 < baseStart_2692990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692996 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_2692996 : Nat := 118140960795 + 2692996 * 2 ^ 59
def prefixEnd_2692996 : Nat := 4983230072969 + 3 ^ 40 * 2692996 * 2
def baseEnd_2692996 : Nat := 1382801348635450874465143

theorem tailTrace_2692996 : CollatzResearch.WordTrace tailWord_2692996 prefixEnd_2692996 1382801348635450874465143 := by
  unfold tailWord_2692996
  simp only [CollatzResearch.WordTrace]
  refine ⟨49110816675871446972621421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65481088901161929296828561 49110816675871446972621421)
  ·
    refine ⟨18416556253451792614733033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49110816675871446972621421 18416556253451792614733033)
    ·
      refine ⟨13812417190088844461049775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18416556253451792614733033 13812417190088844461049775)
      ·
        refine ⟨20718625785133266691574663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13812417190088844461049775 20718625785133266691574663)
        ·
          refine ⟨31077938677699900037361995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20718625785133266691574663 31077938677699900037361995)
          ·
            refine ⟨46616908016549850056042993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31077938677699900037361995 46616908016549850056042993)
            ·
              refine ⟨34962681012412387542032245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46616908016549850056042993 34962681012412387542032245)
              ·
                refine ⟨3277751344913661332065523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34962681012412387542032245 3277751344913661332065523)
                ·
                  refine ⟨4916627017370491998098285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277751344913661332065523 4916627017370491998098285)
                  ·
                    refine ⟨1843735131513934499286857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4916627017370491998098285 1843735131513934499286857)
                    ·
                      refine ⟨1382801348635450874465143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843735131513934499286857 1382801348635450874465143)
                      ·
                        rfl

theorem cell23_2692996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_2692996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692996 prefixEnd_2692996 := by exact prefixLift 2692996
  have htrace : WordTrace (prefixWord ++ tailWord_2692996) baseStart_2692996 baseEnd_2692996 := by
    simpa [prefixWord, tailWord_2692996, baseEnd_2692996] using wordTrace_append hprefix tailTrace_2692996
  have hstable : (prefixWord ++ tailWord_2692996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692996).length < 2 ^ (prefixWord ++ tailWord_2692996).sum := by decide
  have hdescent : baseEnd_2692996 < baseStart_2692996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693072 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_2693072 : Nat := 118140960795 + 2693072 * 2 ^ 59
def prefixEnd_2693072 : Nat := 4983230072969 + 3 ^ 40 * 2693072 * 2
def baseEnd_2693072 : Nat := 1382840373165192577114793

theorem tailTrace_2693072 : CollatzResearch.WordTrace tailWord_2693072 prefixEnd_2693072 1382840373165192577114793 := by
  unfold tailWord_2693072
  simp only [CollatzResearch.WordTrace]
  refine ⟨49112202649733779462504735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65482936866311705950006313 49112202649733779462504735)
  ·
    refine ⟨73668303974600669193757103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49112202649733779462504735 73668303974600669193757103)
    ·
      refine ⟨110502455961901003790635655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73668303974600669193757103 110502455961901003790635655)
      ·
        refine ⟨165753683942851505685953483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110502455961901003790635655 165753683942851505685953483)
        ·
          refine ⟨248630525914277258528930225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165753683942851505685953483 248630525914277258528930225)
          ·
            refine ⟨186472894435707943896697669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248630525914277258528930225 186472894435707943896697669)
            ·
              refine ⟨34963667706695239480630813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186472894435707943896697669 34963667706695239480630813)
              ·
                refine ⟨13111375390010714805236555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34963667706695239480630813 13111375390010714805236555)
                ·
                  refine ⟨19667063085016072207854833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13111375390010714805236555 19667063085016072207854833)
                  ·
                    refine ⟨14750297313762054155891125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19667063085016072207854833 14750297313762054155891125)
                    ·
                      refine ⟨1382840373165192577114793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14750297313762054155891125 1382840373165192577114793)
                      ·
                        rfl

theorem cell23_2693072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_2693072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693072 prefixEnd_2693072 := by exact prefixLift 2693072
  have htrace : WordTrace (prefixWord ++ tailWord_2693072) baseStart_2693072 baseEnd_2693072 := by
    simpa [prefixWord, tailWord_2693072, baseEnd_2693072] using wordTrace_append hprefix tailTrace_2693072
  have hstable : (prefixWord ++ tailWord_2693072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693072).length < 2 ^ (prefixWord ++ tailWord_2693072).sum := by decide
  have hdescent : baseEnd_2693072 < baseStart_2693072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693092 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_2693092 : Nat := 118140960795 + 2693092 * 2 ^ 59
def prefixEnd_2693092 : Nat := 4983230072969 + 3 ^ 40 * 2693092 * 2
def baseEnd_2693092 : Nat := 460950214259427499621567

theorem tailTrace_2693092 : CollatzResearch.WordTrace tailWord_2693092 prefixEnd_2693092 460950214259427499621567 := by
  unfold tailWord_2693092
  simp only [CollatzResearch.WordTrace]
  refine ⟨49112567379697551170368765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65483423172930068227158353 49112567379697551170368765)
  ·
    refine ⟨18417212767386581688888287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49112567379697551170368765 18417212767386581688888287)
    ·
      refine ⟨27625819151079872533332431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18417212767386581688888287 27625819151079872533332431)
      ·
        refine ⟨41438728726619808799998647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27625819151079872533332431 41438728726619808799998647)
        ·
          refine ⟨62158093089929713199997971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41438728726619808799998647 62158093089929713199997971)
          ·
            refine ⟨93237139634894569799996957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62158093089929713199997971 93237139634894569799996957)
            ·
              refine ⟨34963927363085463674998859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93237139634894569799996957 34963927363085463674998859)
              ·
                refine ⟨52445891044628195512498289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34963927363085463674998859 52445891044628195512498289)
                ·
                  refine ⟨39334418283471146634373717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52445891044628195512498289 39334418283471146634373717)
                  ·
                    refine ⟨460950214259427499621567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39334418283471146634373717 460950214259427499621567)
                    ·
                      rfl

theorem cell23_2693092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_2693092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693092 prefixEnd_2693092 := by exact prefixLift 2693092
  have htrace : WordTrace (prefixWord ++ tailWord_2693092) baseStart_2693092 baseEnd_2693092 := by
    simpa [prefixWord, tailWord_2693092, baseEnd_2693092] using wordTrace_append hprefix tailTrace_2693092
  have hstable : (prefixWord ++ tailWord_2693092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693092).length < 2 ^ (prefixWord ++ tailWord_2693092).sum := by decide
  have hdescent : baseEnd_2693092 < baseStart_2693092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693099 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 1, 6, 2]
def baseStart_2693099 : Nat := 118140960795 + 2693099 * 2 ^ 59
def prefixEnd_2693099 : Nat := 4983230072969 + 3 ^ 40 * 2693099 * 2
def baseEnd_2693099 : Nat := 1382854237142863971477169

theorem tailTrace_2693099 : CollatzResearch.WordTrace tailWord_2693099 prefixEnd_2693099 1382854237142863971477169 := by
  unfold tailWord_2693099
  simp only [CollatzResearch.WordTrace]
  refine ⟨98225390070369742536242351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65483593380246495024161567 98225390070369742536242351)
  ·
    refine ⟨147338085105554613804363527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98225390070369742536242351 147338085105554613804363527)
    ·
      refine ⟨221007127658331920706545291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147338085105554613804363527 221007127658331920706545291)
      ·
        refine ⟨331510691487497881059817937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221007127658331920706545291 331510691487497881059817937)
        ·
          refine ⟨248633018615623410794863453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331510691487497881059817937 248633018615623410794863453)
          ·
            refine ⟨93237381980858779048073795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248633018615623410794863453 93237381980858779048073795)
            ·
              refine ⟨139856072971288168572110693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93237381980858779048073795 139856072971288168572110693)
              ·
                refine ⟨26223013682116531607270755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139856072971288168572110693 26223013682116531607270755)
                ·
                  refine ⟨39334520523174797410906133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26223013682116531607270755 39334520523174797410906133)
                  ·
                    refine ⟨1843805649523818628636225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39334520523174797410906133 1843805649523818628636225)
                    ·
                      refine ⟨1382854237142863971477169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843805649523818628636225 1382854237142863971477169)
                      ·
                        rfl

theorem cell23_2693099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 6, 2].length) (baseStart_2693099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693099 prefixEnd_2693099 := by exact prefixLift 2693099
  have htrace : WordTrace (prefixWord ++ tailWord_2693099) baseStart_2693099 baseEnd_2693099 := by
    simpa [prefixWord, tailWord_2693099, baseEnd_2693099] using wordTrace_append hprefix tailTrace_2693099
  have hstable : (prefixWord ++ tailWord_2693099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693099).length < 2 ^ (prefixWord ++ tailWord_2693099).sum := by decide
  have hdescent : baseEnd_2693099 < baseStart_2693099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693112 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_2693112 : Nat := 118140960795 + 2693112 * 2 ^ 59
def prefixEnd_2693112 : Nat := 4983230072969 + 3 ^ 40 * 2693112 * 2
def baseEnd_2693112 : Nat := 1382860912391372420614609

theorem tailTrace_2693112 : CollatzResearch.WordTrace tailWord_2693112 prefixEnd_2693112 1382860912391372420614609 := by
  unfold tailWord_2693112
  simp only [CollatzResearch.WordTrace]
  refine ⟨49112932109661322878232795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65483909479548430504310393 49112932109661322878232795)
  ·
    refine ⟨73669398164491984317349193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49112932109661322878232795 73669398164491984317349193)
    ·
      refine ⟨55252048623368988238011895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73669398164491984317349193 55252048623368988238011895)
      ·
        refine ⟨82878072935053482357017843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55252048623368988238011895 82878072935053482357017843)
        ·
          refine ⟨124317109402580223535526765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82878072935053482357017843 124317109402580223535526765)
          ·
            refine ⟨46618916025967583825822537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124317109402580223535526765 46618916025967583825822537)
            ·
              refine ⟨34964187019475687869366903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46618916025967583825822537 34964187019475687869366903)
              ·
                refine ⟨52446280529213531804050355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34964187019475687869366903 52446280529213531804050355)
                ·
                  refine ⟨78669420793820297706075533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52446280529213531804050355 78669420793820297706075533)
                  ·
                    refine ⟨29501032797682611639778325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78669420793820297706075533 29501032797682611639778325)
                    ·
                      refine ⟨1382860912391372420614609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29501032797682611639778325 1382860912391372420614609)
                      ·
                        rfl

theorem cell23_2693112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_2693112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693112 prefixEnd_2693112 := by exact prefixLift 2693112
  have htrace : WordTrace (prefixWord ++ tailWord_2693112) baseStart_2693112 baseEnd_2693112 := by
    simpa [prefixWord, tailWord_2693112, baseEnd_2693112] using wordTrace_append hprefix tailTrace_2693112
  have hstable : (prefixWord ++ tailWord_2693112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693112).length < 2 ^ (prefixWord ++ tailWord_2693112).sum := by decide
  have hdescent : baseEnd_2693112 < baseStart_2693112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693153 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_2693153 : Nat := 118140960795 + 2693153 * 2 ^ 59
def prefixEnd_2693153 : Nat := 4983230072969 + 3 ^ 40 * 2693153 * 2
def baseEnd_2693153 : Nat := 1382881965098206760201921

theorem tailTrace_2693153 : CollatzResearch.WordTrace tailWord_2693153 prefixEnd_2693153 1382881965098206760201921 := by
  unfold tailWord_2693153
  simp only [CollatzResearch.WordTrace]
  refine ⟨98227359612174109758708113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65484906408116073172472075 98227359612174109758708113)
  ·
    refine ⟨73670519709130582319031085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98227359612174109758708113 73670519709130582319031085)
    ·
      refine ⟨27626444890923968369636657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73670519709130582319031085 27626444890923968369636657)
      ·
        refine ⟨20719833668192976277227493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27626444890923968369636657 20719833668192976277227493)
        ·
          refine ⟨3884968812786183051980155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20719833668192976277227493 3884968812786183051980155)
          ·
            refine ⟨5827453219179274577970233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3884968812786183051980155 5827453219179274577970233)
            ·
              refine ⟨4370589914384455933477675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5827453219179274577970233 4370589914384455933477675)
              ·
                refine ⟨6555884871576683900216513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370589914384455933477675 6555884871576683900216513)
                ·
                  refine ⟨4916913653682512925162385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6555884871576683900216513 4916913653682512925162385)
                  ·
                    refine ⟨3687685240261884693871789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916913653682512925162385 3687685240261884693871789)
                    ·
                      refine ⟨1382881965098206760201921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3687685240261884693871789 1382881965098206760201921)
                      ·
                        rfl

theorem cell23_2693153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_2693153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693153 prefixEnd_2693153 := by exact prefixLift 2693153
  have htrace : WordTrace (prefixWord ++ tailWord_2693153) baseStart_2693153 baseEnd_2693153 := by
    simpa [prefixWord, tailWord_2693153, baseEnd_2693153] using wordTrace_append hprefix tailTrace_2693153
  have hstable : (prefixWord ++ tailWord_2693153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693153).length < 2 ^ (prefixWord ++ tailWord_2693153).sum := by decide
  have hdescent : baseEnd_2693153 < baseStart_2693153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693177 : List Nat := [1, 2, 1, 5, 3, 2, 2, 2, 1, 4]
def baseStart_2693177 : Nat := 118140960795 + 2693177 * 2 ^ 59
def prefixEnd_2693177 : Nat := 4983230072969 + 3 ^ 40 * 2693177 * 2
def baseEnd_2693177 : Nat := 460964762877971555433937

theorem tailTrace_2693177 : CollatzResearch.WordTrace tailWord_2693177 prefixEnd_2693177 460964762877971555433937 := by
  unfold tailWord_2693177
  simp only [CollatzResearch.WordTrace]
  refine ⟨98228234964087161857581785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65485489976058107905054523 98228234964087161857581785)
  ·
    refine ⟨73671176223065371393186339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98228234964087161857581785 73671176223065371393186339)
    ·
      refine ⟨110506764334598057089779509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73671176223065371393186339 110506764334598057089779509)
      ·
        refine ⟨10360009156368567852166829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110506764334598057089779509 10360009156368567852166829)
        ·
          refine ⟨3885003433638212944562561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10360009156368567852166829 3885003433638212944562561)
          ·
            refine ⟨2913752575228659708421921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3885003433638212944562561 2913752575228659708421921)
            ·
              refine ⟨2185314431421494781316441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2913752575228659708421921 2185314431421494781316441)
              ·
                refine ⟨1638985823566121085987331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2185314431421494781316441 1638985823566121085987331)
                ·
                  refine ⟨2458478735349181628980997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638985823566121085987331 2458478735349181628980997)
                  ·
                    refine ⟨460964762877971555433937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2458478735349181628980997 460964762877971555433937)
                    ·
                      rfl

theorem cell23_2693177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 1, 4].length) (baseStart_2693177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693177 prefixEnd_2693177 := by exact prefixLift 2693177
  have htrace : WordTrace (prefixWord ++ tailWord_2693177) baseStart_2693177 baseEnd_2693177 := by
    simpa [prefixWord, tailWord_2693177, baseEnd_2693177] using wordTrace_append hprefix tailTrace_2693177
  have hstable : (prefixWord ++ tailWord_2693177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693177).length < 2 ^ (prefixWord ++ tailWord_2693177).sum := by decide
  have hdescent : baseEnd_2693177 < baseStart_2693177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693223 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_2693223 : Nat := 118140960795 + 2693223 * 2 ^ 59
def prefixEnd_2693223 : Nat := 4983230072969 + 3 ^ 40 * 2693223 * 2
def baseEnd_2693223 : Nat := 1382917908744021486326599

theorem tailTrace_2693223 : CollatzResearch.WordTrace tailWord_2693223 prefixEnd_2693223 1382917908744021486326599 := by
  unfold tailWord_2693223
  simp only [CollatzResearch.WordTrace]
  refine ⟨98229912721920511713756323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65486608481280341142504215 98229912721920511713756323)
  ·
    refine ⟨147344869082880767570634485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98229912721920511713756323 147344869082880767570634485)
    ·
      refine ⟨13813581476520071959746983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147344869082880767570634485 13813581476520071959746983)
      ·
        refine ⟨20720372214780107939620475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13813581476520071959746983 20720372214780107939620475)
        ·
          refine ⟨31080558322170161909430713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20720372214780107939620475 31080558322170161909430713)
          ·
            refine ⟨23310418741627621432073035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31080558322170161909430713 23310418741627621432073035)
            ·
              refine ⟨34965628112441432148109553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23310418741627621432073035 34965628112441432148109553)
              ·
                refine ⟨26224221084331074111082165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34965628112441432148109553 26224221084331074111082165)
                ·
                  refine ⟨2458520726656038197913953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26224221084331074111082165 2458520726656038197913953)
                  ·
                    refine ⟨1843890544992028648435465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2458520726656038197913953 1843890544992028648435465)
                    ·
                      refine ⟨1382917908744021486326599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843890544992028648435465 1382917908744021486326599)
                      ·
                        rfl

theorem cell23_2693223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_2693223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693223 prefixEnd_2693223 := by exact prefixLift 2693223
  have htrace : WordTrace (prefixWord ++ tailWord_2693223) baseStart_2693223 baseEnd_2693223 := by
    simpa [prefixWord, tailWord_2693223, baseEnd_2693223] using wordTrace_append hprefix tailTrace_2693223
  have hstable : (prefixWord ++ tailWord_2693223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693223).length < 2 ^ (prefixWord ++ tailWord_2693223).sum := by decide
  have hdescent : baseEnd_2693223 < baseStart_2693223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693229 : List Nat := [1, 5, 1, 1, 2, 1, 12]
def baseStart_2693229 : Nat := 118140960795 + 2693229 * 2 ^ 59
def prefixEnd_2693229 : Nat := 4983230072969 + 3 ^ 40 * 2693229 * 2
def baseEnd_2693229 : Nat := 17073098637382079788291

theorem tailTrace_2693229 : CollatzResearch.WordTrace tailWord_2693229 prefixEnd_2693229 17073098637382079788291 := by
  unfold tailWord_2693229
  simp only [CollatzResearch.WordTrace]
  refine ⟨98230131559898774738474741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65486754373265849825649827 98230131559898774738474741)
  ·
    refine ⟨9209074833740510131732007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98230131559898774738474741 9209074833740510131732007)
    ·
      refine ⟨13813612250610765197598011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9209074833740510131732007 13813612250610765197598011)
      ·
        refine ⟨20720418375916147796397017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13813612250610765197598011 20720418375916147796397017)
        ·
          refine ⟨15540313781937110847297763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20720418375916147796397017 15540313781937110847297763)
          ·
            refine ⟨23310470672905666270946645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15540313781937110847297763 23310470672905666270946645)
            ·
              refine ⟨17073098637382079788291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 23310470672905666270946645 17073098637382079788291)
              ·
                rfl

theorem cell23_2693229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 12].length) (baseStart_2693229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693229 prefixEnd_2693229 := by exact prefixLift 2693229
  have htrace : WordTrace (prefixWord ++ tailWord_2693229) baseStart_2693229 baseEnd_2693229 := by
    simpa [prefixWord, tailWord_2693229, baseEnd_2693229] using wordTrace_append hprefix tailTrace_2693229
  have hstable : (prefixWord ++ tailWord_2693229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693229).length < 2 ^ (prefixWord ++ tailWord_2693229).sum := by decide
  have hdescent : baseEnd_2693229 < baseStart_2693229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693253 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 4]
def baseStart_2693253 : Nat := 118140960795 + 2693253 * 2 ^ 59
def prefixEnd_2693253 : Nat := 4983230072969 + 3 ^ 40 * 2693253 * 2
def baseEnd_2693253 : Nat := 1382933313163656368951461

theorem tailTrace_2693253 : CollatzResearch.WordTrace tailWord_2693253 prefixEnd_2693253 1382933313163656368951461 := by
  unfold tailWord_2693253
  simp only [CollatzResearch.WordTrace]
  refine ⟨98231006911811826837348413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65487337941207884558232275 98231006911811826837348413)
  ·
    refine ⟨36836627591929435064005655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98231006911811826837348413 36836627591929435064005655)
    ·
      refine ⟨55254941387894152596008483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36836627591929435064005655 55254941387894152596008483)
      ·
        refine ⟨82882412081841228894012725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55254941387894152596008483 82882412081841228894012725)
        ·
          refine ⟨7770226132672615208813693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82882412081841228894012725 7770226132672615208813693)
          ·
            refine ⟨2913834799752230703305135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7770226132672615208813693 2913834799752230703305135)
            ·
              refine ⟨4370752199628346054957703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913834799752230703305135 4370752199628346054957703)
              ·
                refine ⟨6556128299442519082436555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370752199628346054957703 6556128299442519082436555)
                ·
                  refine ⟨9834192449163778623654833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6556128299442519082436555 9834192449163778623654833)
                  ·
                    refine ⟨7375644336872833967741125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9834192449163778623654833 7375644336872833967741125)
                    ·
                      refine ⟨1382933313163656368951461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7375644336872833967741125 1382933313163656368951461)
                      ·
                        rfl

theorem cell23_2693253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_2693253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693253 prefixEnd_2693253 := by exact prefixLift 2693253
  have htrace : WordTrace (prefixWord ++ tailWord_2693253) baseStart_2693253 baseEnd_2693253 := by
    simpa [prefixWord, tailWord_2693253, baseEnd_2693253] using wordTrace_append hprefix tailTrace_2693253
  have hstable : (prefixWord ++ tailWord_2693253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693253).length < 2 ^ (prefixWord ++ tailWord_2693253).sum := by decide
  have hdescent : baseEnd_2693253 < baseStart_2693253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693269 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2693269 : Nat := 118140960795 + 2693269 * 2 ^ 59
def prefixEnd_2693269 : Nat := 4983230072969 + 3 ^ 40 * 2693269 * 2
def baseEnd_2693269 : Nat := 1382941528854128306351387

theorem tailTrace_2693269 : CollatzResearch.WordTrace tailWord_2693269 prefixEnd_2693269 1382941528854128306351387 := by
  unfold tailWord_2693269
  simp only [CollatzResearch.WordTrace]
  refine ⟨98231590479753861569930861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65487726986502574379953907 98231590479753861569930861)
  ·
    refine ⟨36836846429907698088724073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98231590479753861569930861 36836846429907698088724073)
    ·
      refine ⟨27627634822430773566543055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36836846429907698088724073 27627634822430773566543055)
      ·
        refine ⟨41441452233646160349814583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27627634822430773566543055 41441452233646160349814583)
        ·
          refine ⟨62162178350469240524721875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41441452233646160349814583 62162178350469240524721875)
          ·
            refine ⟨93243267525703860787082813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62162178350469240524721875 93243267525703860787082813)
            ·
              refine ⟨34966225322138947795156055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93243267525703860787082813 34966225322138947795156055)
              ·
                refine ⟨52449337983208421692734083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34966225322138947795156055 52449337983208421692734083)
                ·
                  refine ⟨78674006974812632539101125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52449337983208421692734083 78674006974812632539101125)
                  ·
                    refine ⟨14751376307777368601081461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78674006974812632539101125 14751376307777368601081461)
                    ·
                      refine ⟨1382941528854128306351387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14751376307777368601081461 1382941528854128306351387)
                      ·
                        rfl

theorem cell23_2693269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2693269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693269 prefixEnd_2693269 := by exact prefixLift 2693269
  have htrace : WordTrace (prefixWord ++ tailWord_2693269) baseStart_2693269 baseEnd_2693269 := by
    simpa [prefixWord, tailWord_2693269, baseEnd_2693269] using wordTrace_append hprefix tailTrace_2693269
  have hstable : (prefixWord ++ tailWord_2693269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693269).length < 2 ^ (prefixWord ++ tailWord_2693269).sum := by decide
  have hdescent : baseEnd_2693269 < baseStart_2693269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693296 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 2, 8, 2]
def baseStart_2693296 : Nat := 118140960795 + 2693296 * 2 ^ 59
def prefixEnd_2693296 : Nat := 4983230072969 + 3 ^ 40 * 2693296 * 2
def baseEnd_2693296 : Nat := 1382955392831799700713763

theorem tailTrace_2693296 : CollatzResearch.WordTrace tailWord_2693296 prefixEnd_2693296 1382955392831799700713763 := by
  unfold tailWord_2693296
  simp only [CollatzResearch.WordTrace]
  refine ⟨49116287625328022590581871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65488383500437363454109161 49116287625328022590581871)
  ·
    refine ⟨73674431437992033885872807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49116287625328022590581871 73674431437992033885872807)
    ·
      refine ⟨110511647156988050828809211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73674431437992033885872807 110511647156988050828809211)
      ·
        refine ⟨165767470735482076243213817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110511647156988050828809211 165767470735482076243213817)
        ·
          refine ⟨124325603051611557182410363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165767470735482076243213817 124325603051611557182410363)
          ·
            refine ⟨186488404577417335773615545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124325603051611557182410363 186488404577417335773615545)
            ·
              refine ⟨139866303433063001830211659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186488404577417335773615545 139866303433063001830211659)
              ·
                refine ⟨209799455149594502745317489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139866303433063001830211659 209799455149594502745317489)
                ·
                  refine ⟨157349591362195877058988117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209799455149594502745317489 157349591362195877058988117)
                  ·
                    refine ⟨1843940523775732934285017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 157349591362195877058988117 1843940523775732934285017)
                    ·
                      refine ⟨1382955392831799700713763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843940523775732934285017 1382955392831799700713763)
                      ·
                        rfl

theorem cell23_2693296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 8, 2].length) (baseStart_2693296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693296 prefixEnd_2693296 := by exact prefixLift 2693296
  have htrace : WordTrace (prefixWord ++ tailWord_2693296) baseStart_2693296 baseEnd_2693296 := by
    simpa [prefixWord, tailWord_2693296, baseEnd_2693296] using wordTrace_append hprefix tailTrace_2693296
  have hstable : (prefixWord ++ tailWord_2693296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693296).length < 2 ^ (prefixWord ++ tailWord_2693296).sum := by decide
  have hdescent : baseEnd_2693296 < baseStart_2693296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693299 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 5]
def baseStart_2693299 : Nat := 118140960795 + 2693299 * 2 ^ 59
def prefixEnd_2693299 : Nat := 4983230072969 + 3 ^ 40 * 2693299 * 2
def baseEnd_2693299 : Nat := 1382956933273763188976249

theorem tailTrace_2693299 : CollatzResearch.WordTrace tailWord_2693299 prefixEnd_2693299 1382956933273763188976249 := by
  unfold tailWord_2693299
  simp only [CollatzResearch.WordTrace]
  refine ⟨98232684669645176693522951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65488456446430117795681967 98232684669645176693522951)
  ·
    refine ⟨147349027004467765040284427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98232684669645176693522951 147349027004467765040284427)
    ·
      refine ⟨221023540506701647560426641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147349027004467765040284427 221023540506701647560426641)
      ·
        refine ⟨165767655380026235670319981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221023540506701647560426641 165767655380026235670319981)
        ·
          refine ⟨62162870767509838376369993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165767655380026235670319981 62162870767509838376369993)
          ·
            refine ⟨46622153075632378782277495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62162870767509838376369993 46622153075632378782277495)
            ·
              refine ⟨69933229613448568173416243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46622153075632378782277495 69933229613448568173416243)
              ·
                refine ⟨104899844420172852260124365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69933229613448568173416243 104899844420172852260124365)
                ·
                  refine ⟨39337441657564819597546637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104899844420172852260124365 39337441657564819597546637)
                  ·
                    refine ⟨14751540621586807349079989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39337441657564819597546637 14751540621586807349079989)
                    ·
                      refine ⟨1382956933273763188976249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14751540621586807349079989 1382956933273763188976249)
                      ·
                        rfl

theorem cell23_2693299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_2693299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693299 prefixEnd_2693299 := by exact prefixLift 2693299
  have htrace : WordTrace (prefixWord ++ tailWord_2693299) baseStart_2693299 baseEnd_2693299 := by
    simpa [prefixWord, tailWord_2693299, baseEnd_2693299] using wordTrace_append hprefix tailTrace_2693299
  have hstable : (prefixWord ++ tailWord_2693299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693299).length < 2 ^ (prefixWord ++ tailWord_2693299).sum := by decide
  have hdescent : baseEnd_2693299 < baseStart_2693299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693330 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_2693330 : Nat := 118140960795 + 2693330 * 2 ^ 59
def prefixEnd_2693330 : Nat := 4983230072969 + 3 ^ 40 * 2693330 * 2
def baseEnd_2693330 : Nat := 1382972851174052567688607

theorem tailTrace_2693330 : CollatzResearch.WordTrace tailWord_2693330 prefixEnd_2693330 1382972851174052567688607 := by
  unfold tailWord_2693330
  simp only [CollatzResearch.WordTrace]
  refine ⟨24558453833133217246975361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65489210221688579325267629 24558453833133217246975361)
  ·
    refine ⟨18418840374849912935231521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24558453833133217246975361 18418840374849912935231521)
    ·
      refine ⟨13814130281137434701423641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18418840374849912935231521 13814130281137434701423641)
      ·
        refine ⟨10360597710853076026067731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13814130281137434701423641 10360597710853076026067731)
        ·
          refine ⟨15540896566279614039101597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10360597710853076026067731 15540896566279614039101597)
          ·
            refine ⟨5827836212354855264663099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15540896566279614039101597 5827836212354855264663099)
            ·
              refine ⟨8741754318532282896994649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5827836212354855264663099 8741754318532282896994649)
              ·
                refine ⟨6556315738899212172745987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8741754318532282896994649 6556315738899212172745987)
                ·
                  refine ⟨9834473608348818259118981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6556315738899212172745987 9834473608348818259118981)
                  ·
                    refine ⟨1843963801565403423584809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9834473608348818259118981 1843963801565403423584809)
                    ·
                      refine ⟨1382972851174052567688607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843963801565403423584809 1382972851174052567688607)
                      ·
                        rfl

theorem cell23_2693330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_2693330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693330 prefixEnd_2693330 := by exact prefixLift 2693330
  have htrace : WordTrace (prefixWord ++ tailWord_2693330) baseStart_2693330 baseEnd_2693330 := by
    simpa [prefixWord, tailWord_2693330, baseEnd_2693330] using wordTrace_append hprefix tailTrace_2693330
  have hstable : (prefixWord ++ tailWord_2693330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693330).length < 2 ^ (prefixWord ++ tailWord_2693330).sum := by decide
  have hdescent : baseEnd_2693330 < baseStart_2693330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693403 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 2, 4, 2]
def baseStart_2693403 : Nat := 118140960795 + 2693403 * 2 ^ 59
def prefixEnd_2693403 : Nat := 4983230072969 + 3 ^ 40 * 2693403 * 2
def baseEnd_2693403 : Nat := 1383010335261830782075771

theorem tailTrace_2693403 : CollatzResearch.WordTrace tailWord_2693403 prefixEnd_2693403 1383010335261830782075771 := by
  unfold tailWord_2693403
  simp only [CollatzResearch.WordTrace]
  refine ⟨98236477861268402455308863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65490985240845601636872575 98236477861268402455308863)
  ·
    refine ⟨147354716791902603682963295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98236477861268402455308863 147354716791902603682963295)
    ·
      refine ⟨221032075187853905524444943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147354716791902603682963295 221032075187853905524444943)
      ·
        refine ⟨331548112781780858286667415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221032075187853905524444943 331548112781780858286667415)
        ·
          refine ⟨497322169172671287430001123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331548112781780858286667415 497322169172671287430001123)
          ·
            refine ⟨745983253759006931145001685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497322169172671287430001123 745983253759006931145001685)
            ·
              refine ⟨17483982509976724948710977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 745983253759006931145001685 17483982509976724948710977)
              ·
                refine ⟨13112986882482543711533233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17483982509976724948710977 13112986882482543711533233)
                ·
                  refine ⟨9834740161861907783649925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13112986882482543711533233 9834740161861907783649925)
                  ·
                    refine ⟨1844013780349107709434361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9834740161861907783649925 1844013780349107709434361)
                    ·
                      refine ⟨1383010335261830782075771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844013780349107709434361 1383010335261830782075771)
                      ·
                        rfl

theorem cell23_2693403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 4, 2].length) (baseStart_2693403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693403 prefixEnd_2693403 := by exact prefixLift 2693403
  have htrace : WordTrace (prefixWord ++ tailWord_2693403) baseStart_2693403 baseEnd_2693403 := by
    simpa [prefixWord, tailWord_2693403, baseEnd_2693403] using wordTrace_append hprefix tailTrace_2693403
  have hstable : (prefixWord ++ tailWord_2693403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693403).length < 2 ^ (prefixWord ++ tailWord_2693403).sum := by decide
  have hdescent : baseEnd_2693403 < baseStart_2693403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693466 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_2693466 : Nat := 118140960795 + 2693466 * 2 ^ 59
def prefixEnd_2693466 : Nat := 4983230072969 + 3 ^ 40 * 2693466 * 2
def baseEnd_2693466 : Nat := 1383042684543064035587981

theorem tailTrace_2693466 : CollatzResearch.WordTrace tailWord_2693466 prefixEnd_2693466 1383042684543064035587981 := by
  unfold tailWord_2693466
  simp only [CollatzResearch.WordTrace]
  refine ⟨24559693915010041053713063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65492517106693442809901501 24559693915010041053713063)
  ·
    refine ⟨36839540872515061580569595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24559693915010041053713063 36839540872515061580569595)
    ·
      refine ⟨55259311308772592370854393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36839540872515061580569595 55259311308772592370854393)
      ·
        refine ⟨41444483481579444278140795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55259311308772592370854393 41444483481579444278140795)
        ·
          refine ⟨62166725222369166417211193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41444483481579444278140795 62166725222369166417211193)
          ·
            refine ⟨46625043916776874812908395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62166725222369166417211193 46625043916776874812908395)
            ·
              refine ⟨69937565875165312219362593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46625043916776874812908395 69937565875165312219362593)
              ·
                refine ⟨52453174406373984164521945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69937565875165312219362593 52453174406373984164521945)
                ·
                  refine ⟨39339880804780488123391459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52453174406373984164521945 39339880804780488123391459)
                  ·
                    refine ⟨59009821207170732185087189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39339880804780488123391459 59009821207170732185087189)
                    ·
                      refine ⟨1383042684543064035587981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59009821207170732185087189 1383042684543064035587981)
                      ·
                        rfl

theorem cell23_2693466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_2693466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693466 prefixEnd_2693466 := by exact prefixLift 2693466
  have htrace : WordTrace (prefixWord ++ tailWord_2693466) baseStart_2693466 baseEnd_2693466 := by
    simpa [prefixWord, tailWord_2693466, baseEnd_2693466] using wordTrace_append hprefix tailTrace_2693466
  have hstable : (prefixWord ++ tailWord_2693466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693466).length < 2 ^ (prefixWord ++ tailWord_2693466).sum := by decide
  have hdescent : baseEnd_2693466 < baseStart_2693466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693490 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_2693490 : Nat := 118140960795 + 2693490 * 2 ^ 59
def prefixEnd_2693490 : Nat := 4983230072969 + 3 ^ 40 * 2693490 * 2
def baseEnd_2693490 : Nat := 461018336026257313895957

theorem tailTrace_2693490 : CollatzResearch.WordTrace tailWord_2693490 prefixEnd_2693490 461018336026257313895957 := by
  unfold tailWord_2693490
  simp only [CollatzResearch.WordTrace]
  refine ⟨24559912752988304078431481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65493100674635477542483949 24559912752988304078431481)
  ·
    refine ⟨18419934564741228058823611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24559912752988304078431481 18419934564741228058823611)
    ·
      refine ⟨27629901847111842088235417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18419934564741228058823611 27629901847111842088235417)
      ·
        refine ⟨20722426385333881566176563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27629901847111842088235417 20722426385333881566176563)
        ·
          refine ⟨31083639578000822349264845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20722426385333881566176563 31083639578000822349264845)
          ·
            refine ⟨11656364841750308380974317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31083639578000822349264845 11656364841750308380974317)
            ·
              refine ⟨4371136815656365642865369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11656364841750308380974317 4371136815656365642865369)
              ·
                refine ⟨3278352611742274232149027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4371136815656365642865369 3278352611742274232149027)
                ·
                  refine ⟨4917528917613411348223541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278352611742274232149027 4917528917613411348223541)
                  ·
                    refine ⟨461018336026257313895957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4917528917613411348223541 461018336026257313895957)
                    ·
                      rfl

theorem cell23_2693490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_2693490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693490 prefixEnd_2693490 := by exact prefixLift 2693490
  have htrace : WordTrace (prefixWord ++ tailWord_2693490) baseStart_2693490 baseEnd_2693490 := by
    simpa [prefixWord, tailWord_2693490, baseEnd_2693490] using wordTrace_append hprefix tailTrace_2693490
  have hstable : (prefixWord ++ tailWord_2693490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693490).length < 2 ^ (prefixWord ++ tailWord_2693490).sum := by decide
  have hdescent : baseEnd_2693490 < baseStart_2693490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693496 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_2693496 : Nat := 118140960795 + 2693496 * 2 ^ 59
def prefixEnd_2693496 : Nat := 4983230072969 + 3 ^ 40 * 2693496 * 2
def baseEnd_2693496 : Nat := 1383058088962698918212843

theorem tailTrace_2693496 : CollatzResearch.WordTrace tailWord_2693496 prefixEnd_2693496 1383058088962698918212843 := by
  unfold tailWord_2693496
  simp only [CollatzResearch.WordTrace]
  refine ⟨49119934924965739669222171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65493246566620986225629561 49119934924965739669222171)
  ·
    refine ⟨73679902387448609503833257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49119934924965739669222171 73679902387448609503833257)
    ·
      refine ⟨55259926790586457127874943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73679902387448609503833257 55259926790586457127874943)
      ·
        refine ⟨82889890185879685691812415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55259926790586457127874943 82889890185879685691812415)
        ·
          refine ⟨124334835278819528537718623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82889890185879685691812415 124334835278819528537718623)
          ·
            refine ⟨186502252918229292806577935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124334835278819528537718623 186502252918229292806577935)
            ·
              refine ⟨279753379377343939209866903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186502252918229292806577935 279753379377343939209866903)
              ·
                refine ⟨419630069066015908814800355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279753379377343939209866903 419630069066015908814800355)
                ·
                  refine ⟨629445103599023863222200533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419630069066015908814800355 629445103599023863222200533)
                  ·
                    refine ⟨14752619615602121794270325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 629445103599023863222200533 14752619615602121794270325)
                    ·
                      refine ⟨1383058088962698918212843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14752619615602121794270325 1383058088962698918212843)
                      ·
                        rfl

theorem cell23_2693496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_2693496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693496 prefixEnd_2693496 := by exact prefixLift 2693496
  have htrace : WordTrace (prefixWord ++ tailWord_2693496) baseStart_2693496 baseEnd_2693496 := by
    simpa [prefixWord, tailWord_2693496, baseEnd_2693496] using wordTrace_append hprefix tailTrace_2693496
  have hstable : (prefixWord ++ tailWord_2693496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693496).length < 2 ^ (prefixWord ++ tailWord_2693496).sum := by decide
  have hdescent : baseEnd_2693496 < baseStart_2693496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693507 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 1, 5]
def baseStart_2693507 : Nat := 118140960795 + 2693507 * 2 ^ 59
def prefixEnd_2693507 : Nat := 4983230072969 + 3 ^ 40 * 2693507 * 2
def baseEnd_2693507 : Nat := 461021245749966125058431

theorem tailTrace_2693507 : CollatzResearch.WordTrace tailWord_2693507 prefixEnd_2693507 461021245749966125058431 := by
  unfold tailWord_2693507
  simp only [CollatzResearch.WordTrace]
  refine ⟨98240271052891628217094775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65493514035261085478063183 98240271052891628217094775)
  ·
    refine ⟨147360406579337442325642163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98240271052891628217094775 147360406579337442325642163)
    ·
      refine ⟨221040609869006163488463245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147360406579337442325642163 221040609869006163488463245)
      ·
        refine ⟨82890228700877311308173717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221040609869006163488463245 82890228700877311308173717)
        ·
          refine ⟨3885479470353623967570643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82890228700877311308173717 3885479470353623967570643)
          ·
            refine ⟨5828219205530435951355965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3885479470353623967570643 5828219205530435951355965)
            ·
              refine ⟨2185582202073913481758487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5828219205530435951355965 2185582202073913481758487)
              ·
                refine ⟨3278373303110870222637731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185582202073913481758487 3278373303110870222637731)
                ·
                  refine ⟨4917559954666305333956597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278373303110870222637731 4917559954666305333956597)
                  ·
                    refine ⟨461021245749966125058431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4917559954666305333956597 461021245749966125058431)
                    ·
                      rfl

theorem cell23_2693507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 5].length) (baseStart_2693507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693507 prefixEnd_2693507 := by exact prefixLift 2693507
  have htrace : WordTrace (prefixWord ++ tailWord_2693507) baseStart_2693507 baseEnd_2693507 := by
    simpa [prefixWord, tailWord_2693507, baseEnd_2693507] using wordTrace_append hprefix tailTrace_2693507
  have hstable : (prefixWord ++ tailWord_2693507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693507).length < 2 ^ (prefixWord ++ tailWord_2693507).sum := by decide
  have hdescent : baseEnd_2693507 < baseStart_2693507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693516 : List Nat := [2, 2, 1, 2, 1, 15]
def baseStart_2693516 : Nat := 118140960795 + 2693516 * 2 ^ 59
def prefixEnd_2693516 : Nat := 4983230072969 + 3 ^ 40 * 2693516 * 2
def baseEnd_2693516 : Nat := 5691639335702834732357

theorem tailTrace_2693516 : CollatzResearch.WordTrace tailWord_2693516 prefixEnd_2693516 5691639335702834732357 := by
  unfold tailWord_2693516
  simp only [CollatzResearch.WordTrace]
  refine ⟨49120299654929511377086201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65493732873239348502781601 49120299654929511377086201)
  ·
    refine ⟨36840224741197133532814651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49120299654929511377086201 36840224741197133532814651)
    ·
      refine ⟨55260337111795700299221977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36840224741197133532814651 55260337111795700299221977)
      ·
        refine ⟨41445252833846775224416483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55260337111795700299221977 41445252833846775224416483)
        ·
          refine ⟨62167879250770162836624725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41445252833846775224416483 62167879250770162836624725)
          ·
            refine ⟨5691639335702834732357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 62167879250770162836624725 5691639335702834732357)
            ·
              rfl

theorem cell23_2693516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 15].length) (baseStart_2693516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693516 prefixEnd_2693516 := by exact prefixLift 2693516
  have htrace : WordTrace (prefixWord ++ tailWord_2693516) baseStart_2693516 baseEnd_2693516 := by
    simpa [prefixWord, tailWord_2693516, baseEnd_2693516] using wordTrace_append hprefix tailTrace_2693516
  have hstable : (prefixWord ++ tailWord_2693516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693516).length < 2 ^ (prefixWord ++ tailWord_2693516).sum := by decide
  have hdescent : baseEnd_2693516 < baseStart_2693516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693530 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2693530 : Nat := 118140960795 + 2693530 * 2 ^ 59
def prefixEnd_2693530 : Nat := 4983230072969 + 3 ^ 40 * 2693530 * 2
def baseEnd_2693530 : Nat := 1383075547304951785187687

theorem tailTrace_2693530 : CollatzResearch.WordTrace tailWord_2693530 prefixEnd_2693530 1383075547304951785187687 := by
  unfold tailWord_2693530
  simp only [CollatzResearch.WordTrace]
  refine ⟨24560277482952075786295511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65494073287872202096788029 24560277482952075786295511)
  ·
    refine ⟨36840416224428113679443267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24560277482952075786295511 36840416224428113679443267)
    ·
      refine ⟨55260624336642170519164901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36840416224428113679443267 55260624336642170519164901)
      ·
        refine ⟨10361367063120406972343419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55260624336642170519164901 10361367063120406972343419)
        ·
          refine ⟨15542050594680610458515129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10361367063120406972343419 15542050594680610458515129)
          ·
            refine ⟨11656537946010457843886347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15542050594680610458515129 11656537946010457843886347)
            ·
              refine ⟨17484806919015686765829521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11656537946010457843886347 17484806919015686765829521)
              ·
                refine ⟨13113605189261765074372141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17484806919015686765829521 13113605189261765074372141)
                ·
                  refine ⟨4917601945973161902889553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13113605189261765074372141 4917601945973161902889553)
                  ·
                    refine ⟨3688201459479871427167165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4917601945973161902889553 3688201459479871427167165)
                    ·
                      refine ⟨1383075547304951785187687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3688201459479871427167165 1383075547304951785187687)
                      ·
                        rfl

theorem cell23_2693530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2693530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693530 prefixEnd_2693530 := by exact prefixLift 2693530
  have htrace : WordTrace (prefixWord ++ tailWord_2693530) baseStart_2693530 baseEnd_2693530 := by
    simpa [prefixWord, tailWord_2693530, baseEnd_2693530] using wordTrace_append hprefix tailTrace_2693530
  have hstable : (prefixWord ++ tailWord_2693530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693530).length < 2 ^ (prefixWord ++ tailWord_2693530).sum := by decide
  have hdescent : baseEnd_2693530 < baseStart_2693530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693537 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 1, 6]
def baseStart_2693537 : Nat := 118140960795 + 2693537 * 2 ^ 59
def prefixEnd_2693537 : Nat := 4983230072969 + 3 ^ 40 * 2693537 * 2
def baseEnd_2693537 : Nat := 461026380556511085933385

theorem tailTrace_2693537 : CollatzResearch.WordTrace tailWord_2693537 prefixEnd_2693537 461026380556511085933385 := by
  unfold tailWord_2693537
  simp only [CollatzResearch.WordTrace]
  refine ⟨98241365242782943340686865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65494243495188628893791243 98241365242782943340686865)
  ·
    refine ⟨73681023932087207505515149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98241365242782943340686865 73681023932087207505515149)
    ·
      refine ⟨27630383974532702814568181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73681023932087207505515149 27630383974532702814568181)
      ·
        refine ⟨2590348497612440888865767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27630383974532702814568181 2590348497612440888865767)
        ·
          refine ⟨3885522746418661333298651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590348497612440888865767 3885522746418661333298651)
          ·
            refine ⟨5828284119627991999947977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3885522746418661333298651 5828284119627991999947977)
            ·
              refine ⟨4371213089720993999960983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5828284119627991999947977 4371213089720993999960983)
              ·
                refine ⟨6556819634581490999941475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4371213089720993999960983 6556819634581490999941475)
                ·
                  refine ⟨9835229451872236499912213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6556819634581490999941475 9835229451872236499912213)
                  ·
                    refine ⟨461026380556511085933385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9835229451872236499912213 461026380556511085933385)
                    ·
                      rfl

theorem cell23_2693537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_2693537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693537 prefixEnd_2693537 := by exact prefixLift 2693537
  have htrace : WordTrace (prefixWord ++ tailWord_2693537) baseStart_2693537 baseEnd_2693537 := by
    simpa [prefixWord, tailWord_2693537, baseEnd_2693537] using wordTrace_append hprefix tailTrace_2693537
  have hstable : (prefixWord ++ tailWord_2693537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693537).length < 2 ^ (prefixWord ++ tailWord_2693537).sum := by decide
  have hdescent : baseEnd_2693537 < baseStart_2693537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693544 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_2693544 : Nat := 118140960795 + 2693544 * 2 ^ 59
def prefixEnd_2693544 : Nat := 4983230072969 + 3 ^ 40 * 2693544 * 2
def baseEnd_2693544 : Nat := 1383082736034114730412623

theorem tailTrace_2693544 : CollatzResearch.WordTrace tailWord_2693544 prefixEnd_2693544 1383082736034114730412623 := by
  unfold tailWord_2693544
  simp only [CollatzResearch.WordTrace]
  refine ⟨49120810276878791768095843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65494413702505055690794457 49120810276878791768095843)
  ·
    refine ⟨73681215415318187652143765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49120810276878791768095843 73681215415318187652143765)
    ·
      refine ⟨3453806972593040046194239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73681215415318187652143765 3453806972593040046194239)
      ·
        refine ⟨5180710458889560069291359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3453806972593040046194239 5180710458889560069291359)
        ·
          refine ⟨7771065688334340103937039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5180710458889560069291359 7771065688334340103937039)
          ·
            refine ⟨11656598532501510155905559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7771065688334340103937039 11656598532501510155905559)
            ·
              refine ⟨17484897798752265233858339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11656598532501510155905559 17484897798752265233858339)
              ·
                refine ⟨26227346698128397850787509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17484897798752265233858339 26227346698128397850787509)
                ·
                  refine ⟨2458813752949537298511329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26227346698128397850787509 2458813752949537298511329)
                  ·
                    refine ⟨1844110314712152973883497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2458813752949537298511329 1844110314712152973883497)
                    ·
                      refine ⟨1383082736034114730412623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844110314712152973883497 1383082736034114730412623)
                      ·
                        rfl

theorem cell23_2693544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_2693544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693544 prefixEnd_2693544 := by exact prefixLift 2693544
  have htrace : WordTrace (prefixWord ++ tailWord_2693544) baseStart_2693544 baseEnd_2693544 := by
    simpa [prefixWord, tailWord_2693544, baseEnd_2693544] using wordTrace_append hprefix tailTrace_2693544
  have hstable : (prefixWord ++ tailWord_2693544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693544).length < 2 ^ (prefixWord ++ tailWord_2693544).sum := by decide
  have hdescent : baseEnd_2693544 < baseStart_2693544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693560 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 4, 1, 3]
def baseStart_2693560 : Nat := 118140960795 + 2693560 * 2 ^ 59
def prefixEnd_2693560 : Nat := 4983230072969 + 3 ^ 40 * 2693560 * 2
def baseEnd_2693560 : Nat := 1383090951724586667812549

theorem tailTrace_2693560 : CollatzResearch.WordTrace tailWord_2693560 prefixEnd_2693560 1383090951724586667812549 := by
  unfold tailWord_2693560
  simp only [CollatzResearch.WordTrace]
  refine ⟨49121102060849809134387067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65494802747799745512516089 49121102060849809134387067)
  ·
    refine ⟨73681653091274713701580601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49121102060849809134387067 73681653091274713701580601)
    ·
      refine ⟨55261239818456035276185451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73681653091274713701580601 55261239818456035276185451)
      ·
        refine ⟨82891859727684052914278177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55261239818456035276185451 82891859727684052914278177)
        ·
          refine ⟨62168894795763039685708633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82891859727684052914278177 62168894795763039685708633)
          ·
            refine ⟨46626671096822279764281475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62168894795763039685708633 46626671096822279764281475)
            ·
              refine ⟨69940006645233419646422213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46626671096822279764281475 69940006645233419646422213)
              ·
                refine ⟨13113751245981266183704165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69940006645233419646422213 13113751245981266183704165)
                ·
                  refine ⟨2458828358621487409444531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13113751245981266183704165 2458828358621487409444531)
                  ·
                    refine ⟨3688242537932231114166797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2458828358621487409444531 3688242537932231114166797)
                    ·
                      refine ⟨1383090951724586667812549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3688242537932231114166797 1383090951724586667812549)
                      ·
                        rfl

theorem cell23_2693560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_2693560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693560 prefixEnd_2693560 := by exact prefixLift 2693560
  have htrace : WordTrace (prefixWord ++ tailWord_2693560) baseStart_2693560 baseEnd_2693560 := by
    simpa [prefixWord, tailWord_2693560, baseEnd_2693560] using wordTrace_append hprefix tailTrace_2693560
  have hstable : (prefixWord ++ tailWord_2693560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693560).length < 2 ^ (prefixWord ++ tailWord_2693560).sum := by decide
  have hdescent : baseEnd_2693560 < baseStart_2693560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693561 : List Nat := [1, 2, 1, 4, 3, 2, 2, 3, 1, 2, 2]
def baseStart_2693561 : Nat := 118140960795 + 2693561 * 2 ^ 59
def prefixEnd_2693561 : Nat := 4983230072969 + 3 ^ 40 * 2693561 * 2
def baseEnd_2693561 : Nat := 1383091465205241163900045

theorem tailTrace_2693561 : CollatzResearch.WordTrace tailWord_2693561 prefixEnd_2693561 1383091465205241163900045 := by
  unfold tailWord_2693561
  simp only [CollatzResearch.WordTrace]
  refine ⟨98242240594695995439560537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65494827063130663626373691 98242240594695995439560537)
  ·
    refine ⟨73681680446021996579670403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98242240594695995439560537 73681680446021996579670403)
    ·
      refine ⟨110522520669032994869505605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73681680446021996579670403 110522520669032994869505605)
      ·
        refine ⟨20722972625443686538032301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110522520669032994869505605 20722972625443686538032301)
        ·
          refine ⟨7771114734541382451762113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20722972625443686538032301 7771114734541382451762113)
          ·
            refine ⟨5828336050906036838821585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7771114734541382451762113 5828336050906036838821585)
            ·
              refine ⟨4371252038179527629116189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5828336050906036838821585 4371252038179527629116189)
              ·
                refine ⟨1639219514317322860918571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4371252038179527629116189 1639219514317322860918571)
                ·
                  refine ⟨2458829271475984291377857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639219514317322860918571 2458829271475984291377857)
                  ·
                    refine ⟨1844121953606988218533393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2458829271475984291377857 1844121953606988218533393)
                    ·
                      refine ⟨1383091465205241163900045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844121953606988218533393 1383091465205241163900045)
                      ·
                        rfl

theorem cell23_2693561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_2693561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693561 prefixEnd_2693561 := by exact prefixLift 2693561
  have htrace : WordTrace (prefixWord ++ tailWord_2693561) baseStart_2693561 baseEnd_2693561 := by
    simpa [prefixWord, tailWord_2693561, baseEnd_2693561] using wordTrace_append hprefix tailTrace_2693561
  have hstable : (prefixWord ++ tailWord_2693561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693561).length < 2 ^ (prefixWord ++ tailWord_2693561).sum := by decide
  have hdescent : baseEnd_2693561 < baseStart_2693561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693564 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2693564 : Nat := 118140960795 + 2693564 * 2 ^ 59
def prefixEnd_2693564 : Nat := 4983230072969 + 3 ^ 40 * 2693564 * 2
def baseEnd_2693564 : Nat := 1383093005647204652162531

theorem tailTrace_2693564 : CollatzResearch.WordTrace tailWord_2693564 prefixEnd_2693564 1383093005647204652162531 := by
  unfold tailWord_2693564
  simp only [CollatzResearch.WordTrace]
  refine ⟨49121175006842563475959873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65494900009123417967946497 49121175006842563475959873)
  ·
    refine ⟨36840881255131922606969905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49121175006842563475959873 36840881255131922606969905)
    ·
      refine ⟨27630660941348941955227429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36840881255131922606969905 27630660941348941955227429)
      ·
        refine ⟨5180748926502926616605143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27630660941348941955227429 5180748926502926616605143)
        ·
          refine ⟨7771123389754389924907715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5180748926502926616605143 7771123389754389924907715)
          ·
            refine ⟨11656685084631584887361573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7771123389754389924907715 11656685084631584887361573)
            ·
              refine ⟨2185628453368422166380295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11656685084631584887361573 2185628453368422166380295)
              ·
                refine ⟨3278442680052633249570443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185628453368422166380295 3278442680052633249570443)
                ·
                  refine ⟨4917664020078949874355665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278442680052633249570443 4917664020078949874355665)
                  ·
                    refine ⟨3688248015059212405766749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4917664020078949874355665 3688248015059212405766749)
                    ·
                      refine ⟨1383093005647204652162531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3688248015059212405766749 1383093005647204652162531)
                      ·
                        rfl

theorem cell23_2693564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2693564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693564 prefixEnd_2693564 := by exact prefixLift 2693564
  have htrace : WordTrace (prefixWord ++ tailWord_2693564) baseStart_2693564 baseEnd_2693564 := by
    simpa [prefixWord, tailWord_2693564, baseEnd_2693564] using wordTrace_append hprefix tailTrace_2693564
  have hstable : (prefixWord ++ tailWord_2693564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693564).length < 2 ^ (prefixWord ++ tailWord_2693564).sum := by decide
  have hdescent : baseEnd_2693564 < baseStart_2693564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693577 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 2, 1, 3]
def baseStart_2693577 : Nat := 118140960795 + 2693577 * 2 ^ 59
def prefixEnd_2693577 : Nat := 4983230072969 + 3 ^ 40 * 2693577 * 2
def baseEnd_2693577 : Nat := 1383099680895713101299971

theorem tailTrace_2693577 : CollatzResearch.WordTrace tailWord_2693577 prefixEnd_2693577 1383099680895713101299971 := by
  unfold tailWord_2693577
  simp only [CollatzResearch.WordTrace]
  refine ⟨98242824162638030172142985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65495216108425353448095323 98242824162638030172142985)
  ·
    refine ⟨73682118121978522629107239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98242824162638030172142985 73682118121978522629107239)
    ·
      refine ⟨110523177182967783943660859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73682118121978522629107239 110523177182967783943660859)
      ·
        refine ⟨165784765774451675915491289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110523177182967783943660859 165784765774451675915491289)
        ·
          refine ⟨124338574330838756936618467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165784765774451675915491289 124338574330838756936618467)
          ·
            refine ⟨186507861496258135404927701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124338574330838756936618467 186507861496258135404927701)
            ·
              refine ⟨4371278003818550048552993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 186507861496258135404927701 4371278003818550048552993)
              ·
                refine ⟨3278458502863912536414745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4371278003818550048552993 3278458502863912536414745)
                ·
                  refine ⟨2458843877147934402311059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3278458502863912536414745 2458843877147934402311059)
                  ·
                    refine ⟨3688265815721901603466589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2458843877147934402311059 3688265815721901603466589)
                    ·
                      refine ⟨1383099680895713101299971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3688265815721901603466589 1383099680895713101299971)
                      ·
                        rfl

theorem cell23_2693577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 1, 3].length) (baseStart_2693577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693577 prefixEnd_2693577 := by exact prefixLift 2693577
  have htrace : WordTrace (prefixWord ++ tailWord_2693577) baseStart_2693577 baseEnd_2693577 := by
    simpa [prefixWord, tailWord_2693577, baseEnd_2693577] using wordTrace_append hprefix tailTrace_2693577
  have hstable : (prefixWord ++ tailWord_2693577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693577).length < 2 ^ (prefixWord ++ tailWord_2693577).sum := by decide
  have hdescent : baseEnd_2693577 < baseStart_2693577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693593 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 2, 6]
def baseStart_2693593 : Nat := 118140960795 + 2693593 * 2 ^ 59
def prefixEnd_2693593 : Nat := 4983230072969 + 3 ^ 40 * 2693593 * 2
def baseEnd_2693593 : Nat := 461035965528728346233299

theorem tailTrace_2693593 : CollatzResearch.WordTrace tailWord_2693593 prefixEnd_2693593 461035965528728346233299 := by
  unfold tailWord_2693593
  simp only [CollatzResearch.WordTrace]
  refine ⟨98243407730580064904725433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65495605153720043269816955 98243407730580064904725433)
  ·
    refine ⟨73682555797935048678544075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98243407730580064904725433 73682555797935048678544075)
    ·
      refine ⟨110523833696902573017816113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73682555797935048678544075 110523833696902573017816113)
      ·
        refine ⟨82892875272676929763362085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110523833696902573017816113 82892875272676929763362085)
        ·
          refine ⟨15542414113626924330630391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82892875272676929763362085 15542414113626924330630391)
          ·
            refine ⟨23313621170440386495945587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15542414113626924330630391 23313621170440386495945587)
            ·
              refine ⟨34970431755660579743918381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23313621170440386495945587 34970431755660579743918381)
              ·
                refine ⟨13113911908372717403969393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34970431755660579743918381 13113911908372717403969393)
                ·
                  refine ⟨9835433931279538052977045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13113911908372717403969393 9835433931279538052977045)
                  ·
                    refine ⟨461035965528728346233299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9835433931279538052977045 461035965528728346233299)
                    ·
                      rfl

theorem cell23_2693593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_2693593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693593 prefixEnd_2693593 := by exact prefixLift 2693593
  have htrace : WordTrace (prefixWord ++ tailWord_2693593) baseStart_2693593 baseEnd_2693593 := by
    simpa [prefixWord, tailWord_2693593, baseEnd_2693593] using wordTrace_append hprefix tailTrace_2693593
  have hstable : (prefixWord ++ tailWord_2693593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693593).length < 2 ^ (prefixWord ++ tailWord_2693593).sum := by decide
  have hdescent : baseEnd_2693593 < baseStart_2693593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693594 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3]
def baseStart_2693594 : Nat := 118140960795 + 2693594 * 2 ^ 59
def prefixEnd_2693594 : Nat := 4983230072969 + 3 ^ 40 * 2693594 * 2
def baseEnd_2693594 : Nat := 1383108410066839534787393

theorem tailTrace_2693594 : CollatzResearch.WordTrace tailWord_2693594 prefixEnd_2693594 1383108410066839534787393 := by
  unfold tailWord_2693594
  simp only [CollatzResearch.WordTrace]
  refine ⟨24560861050894110518877959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65495629469050961383674557 24560861050894110518877959)
  ·
    refine ⟨36841291576341165778316939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24560861050894110518877959 36841291576341165778316939)
    ·
      refine ⟨55261937364511748667475409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36841291576341165778316939 55261937364511748667475409)
      ·
        refine ⟨41446453023383811500606557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55261937364511748667475409 41446453023383811500606557)
        ·
          refine ⟨15542419883768929312727459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41446453023383811500606557 15542419883768929312727459)
          ·
            refine ⟨23313629825653393969091189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15542419883768929312727459 23313629825653393969091189)
            ·
              refine ⟨2185652796155005684602299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23313629825653393969091189 2185652796155005684602299)
              ·
                refine ⟨3278479194232508526903449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185652796155005684602299 3278479194232508526903449)
                ·
                  refine ⟨2458859395674381395177587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3278479194232508526903449 2458859395674381395177587)
                  ·
                    refine ⟨3688289093511572092766381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2458859395674381395177587 3688289093511572092766381)
                    ·
                      refine ⟨1383108410066839534787393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3688289093511572092766381 1383108410066839534787393)
                      ·
                        rfl

theorem cell23_2693594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_2693594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693594 prefixEnd_2693594 := by exact prefixLift 2693594
  have htrace : WordTrace (prefixWord ++ tailWord_2693594) baseStart_2693594 baseEnd_2693594 := by
    simpa [prefixWord, tailWord_2693594, baseEnd_2693594] using wordTrace_append hprefix tailTrace_2693594
  have hstable : (prefixWord ++ tailWord_2693594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693594).length < 2 ^ (prefixWord ++ tailWord_2693594).sum := by decide
  have hdescent : baseEnd_2693594 < baseStart_2693594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693617 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 6, 2, 2]
def baseStart_2693617 : Nat := 118140960795 + 2693617 * 2 ^ 59
def prefixEnd_2693617 : Nat := 4983230072969 + 3 ^ 40 * 2693617 * 2
def baseEnd_2693617 : Nat := 1383120220121892944799787

theorem tailTrace_2693617 : CollatzResearch.WordTrace tailWord_2693617 prefixEnd_2693617 1383120220121892944799787 := by
  unfold tailWord_2693617
  simp only [CollatzResearch.WordTrace]
  refine ⟨98244283082493117003599105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65496188721662078002399403 98244283082493117003599105)
  ·
    refine ⟨73683212311869837752699329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98244283082493117003599105 73683212311869837752699329)
    ·
      refine ⟨55262409233902378314524497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73683212311869837752699329 55262409233902378314524497)
      ·
        refine ⟨41446806925426783735893373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55262409233902378314524497 41446806925426783735893373)
        ·
          refine ⟨15542552597035043900960015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41446806925426783735893373 15542552597035043900960015)
          ·
            refine ⟨23313828895552565851440023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15542552597035043900960015 23313828895552565851440023)
            ·
              refine ⟨34970743343328848777160035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23313828895552565851440023 34970743343328848777160035)
              ·
                refine ⟨52456115014993273165740053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34970743343328848777160035 52456115014993273165740053)
                ·
                  refine ⟨2458880391327809679644065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52456115014993273165740053 2458880391327809679644065)
                  ·
                    refine ⟨1844160293495857259733049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2458880391327809679644065 1844160293495857259733049)
                    ·
                      refine ⟨1383120220121892944799787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844160293495857259733049 1383120220121892944799787)
                      ·
                        rfl

theorem cell23_2693617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_2693617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693617 prefixEnd_2693617 := by exact prefixLift 2693617
  have htrace : WordTrace (prefixWord ++ tailWord_2693617) baseStart_2693617 baseEnd_2693617 := by
    simpa [prefixWord, tailWord_2693617, baseEnd_2693617] using wordTrace_append hprefix tailTrace_2693617
  have hstable : (prefixWord ++ tailWord_2693617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693617).length < 2 ^ (prefixWord ++ tailWord_2693617).sum := by decide
  have hdescent : baseEnd_2693617 < baseStart_2693617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693645 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_2693645 : Nat := 118140960795 + 2693645 * 2 ^ 59
def prefixEnd_2693645 : Nat := 4983230072969 + 3 ^ 40 * 2693645 * 2
def baseEnd_2693645 : Nat := 1383134597580218835249659

theorem tailTrace_2693645 : CollatzResearch.WordTrace tailWord_2693645 prefixEnd_2693645 1383134597580218835249659 := by
  unfold tailWord_2693645
  simp only [CollatzResearch.WordTrace]
  refine ⟨98245304326391677785618389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65496869550927785190412259 98245304326391677785618389)
  ·
    refine ⟨2302624320149804948100431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 98245304326391677785618389 2302624320149804948100431)
    ·
      refine ⟨3453936480224707422150647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2302624320149804948100431 3453936480224707422150647)
      ·
        refine ⟨5180904720337061133225971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3453936480224707422150647 5180904720337061133225971)
        ·
          refine ⟨7771357080505591699838957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5180904720337061133225971 7771357080505591699838957)
          ·
            refine ⟨2914258905189596887439609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7771357080505591699838957 2914258905189596887439609)
            ·
              refine ⟨2185694178892197665579707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2914258905189596887439609 2185694178892197665579707)
              ·
                refine ⟨3278541268338296498369561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185694178892197665579707 3278541268338296498369561)
                ·
                  refine ⟨2458905951253722373777171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3278541268338296498369561 2458905951253722373777171)
                  ·
                    refine ⟨3688358926880583560665757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2458905951253722373777171 3688358926880583560665757)
                    ·
                      refine ⟨1383134597580218835249659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3688358926880583560665757 1383134597580218835249659)
                      ·
                        rfl

theorem cell23_2693645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_2693645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693645 prefixEnd_2693645 := by exact prefixLift 2693645
  have htrace : WordTrace (prefixWord ++ tailWord_2693645) baseStart_2693645 baseEnd_2693645 := by
    simpa [prefixWord, tailWord_2693645, baseEnd_2693645] using wordTrace_append hprefix tailTrace_2693645
  have hstable : (prefixWord ++ tailWord_2693645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693645).length < 2 ^ (prefixWord ++ tailWord_2693645).sum := by decide
  have hdescent : baseEnd_2693645 < baseStart_2693645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693663 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_2693663 : Nat := 118140960795 + 2693663 * 2 ^ 59
def prefixEnd_2693663 : Nat := 4983230072969 + 3 ^ 40 * 2693663 * 2
def baseEnd_2693663 : Nat := 1383143840231999764824575

theorem tailTrace_2693663 : CollatzResearch.WordTrace tailWord_2693663 prefixEnd_2693663 1383143840231999764824575 := by
  unfold tailWord_2693663
  simp only [CollatzResearch.WordTrace]
  refine ⟨98245960840326466859773643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65497307226884311239849095 98245960840326466859773643)
  ·
    refine ⟨147368941260489700289660465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98245960840326466859773643 147368941260489700289660465)
    ·
      refine ⟨110526705945367275217245349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147368941260489700289660465 110526705945367275217245349)
      ·
        refine ⟨20723757364756364103233503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110526705945367275217245349 20723757364756364103233503)
        ·
          refine ⟨31085636047134546154850255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20723757364756364103233503 31085636047134546154850255)
          ·
            refine ⟨46628454070701819232275383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31085636047134546154850255 46628454070701819232275383)
            ·
              refine ⟨69942681106052728848413075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46628454070701819232275383 69942681106052728848413075)
              ·
                refine ⟨104914021659079093272619613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69942681106052728848413075 104914021659079093272619613)
                ·
                  refine ⟨39342758122154659977232355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104914021659079093272619613 39342758122154659977232355)
                  ·
                    refine ⟨59014137183231989965848533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39342758122154659977232355 59014137183231989965848533)
                    ·
                      refine ⟨1383143840231999764824575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59014137183231989965848533 1383143840231999764824575)
                      ·
                        rfl

theorem cell23_2693663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_2693663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693663 prefixEnd_2693663 := by exact prefixLift 2693663
  have htrace : WordTrace (prefixWord ++ tailWord_2693663) baseStart_2693663 baseEnd_2693663 := by
    simpa [prefixWord, tailWord_2693663, baseEnd_2693663] using wordTrace_append hprefix tailTrace_2693663
  have hstable : (prefixWord ++ tailWord_2693663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693663).length < 2 ^ (prefixWord ++ tailWord_2693663).sum := by decide
  have hdescent : baseEnd_2693663 < baseStart_2693663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693764 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 6]
def baseStart_2693764 : Nat := 118140960795 + 2693764 * 2 ^ 59
def prefixEnd_2693764 : Nat := 4983230072969 + 3 ^ 40 * 2693764 * 2
def baseEnd_2693764 : Nat := 153688411308678207740179

theorem tailTrace_2693764 : CollatzResearch.WordTrace tailWord_2693764 prefixEnd_2693764 153688411308678207740179 := by
  unfold tailWord_2693764
  simp only [CollatzResearch.WordTrace]
  refine ⟨49124822306480280554600173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65499763075307040739466897 49124822306480280554600173)
  ·
    refine ⟨18421808364930105207975065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49124822306480280554600173 18421808364930105207975065)
    ·
      refine ⟨13816356273697578905981299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18421808364930105207975065 13816356273697578905981299)
      ·
        refine ⟨20724534410546368358971949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13816356273697578905981299 20724534410546368358971949)
        ·
          refine ⟨7771700403954888134614481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20724534410546368358971949 7771700403954888134614481)
          ·
            refine ⟨5828775302966166100960861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7771700403954888134614481 5828775302966166100960861)
            ·
              refine ⟨2185790738612312287860323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5828775302966166100960861 2185790738612312287860323)
              ·
                refine ⟨3278686107918468431790485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185790738612312287860323 3278686107918468431790485)
                ·
                  refine ⟨153688411308678207740179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3278686107918468431790485 153688411308678207740179)
                  ·
                    rfl

theorem cell23_2693764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_2693764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693764 prefixEnd_2693764 := by exact prefixLift 2693764
  have htrace : WordTrace (prefixWord ++ tailWord_2693764) baseStart_2693764 baseEnd_2693764 := by
    simpa [prefixWord, tailWord_2693764, baseEnd_2693764] using wordTrace_append hprefix tailTrace_2693764
  have hstable : (prefixWord ++ tailWord_2693764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693764).length < 2 ^ (prefixWord ++ tailWord_2693764).sum := by decide
  have hdescent : baseEnd_2693764 < baseStart_2693764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693767 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 3, 5, 2]
def baseStart_2693767 : Nat := 118140960795 + 2693767 * 2 ^ 59
def prefixEnd_2693767 : Nat := 4983230072969 + 3 ^ 40 * 2693767 * 2
def baseEnd_2693767 : Nat := 1383197242220067357924097

theorem tailTrace_2693767 : CollatzResearch.WordTrace tailWord_2693767 prefixEnd_2693767 1383197242220067357924097 := by
  unfold tailWord_2693767
  simp only [CollatzResearch.WordTrace]
  refine ⟨98249754031949692621559555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65499836021299795081039703 98249754031949692621559555)
  ·
    refine ⟨147374631047924538932339333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98249754031949692621559555 147374631047924538932339333)
    ·
      refine ⟨27632743321485851049813625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147374631047924538932339333 27632743321485851049813625)
      ·
        refine ⟨20724557491114388287360219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27632743321485851049813625 20724557491114388287360219)
        ·
          refine ⟨31086836236671582431040329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20724557491114388287360219 31086836236671582431040329)
          ·
            refine ⟨23315127177503686823280247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31086836236671582431040329 23315127177503686823280247)
            ·
              refine ⟨34972690766255530234920371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23315127177503686823280247 34972690766255530234920371)
              ·
                refine ⟨52459036149383295352380557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34972690766255530234920371 52459036149383295352380557)
                ·
                  refine ⟨19672138556018735757142709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52459036149383295352380557 19672138556018735757142709)
                  ·
                    refine ⟨1844262989626756477232129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19672138556018735757142709 1844262989626756477232129)
                    ·
                      refine ⟨1383197242220067357924097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844262989626756477232129 1383197242220067357924097)
                      ·
                        rfl

theorem cell23_2693767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_2693767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693767 prefixEnd_2693767 := by exact prefixLift 2693767
  have htrace : WordTrace (prefixWord ++ tailWord_2693767) baseStart_2693767 baseEnd_2693767 := by
    simpa [prefixWord, tailWord_2693767, baseEnd_2693767] using wordTrace_append hprefix tailTrace_2693767
  have hstable : (prefixWord ++ tailWord_2693767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693767).length < 2 ^ (prefixWord ++ tailWord_2693767).sum := by decide
  have hdescent : baseEnd_2693767 < baseStart_2693767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693774 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2693774 : Nat := 118140960795 + 2693774 * 2 ^ 59
def prefixEnd_2693774 : Nat := 4983230072969 + 3 ^ 40 * 2693774 * 2
def baseEnd_2693774 : Nat := 1383200836584648830536565

theorem tailTrace_2693774 : CollatzResearch.WordTrace tailWord_2693774 prefixEnd_2693774 1383200836584648830536565 := by
  unfold tailWord_2693774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12281251167865541602133047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65500006228616221878042917 12281251167865541602133047)
  ·
    refine ⟨18421876751798312403199571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12281251167865541602133047 18421876751798312403199571)
    ·
      refine ⟨27632815127697468604799357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18421876751798312403199571 27632815127697468604799357)
      ·
        refine ⟨10362305672886550726799759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27632815127697468604799357 10362305672886550726799759)
        ·
          refine ⟨15543458509329826090199639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10362305672886550726799759 15543458509329826090199639)
          ·
            refine ⟨23315187763994739135299459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15543458509329826090199639 23315187763994739135299459)
            ·
              refine ⟨34972781645992108702949189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23315187763994739135299459 34972781645992108702949189)
              ·
                refine ⟨6557396558623520381802973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34972781645992108702949189 6557396558623520381802973)
                ·
                  refine ⟨2459023709483820143176115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6557396558623520381802973 2459023709483820143176115)
                  ·
                    refine ⟨3688535564225730214764173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2459023709483820143176115 3688535564225730214764173)
                    ·
                      refine ⟨1383200836584648830536565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3688535564225730214764173 1383200836584648830536565)
                      ·
                        rfl

theorem cell23_2693774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2693774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693774 prefixEnd_2693774 := by exact prefixLift 2693774
  have htrace : WordTrace (prefixWord ++ tailWord_2693774) baseStart_2693774 baseEnd_2693774 := by
    simpa [prefixWord, tailWord_2693774, baseEnd_2693774] using wordTrace_append hprefix tailTrace_2693774
  have hstable : (prefixWord ++ tailWord_2693774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693774).length < 2 ^ (prefixWord ++ tailWord_2693774).sum := by decide
  have hdescent : baseEnd_2693774 < baseStart_2693774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693784 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 2, 3, 2]
def baseStart_2693784 : Nat := 118140960795 + 2693784 * 2 ^ 59
def prefixEnd_2693784 : Nat := 4983230072969 + 3 ^ 40 * 2693784 * 2
def baseEnd_2693784 : Nat := 1383205971391193791411519

theorem tailTrace_2693784 : CollatzResearch.WordTrace tailWord_2693784 prefixEnd_2693784 1383205971391193791411519 := by
  unfold tailWord_2693784
  simp only [CollatzResearch.WordTrace]
  refine ⟨49125187036444052262464203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65500249381925403016618937 49125187036444052262464203)
  ·
    refine ⟨73687780554666078393696305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49125187036444052262464203 73687780554666078393696305)
    ·
      refine ⟨55265835415999558795272229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73687780554666078393696305 55265835415999558795272229)
      ·
        refine ⟨10362344140499917274113543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55265835415999558795272229 10362344140499917274113543)
        ·
          refine ⟨15543516210749875911170315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10362344140499917274113543 15543516210749875911170315)
          ·
            refine ⟨23315274316124813866755473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15543516210749875911170315 23315274316124813866755473)
            ·
              refine ⟨17486455737093610400066605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23315274316124813866755473 17486455737093610400066605)
              ·
                refine ⟨6557420901410103900024977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17486455737093610400066605 6557420901410103900024977)
                ·
                  refine ⟨4918065676057577925018733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6557420901410103900024977 4918065676057577925018733)
                  ·
                    refine ⟨1844274628521591721882025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4918065676057577925018733 1844274628521591721882025)
                    ·
                      refine ⟨1383205971391193791411519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844274628521591721882025 1383205971391193791411519)
                      ·
                        rfl

theorem cell23_2693784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_2693784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693784 prefixEnd_2693784 := by exact prefixLift 2693784
  have htrace : WordTrace (prefixWord ++ tailWord_2693784) baseStart_2693784 baseEnd_2693784 := by
    simpa [prefixWord, tailWord_2693784, baseEnd_2693784] using wordTrace_append hprefix tailTrace_2693784
  have hstable : (prefixWord ++ tailWord_2693784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693784).length < 2 ^ (prefixWord ++ tailWord_2693784).sum := by decide
  have hdescent : baseEnd_2693784 < baseStart_2693784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693807 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 4, 4]
def baseStart_2693807 : Nat := 118140960795 + 2693807 * 2 ^ 59
def prefixEnd_2693807 : Nat := 4983230072969 + 3 ^ 40 * 2693807 * 2
def baseEnd_2693807 : Nat := 461072593815415733807971

theorem tailTrace_2693807 : CollatzResearch.WordTrace tailWord_2693807 prefixEnd_2693807 461072593815415733807971 := by
  unfold tailWord_2693807
  simp only [CollatzResearch.WordTrace]
  refine ⟨98251212951804779453015675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65500808634536519635343783 98251212951804779453015675)
  ·
    refine ⟨147376819427707169179523513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98251212951804779453015675 147376819427707169179523513)
    ·
      refine ⟨110532614570780376884642635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147376819427707169179523513 110532614570780376884642635)
      ·
        refine ⟨165798921856170565326963953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110532614570780376884642635 165798921856170565326963953)
        ·
          refine ⟨124349191392127923995222965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165798921856170565326963953 124349191392127923995222965)
          ·
            refine ⟨11657736693011992874552153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124349191392127923995222965 11657736693011992874552153)
            ·
              refine ⟨8743302519758994655914115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11657736693011992874552153 8743302519758994655914115)
              ·
                refine ⟨13114953779638491983871173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8743302519758994655914115 13114953779638491983871173)
                ·
                  refine ⟨2459053833682217246975845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13114953779638491983871173 2459053833682217246975845)
                  ·
                    refine ⟨461072593815415733807971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2459053833682217246975845 461072593815415733807971)
                    ·
                      rfl

theorem cell23_2693807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 4].length) (baseStart_2693807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693807 prefixEnd_2693807 := by exact prefixLift 2693807
  have htrace : WordTrace (prefixWord ++ tailWord_2693807) baseStart_2693807 baseEnd_2693807 := by
    simpa [prefixWord, tailWord_2693807, baseEnd_2693807] using wordTrace_append hprefix tailTrace_2693807
  have hstable : (prefixWord ++ tailWord_2693807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693807).length < 2 ^ (prefixWord ++ tailWord_2693807).sum := by decide
  have hdescent : baseEnd_2693807 < baseStart_2693807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693817 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2693817 : Nat := 118140960795 + 2693817 * 2 ^ 59
def prefixEnd_2693817 : Nat := 4983230072969 + 3 ^ 40 * 2693817 * 2
def baseEnd_2693817 : Nat := 1383222916252792162298867

theorem tailTrace_2693817 : CollatzResearch.WordTrace tailWord_2693817 prefixEnd_2693817 1383222916252792162298867 := by
  unfold tailWord_2693817
  simp only [CollatzResearch.WordTrace]
  refine ⟨98251577681768551160879705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65501051787845700773919803 98251577681768551160879705)
  ·
    refine ⟨73688683261326413370659779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98251577681768551160879705 73688683261326413370659779)
    ·
      refine ⟨110533024891989620055989669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73688683261326413370659779 110533024891989620055989669)
      ·
        refine ⟨20724942167248053760498063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110533024891989620055989669 20724942167248053760498063)
        ·
          refine ⟨31087413250872080640747095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20724942167248053760498063 31087413250872080640747095)
          ·
            refine ⟨46631119876308120961120643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31087413250872080640747095 46631119876308120961120643)
            ·
              refine ⟨69946679814462181441680965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46631119876308120961120643 69946679814462181441680965)
              ·
                refine ⟨13115002465211659020315181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69946679814462181441680965 13115002465211659020315181)
                ·
                  refine ⟨4918125924454372132618193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13115002465211659020315181 4918125924454372132618193)
                  ·
                    refine ⟨3688594443340779099463645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4918125924454372132618193 3688594443340779099463645)
                    ·
                      refine ⟨1383222916252792162298867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3688594443340779099463645 1383222916252792162298867)
                      ·
                        rfl

theorem cell23_2693817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2693817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693817 prefixEnd_2693817 := by exact prefixLift 2693817
  have htrace : WordTrace (prefixWord ++ tailWord_2693817) baseStart_2693817 baseEnd_2693817 := by
    simpa [prefixWord, tailWord_2693817, baseEnd_2693817] using wordTrace_append hprefix tailTrace_2693817
  have hstable : (prefixWord ++ tailWord_2693817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693817).length < 2 ^ (prefixWord ++ tailWord_2693817).sum := by decide
  have hdescent : baseEnd_2693817 < baseStart_2693817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693824 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 2, 4]
def baseStart_2693824 : Nat := 118140960795 + 2693824 * 2 ^ 59
def prefixEnd_2693824 : Nat := 4983230072969 + 3 ^ 40 * 2693824 * 2
def baseEnd_2693824 : Nat := 461075503539124544970445

theorem tailTrace_2693824 : CollatzResearch.WordTrace tailWord_2693824 prefixEnd_2693824 461075503539124544970445 := by
  unfold tailWord_2693824
  simp only [CollatzResearch.WordTrace]
  refine ⟨49125916496371595678192263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65501221995162127570923017 49125916496371595678192263)
  ·
    refine ⟨73688874744557393517288395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49125916496371595678192263 73688874744557393517288395)
    ·
      refine ⟨110533312116836090275932593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73688874744557393517288395 110533312116836090275932593)
      ·
        refine ⟨82899984087627067706949445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110533312116836090275932593 82899984087627067706949445)
        ·
          refine ⟨15543747016430075195053021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82899984087627067706949445 15543747016430075195053021)
          ·
            refine ⟨5828905131161278198144883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15543747016430075195053021 5828905131161278198144883)
            ·
              refine ⟨8743357696741917297217325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5828905131161278198144883 8743357696741917297217325)
              ·
                refine ⟨3278759136278218986456497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8743357696741917297217325 3278759136278218986456497)
                ·
                  refine ⟨2459069352208664239842373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3278759136278218986456497 2459069352208664239842373)
                  ·
                    refine ⟨461075503539124544970445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2459069352208664239842373 461075503539124544970445)
                    ·
                      rfl

theorem cell23_2693824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2, 4].length) (baseStart_2693824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693824 prefixEnd_2693824 := by exact prefixLift 2693824
  have htrace : WordTrace (prefixWord ++ tailWord_2693824) baseStart_2693824 baseEnd_2693824 := by
    simpa [prefixWord, tailWord_2693824, baseEnd_2693824] using wordTrace_append hprefix tailTrace_2693824
  have hstable : (prefixWord ++ tailWord_2693824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693824).length < 2 ^ (prefixWord ++ tailWord_2693824).sum := by decide
  have hdescent : baseEnd_2693824 < baseStart_2693824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693834 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_2693834 : Nat := 118140960795 + 2693834 * 2 ^ 59
def prefixEnd_2693834 : Nat := 4983230072969 + 3 ^ 40 * 2693834 * 2
def baseEnd_2693834 : Nat := 1383231645423918595786289

theorem tailTrace_2693834 : CollatzResearch.WordTrace tailWord_2693834 prefixEnd_2693834 1383231645423918595786289 := by
  unfold tailWord_2693834
  simp only [CollatzResearch.WordTrace]
  refine ⟨24563049430676740766062139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65501465148471308709499037 24563049430676740766062139)
  ·
    refine ⟨36844574146015111149093209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24563049430676740766062139 36844574146015111149093209)
    ·
      refine ⟨27633430609511333361819907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36844574146015111149093209 27633430609511333361819907)
      ·
        refine ⟨41450145914267000042729861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27633430609511333361819907 41450145914267000042729861)
        ·
          refine ⟨7771902358925062508011849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41450145914267000042729861 7771902358925062508011849)
          ·
            refine ⟨5828926769193796881008887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7771902358925062508011849 5828926769193796881008887)
            ·
              refine ⟨8743390153790695321513331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5828926769193796881008887 8743390153790695321513331)
              ·
                refine ⟨13115085230686042982269997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8743390153790695321513331 13115085230686042982269997)
                ·
                  refine ⟨4918156961507266118351249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13115085230686042982269997 4918156961507266118351249)
                  ·
                    refine ⟨3688617721130449588763437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4918156961507266118351249 3688617721130449588763437)
                    ·
                      refine ⟨1383231645423918595786289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3688617721130449588763437 1383231645423918595786289)
                      ·
                        rfl

theorem cell23_2693834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_2693834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693834 prefixEnd_2693834 := by exact prefixLift 2693834
  have htrace : WordTrace (prefixWord ++ tailWord_2693834) baseStart_2693834 baseEnd_2693834 := by
    simpa [prefixWord, tailWord_2693834, baseEnd_2693834] using wordTrace_append hprefix tailTrace_2693834
  have hstable : (prefixWord ++ tailWord_2693834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693834).length < 2 ^ (prefixWord ++ tailWord_2693834).sum := by decide
  have hdescent : baseEnd_2693834 < baseStart_2693834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693847 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 3]
def baseStart_2693847 : Nat := 118140960795 + 2693847 * 2 ^ 59
def prefixEnd_2693847 : Nat := 4983230072969 + 3 ^ 40 * 2693847 * 2
def baseEnd_2693847 : Nat := 1383238320672427044923729

theorem tailTrace_2693847 : CollatzResearch.WordTrace tailWord_2693847 prefixEnd_2693847 1383238320672427044923729 := by
  unfold tailWord_2693847
  simp only [CollatzResearch.WordTrace]
  refine ⟨98252671871659866284471795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65501781247773244189647863 98252671871659866284471795)
  ·
    refine ⟨147379007807489799426707693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98252671871659866284471795 147379007807489799426707693)
    ·
      refine ⟨55267127927808674785015385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147379007807489799426707693 55267127927808674785015385)
      ·
        refine ⟨41450345945856506088761539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55267127927808674785015385 41450345945856506088761539)
        ·
          refine ⟨62175518918784759133142309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41450345945856506088761539 62175518918784759133142309)
          ·
            refine ⟨11657909797272142337464183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62175518918784759133142309 11657909797272142337464183)
            ·
              refine ⟨17486864695908213506196275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11657909797272142337464183 17486864695908213506196275)
              ·
                refine ⟨26230297043862320259294413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17486864695908213506196275 26230297043862320259294413)
                ·
                  refine ⟨9836361391448370097235405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26230297043862320259294413 9836361391448370097235405)
                  ·
                    refine ⟨3688635521793138786463277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9836361391448370097235405 3688635521793138786463277)
                    ·
                      refine ⟨1383238320672427044923729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3688635521793138786463277 1383238320672427044923729)
                      ·
                        rfl

theorem cell23_2693847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_2693847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693847 prefixEnd_2693847 := by exact prefixLift 2693847
  have htrace : WordTrace (prefixWord ++ tailWord_2693847) baseStart_2693847 baseEnd_2693847 := by
    simpa [prefixWord, tailWord_2693847, baseEnd_2693847] using wordTrace_append hprefix tailTrace_2693847
  have hstable : (prefixWord ++ tailWord_2693847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693847).length < 2 ^ (prefixWord ++ tailWord_2693847).sum := by decide
  have hdescent : baseEnd_2693847 < baseStart_2693847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693921 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 4, 2, 2]
def baseStart_2693921 : Nat := 118140960795 + 2693921 * 2 ^ 59
def prefixEnd_2693921 : Nat := 4983230072969 + 3 ^ 40 * 2693921 * 2
def baseEnd_2693921 : Nat := 1383276318240859755398389

theorem tailTrace_2693921 : CollatzResearch.WordTrace tailWord_2693921 prefixEnd_2693921 1383276318240859755398389 := by
  unfold tailWord_2693921
  simp only [CollatzResearch.WordTrace]
  refine ⟨98255370873391776922665617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65503580582261184615110411 98255370873391776922665617)
  ·
    refine ⟨73691528155043832691999213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98255370873391776922665617 73691528155043832691999213)
    ·
      refine ⟨27634323058141437259499705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73691528155043832691999213 27634323058141437259499705)
      ·
        refine ⟨20725742293606077944624779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27634323058141437259499705 20725742293606077944624779)
        ·
          refine ⟨31088613440409116916937169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20725742293606077944624779 31088613440409116916937169)
          ·
            refine ⟨23316460080306837687702877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31088613440409116916937169 23316460080306837687702877)
            ·
              refine ⟨8743672530115064132888579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23316460080306837687702877 8743672530115064132888579)
              ·
                refine ⟨13115508795172596199332869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8743672530115064132888579 13115508795172596199332869)
                ·
                  refine ⟨2459157899094861787374913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13115508795172596199332869 2459157899094861787374913)
                  ·
                    refine ⟨1844368424321146340531185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2459157899094861787374913 1844368424321146340531185)
                    ·
                      refine ⟨1383276318240859755398389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844368424321146340531185 1383276318240859755398389)
                      ·
                        rfl

theorem cell23_2693921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_2693921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693921 prefixEnd_2693921 := by exact prefixLift 2693921
  have htrace : WordTrace (prefixWord ++ tailWord_2693921) baseStart_2693921 baseEnd_2693921 := by
    simpa [prefixWord, tailWord_2693921, baseEnd_2693921] using wordTrace_append hprefix tailTrace_2693921
  have hstable : (prefixWord ++ tailWord_2693921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693921).length < 2 ^ (prefixWord ++ tailWord_2693921).sum := by decide
  have hdescent : baseEnd_2693921 < baseStart_2693921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693958 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2693958 : Nat := 118140960795 + 2693958 * 2 ^ 59
def prefixEnd_2693958 : Nat := 4983230072969 + 3 ^ 40 * 2693958 * 2
def baseEnd_2693958 : Nat := 1383295317025076110635719

theorem tailTrace_2693958 : CollatzResearch.WordTrace tailWord_2693958 prefixEnd_2693958 1383295317025076110635719 := by
  unfold tailWord_2693958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070522511695554132555079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65504480249505154827841685 3070522511695554132555079)
  ·
    refine ⟨4605783767543331198832619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3070522511695554132555079 4605783767543331198832619)
    ·
      refine ⟨6908675651314996798248929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4605783767543331198832619 6908675651314996798248929)
      ·
        refine ⟨5181506738486247598686697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6908675651314996798248929 5181506738486247598686697)
        ·
          refine ⟨3886130053864685699015023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5181506738486247598686697 3886130053864685699015023)
          ·
            refine ⟨5829195080797028548522535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3886130053864685699015023 5829195080797028548522535)
            ·
              refine ⟨8743792621195542822783803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5829195080797028548522535 8743792621195542822783803)
              ·
                refine ⟨13115688931793314234175705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8743792621195542822783803 13115688931793314234175705)
                ·
                  refine ⟨9836766698844985675631779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13115688931793314234175705 9836766698844985675631779)
                  ·
                    refine ⟨14755150048267478513447669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9836766698844985675631779 14755150048267478513447669)
                    ·
                      refine ⟨1383295317025076110635719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14755150048267478513447669 1383295317025076110635719)
                      ·
                        rfl

theorem cell23_2693958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2693958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693958 prefixEnd_2693958 := by exact prefixLift 2693958
  have htrace : WordTrace (prefixWord ++ tailWord_2693958) baseStart_2693958 baseEnd_2693958 := by
    simpa [prefixWord, tailWord_2693958, baseEnd_2693958] using wordTrace_append hprefix tailTrace_2693958
  have hstable : (prefixWord ++ tailWord_2693958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693958).length < 2 ^ (prefixWord ++ tailWord_2693958).sum := by decide
  have hdescent : baseEnd_2693958 < baseStart_2693958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693961 : List Nat := [1, 2, 1, 1, 2, 7, 1, 3, 5]
def baseStart_2693961 : Nat := 118140960795 + 2693961 * 2 ^ 59
def prefixEnd_2693961 : Nat := 4983230072969 + 3 ^ 40 * 2693961 * 2
def baseEnd_2693961 : Nat := 153699650829671066544245

theorem tailTrace_2693961 : CollatzResearch.WordTrace tailWord_2693961 prefixEnd_2693961 153699650829671066544245 := by
  unfold tailWord_2693961
  simp only [CollatzResearch.WordTrace]
  refine ⟨98256829793246863754121737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65504553195497909169414491 98256829793246863754121737)
  ·
    refine ⟨73692622344935147815591303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98256829793246863754121737 73692622344935147815591303)
    ·
      refine ⟨110538933517402721723386955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73692622344935147815591303 110538933517402721723386955)
      ·
        refine ⟨165808400276104082585080433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110538933517402721723386955 165808400276104082585080433)
        ·
          refine ⟨124356300207078061938810325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165808400276104082585080433 124356300207078061938810325)
          ·
            refine ⟨2914600786103392076690867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 124356300207078061938810325 2914600786103392076690867)
            ·
              refine ⟨4371901179155088115036301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2914600786103392076690867 4371901179155088115036301)
              ·
                refine ⟨1639462942183158043138613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4371901179155088115036301 1639462942183158043138613)
                ·
                  refine ⟨153699650829671066544245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1639462942183158043138613 153699650829671066544245)
                  ·
                    rfl

theorem cell23_2693961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 5].length) (baseStart_2693961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2693961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2693961 prefixEnd_2693961 := by exact prefixLift 2693961
  have htrace : WordTrace (prefixWord ++ tailWord_2693961) baseStart_2693961 baseEnd_2693961 := by
    simpa [prefixWord, tailWord_2693961, baseEnd_2693961] using wordTrace_append hprefix tailTrace_2693961
  have hstable : (prefixWord ++ tailWord_2693961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693961).length < 2 ^ (prefixWord ++ tailWord_2693961).sum := by decide
  have hdescent : baseEnd_2693961 < baseStart_2693961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694007 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_2694007 : Nat := 118140960795 + 2694007 * 2 ^ 59
def prefixEnd_2694007 : Nat := 4983230072969 + 3 ^ 40 * 2694007 * 2
def baseEnd_2694007 : Nat := 1383320477577146418922993

theorem tailTrace_2694007 : CollatzResearch.WordTrace tailWord_2694007 prefixEnd_2694007 1383320477577146418922993 := by
  unfold tailWord_2694007
  simp only [CollatzResearch.WordTrace]
  refine ⟨98258507551080213610296275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65505671700720142406864183 98258507551080213610296275)
  ·
    refine ⟨147387761326620320415444413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98258507551080213610296275 147387761326620320415444413)
    ·
      refine ⟨55270410497482620155791655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147387761326620320415444413 55270410497482620155791655)
      ·
        refine ⟨82905615746223930233687483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55270410497482620155791655 82905615746223930233687483)
        ·
          refine ⟨124358423619335895350531225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82905615746223930233687483 124358423619335895350531225)
          ·
            refine ⟨93268817714501921512898419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124358423619335895350531225 93268817714501921512898419)
            ·
              refine ⟨139903226571752882269347629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93268817714501921512898419 139903226571752882269347629)
              ·
                refine ⟨52463709964407330851005361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139903226571752882269347629 52463709964407330851005361)
                ·
                  refine ⟨39347782473305498138254021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52463709964407330851005361 39347782473305498138254021)
                  ·
                    refine ⟨7377709213744780900922629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39347782473305498138254021 7377709213744780900922629)
                    ·
                      refine ⟨1383320477577146418922993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7377709213744780900922629 1383320477577146418922993)
                      ·
                        rfl

theorem cell23_2694007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_2694007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694007 prefixEnd_2694007 := by exact prefixLift 2694007
  have htrace : WordTrace (prefixWord ++ tailWord_2694007) baseStart_2694007 baseEnd_2694007 := by
    simpa [prefixWord, tailWord_2694007, baseEnd_2694007] using wordTrace_append hprefix tailTrace_2694007
  have hstable : (prefixWord ++ tailWord_2694007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694007).length < 2 ^ (prefixWord ++ tailWord_2694007).sum := by decide
  have hdescent : baseEnd_2694007 < baseStart_2694007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694057 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_2694057 : Nat := 118140960795 + 2694057 * 2 ^ 59
def prefixEnd_2694057 : Nat := 4983230072969 + 3 ^ 40 * 2694057 * 2
def baseEnd_2694057 : Nat := 1383346151609871223297763

theorem tailTrace_2694057 : CollatzResearch.WordTrace tailWord_2694057 prefixEnd_2694057 1383346151609871223297763 := by
  unfold tailWord_2694057
  simp only [CollatzResearch.WordTrace]
  refine ⟨98260331200899072149616425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65506887467266048099744283 98260331200899072149616425)
  ·
    refine ⟨73695248400674304112212319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98260331200899072149616425 73695248400674304112212319)
    ·
      refine ⟨110542872601011456168318479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73695248400674304112212319 110542872601011456168318479)
      ·
        refine ⟨165814308901517184252477719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110542872601011456168318479 165814308901517184252477719)
        ·
          refine ⟨248721463352275776378716579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165814308901517184252477719 248721463352275776378716579)
          ·
            refine ⟨373082195028413664568074869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248721463352275776378716579 373082195028413664568074869)
            ·
              refine ⟨34976455783913781053257019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 373082195028413664568074869 34976455783913781053257019)
              ·
                refine ⟨52464683675870671579885529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34976455783913781053257019 52464683675870671579885529)
                ·
                  refine ⟨39348512756903003684914147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52464683675870671579885529 39348512756903003684914147)
                  ·
                    refine ⟨59022769135354505527371221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39348512756903003684914147 59022769135354505527371221)
                    ·
                      refine ⟨1383346151609871223297763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59022769135354505527371221 1383346151609871223297763)
                      ·
                        rfl

theorem cell23_2694057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_2694057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694057 prefixEnd_2694057 := by exact prefixLift 2694057
  have htrace : WordTrace (prefixWord ++ tailWord_2694057) baseStart_2694057 baseEnd_2694057 := by
    simpa [prefixWord, tailWord_2694057, baseEnd_2694057] using wordTrace_append hprefix tailTrace_2694057
  have hstable : (prefixWord ++ tailWord_2694057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694057).length < 2 ^ (prefixWord ++ tailWord_2694057).sum := by decide
  have hdescent : baseEnd_2694057 < baseStart_2694057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694065 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 2, 2, 3]
def baseStart_2694065 : Nat := 118140960795 + 2694065 * 2 ^ 59
def prefixEnd_2694065 : Nat := 4983230072969 + 3 ^ 40 * 2694065 * 2
def baseEnd_2694065 : Nat := 1383350259455107191997727

theorem tailTrace_2694065 : CollatzResearch.WordTrace tailWord_2694065 prefixEnd_2694065 1383350259455107191997727 := by
  unfold tailWord_2694065
  simp only [CollatzResearch.WordTrace]
  refine ⟨98260622984870089515907649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65507081989913393010605099 98260622984870089515907649)
  ·
    refine ⟨73695467238652567136930737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98260622984870089515907649 73695467238652567136930737)
    ·
      refine ⟨55271600428989425352698053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73695467238652567136930737 55271600428989425352698053)
      ·
        refine ⟨10363425080435517253630885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55271600428989425352698053 10363425080435517253630885)
        ·
          refine ⟨1943142202581659485055791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10363425080435517253630885 1943142202581659485055791)
          ·
            refine ⟨2914713303872489227583687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943142202581659485055791 2914713303872489227583687)
            ·
              refine ⟨4372069955808733841375531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2914713303872489227583687 4372069955808733841375531)
              ·
                refine ⟨6558104933713100762063297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4372069955808733841375531 6558104933713100762063297)
                ·
                  refine ⟨4918578700284825571547473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6558104933713100762063297 4918578700284825571547473)
                  ·
                    refine ⟨3688934025213619178660605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4918578700284825571547473 3688934025213619178660605)
                    ·
                      refine ⟨1383350259455107191997727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3688934025213619178660605 1383350259455107191997727)
                      ·
                        rfl

theorem cell23_2694065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_2694065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694065 prefixEnd_2694065 := by exact prefixLift 2694065
  have htrace : WordTrace (prefixWord ++ tailWord_2694065) baseStart_2694065 baseEnd_2694065 := by
    simpa [prefixWord, tailWord_2694065, baseEnd_2694065] using wordTrace_append hprefix tailTrace_2694065
  have hstable : (prefixWord ++ tailWord_2694065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694065).length < 2 ^ (prefixWord ++ tailWord_2694065).sum := by decide
  have hdescent : baseEnd_2694065 < baseStart_2694065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694104 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_2694104 : Nat := 118140960795 + 2694104 * 2 ^ 59
def prefixEnd_2694104 : Nat := 4983230072969 + 3 ^ 40 * 2694104 * 2
def baseEnd_2694104 : Nat := 1383370285200632539410047

theorem tailTrace_2694104 : CollatzResearch.WordTrace tailWord_2694104 prefixEnd_2694104 1383370285200632539410047 := by
  unfold tailWord_2694104
  simp only [CollatzResearch.WordTrace]
  refine ⟨49131022715864399588288683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65508030287819199451051577 49131022715864399588288683)
  ·
    refine ⟨73696534073796599382433025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49131022715864399588288683 73696534073796599382433025)
    ·
      refine ⟨55272400555347449536824769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73696534073796599382433025 55272400555347449536824769)
      ·
        refine ⟨41454300416510587152618577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55272400555347449536824769 41454300416510587152618577)
        ·
          refine ⟨31090725312382940364463933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41454300416510587152618577 31090725312382940364463933)
          ·
            refine ⟨11659021992143602636673975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31090725312382940364463933 11659021992143602636673975)
            ·
              refine ⟨17488532988215403955010963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11659021992143602636673975 17488532988215403955010963)
              ·
                refine ⟨26232799482323105932516445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17488532988215403955010963 26232799482323105932516445)
                ·
                  refine ⟨9837299805871164724693667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26232799482323105932516445 9837299805871164724693667)
                  ·
                    refine ⟨14755949708806747087040501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9837299805871164724693667 14755949708806747087040501)
                    ·
                      refine ⟨1383370285200632539410047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14755949708806747087040501 1383370285200632539410047)
                      ·
                        rfl

theorem cell23_2694104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_2694104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694104 prefixEnd_2694104 := by exact prefixLift 2694104
  have htrace : WordTrace (prefixWord ++ tailWord_2694104) baseStart_2694104 baseEnd_2694104 := by
    simpa [prefixWord, tailWord_2694104, baseEnd_2694104] using wordTrace_append hprefix tailTrace_2694104
  have hstable : (prefixWord ++ tailWord_2694104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694104).length < 2 ^ (prefixWord ++ tailWord_2694104).sum := by decide
  have hdescent : baseEnd_2694104 < baseStart_2694104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694146 : List Nat := [3, 4, 1, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2694146 : Nat := 118140960795 + 2694146 * 2 ^ 59
def prefixEnd_2694146 : Nat := 4983230072969 + 3 ^ 40 * 2694146 * 2
def baseEnd_2694146 : Nat := 1383391851388121375084855

theorem tailTrace_2694146 : CollatzResearch.WordTrace tailWord_2694146 prefixEnd_2694146 1383391851388121375084855 := by
  unfold tailWord_2694146
  simp only [CollatzResearch.WordTrace]
  refine ⟨24565894324394160087401573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65509051531717760233070861 24565894324394160087401573)
  ·
    refine ⟨4606105185823905016387795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24565894324394160087401573 4606105185823905016387795)
    ·
      refine ⟨6909157778735857524581693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4606105185823905016387795 6909157778735857524581693)
      ·
        refine ⟨2590934167025946571718135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6909157778735857524581693 2590934167025946571718135)
        ·
          refine ⟨3886401250538919857577203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590934167025946571718135 3886401250538919857577203)
          ·
            refine ⟨5829601875808379786365805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3886401250538919857577203 5829601875808379786365805)
            ·
              refine ⟨2186100703428142419887177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5829601875808379786365805 2186100703428142419887177)
              ·
                refine ⟨1639575527571106814915383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186100703428142419887177 1639575527571106814915383)
                ·
                  refine ⟨2459363291356660222373075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639575527571106814915383 2459363291356660222373075)
                  ·
                    refine ⟨3689044937034990333559613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2459363291356660222373075 3689044937034990333559613)
                    ·
                      refine ⟨1383391851388121375084855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3689044937034990333559613 1383391851388121375084855)
                      ·
                        rfl

theorem cell23_2694146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2694146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694146 prefixEnd_2694146 := by exact prefixLift 2694146
  have htrace : WordTrace (prefixWord ++ tailWord_2694146) baseStart_2694146 baseEnd_2694146 := by
    simpa [prefixWord, tailWord_2694146, baseEnd_2694146] using wordTrace_append hprefix tailTrace_2694146
  have hstable : (prefixWord ++ tailWord_2694146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694146).length < 2 ^ (prefixWord ++ tailWord_2694146).sum := by decide
  have hdescent : baseEnd_2694146 < baseStart_2694146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694172 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_2694172 : Nat := 118140960795 + 2694172 * 2 ^ 59
def prefixEnd_2694172 : Nat := 4983230072969 + 3 ^ 40 * 2694172 * 2
def baseEnd_2694172 : Nat := 1383405201885138273359735

theorem tailTrace_2694172 : CollatzResearch.WordTrace tailWord_2694172 prefixEnd_2694172 1383405201885138273359735 := by
  unfold tailWord_2694172
  simp only [CollatzResearch.WordTrace]
  refine ⟨49132262797741223395026385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65509683730321631193368513 49132262797741223395026385)
  ·
    refine ⟨36849197098305917546269789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49132262797741223395026385 36849197098305917546269789)
    ·
      refine ⟨13818448911864719079851171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36849197098305917546269789 13818448911864719079851171)
      ·
        refine ⟨20727673367797078619776757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13818448911864719079851171 20727673367797078619776757)
        ·
          refine ⟨1943219378230976120604071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20727673367797078619776757 1943219378230976120604071)
          ·
            refine ⟨2914829067346464180906107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943219378230976120604071 2914829067346464180906107)
            ·
              refine ⟨4372243601019696271359161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2914829067346464180906107 4372243601019696271359161)
              ·
                refine ⟨3279182700764772203519371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4372243601019696271359161 3279182700764772203519371)
                ·
                  refine ⟨4918774051147158305279057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3279182700764772203519371 4918774051147158305279057)
                  ·
                    refine ⟨3689080538360368728959293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4918774051147158305279057 3689080538360368728959293)
                    ·
                      refine ⟨1383405201885138273359735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3689080538360368728959293 1383405201885138273359735)
                      ·
                        rfl

theorem cell23_2694172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_2694172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694172 prefixEnd_2694172 := by exact prefixLift 2694172
  have htrace : WordTrace (prefixWord ++ tailWord_2694172) baseStart_2694172 baseEnd_2694172 := by
    simpa [prefixWord, tailWord_2694172, baseEnd_2694172] using wordTrace_append hprefix tailTrace_2694172
  have hstable : (prefixWord ++ tailWord_2694172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694172).length < 2 ^ (prefixWord ++ tailWord_2694172).sum := by decide
  have hdescent : baseEnd_2694172 < baseStart_2694172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694225 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 2, 2, 2]
def baseStart_2694225 : Nat := 118140960795 + 2694225 * 2 ^ 59
def prefixEnd_2694225 : Nat := 4983230072969 + 3 ^ 40 * 2694225 * 2
def baseEnd_2694225 : Nat := 1383432416359826565996991

theorem tailTrace_2694225 : CollatzResearch.WordTrace tailWord_2694225 prefixEnd_2694225 1383432416359826565996991 := by
  unfold tailWord_2694225
  simp only [CollatzResearch.WordTrace]
  refine ⟨98266458664290436841732129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65510972442860291227821419 98266458664290436841732129)
  ·
    refine ⟨73699843998217827631299097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98266458664290436841732129 73699843998217827631299097)
    ·
      refine ⟨55274882998663370723474323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73699843998217827631299097 55274882998663370723474323)
      ·
        refine ⟨82912324497995056085211485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55274882998663370723474323 82912324497995056085211485)
        ·
          refine ⟨31092121686748146031954307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82912324497995056085211485 31092121686748146031954307)
          ·
            refine ⟨46638182530122219047931461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31092121686748146031954307 46638182530122219047931461)
            ·
              refine ⟨8744659224397916071487149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46638182530122219047931461 8744659224397916071487149)
              ·
                refine ⟨3279247209149218526807681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8744659224397916071487149 3279247209149218526807681)
                ·
                  refine ⟨2459435406861913895105761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3279247209149218526807681 2459435406861913895105761)
                  ·
                    refine ⟨1844576555146435421329321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2459435406861913895105761 1844576555146435421329321)
                    ·
                      refine ⟨1383432416359826565996991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844576555146435421329321 1383432416359826565996991)
                      ·
                        rfl

theorem cell23_2694225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_2694225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694225 prefixEnd_2694225 := by exact prefixLift 2694225
  have htrace : WordTrace (prefixWord ++ tailWord_2694225) baseStart_2694225 baseEnd_2694225 := by
    simpa [prefixWord, tailWord_2694225, baseEnd_2694225] using wordTrace_append hprefix tailTrace_2694225
  have hstable : (prefixWord ++ tailWord_2694225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694225).length < 2 ^ (prefixWord ++ tailWord_2694225).sum := by decide
  have hdescent : baseEnd_2694225 < baseStart_2694225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694281 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_2694281 : Nat := 118140960795 + 2694281 * 2 ^ 59
def prefixEnd_2694281 : Nat := 4983230072969 + 3 ^ 40 * 2694281 * 2
def baseEnd_2694281 : Nat := 1383461171276478346896733

theorem tailTrace_2694281 : CollatzResearch.WordTrace tailWord_2694281 prefixEnd_2694281 1383461171276478346896733 := by
  unfold tailWord_2694281
  simp only [CollatzResearch.WordTrace]
  refine ⟨98268501152087558405770697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65512334101391705603847131 98268501152087558405770697)
  ·
    refine ⟨73701375864065668804328023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98268501152087558405770697 73701375864065668804328023)
    ·
      refine ⟨110552063796098503206492035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73701375864065668804328023 110552063796098503206492035)
      ·
        refine ⟨165828095694147754809738053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110552063796098503206492035 165828095694147754809738053)
        ·
          refine ⟨31092767942652704026825885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165828095694147754809738053 31092767942652704026825885)
          ·
            refine ⟨11659787978494764010059707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31092767942652704026825885 11659787978494764010059707)
            ·
              refine ⟨17489681967742146015089561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11659787978494764010059707 17489681967742146015089561)
              ·
                refine ⟨13117261475806609511317171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17489681967742146015089561 13117261475806609511317171)
                ·
                  refine ⟨19675892213709914266975757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13117261475806609511317171 19675892213709914266975757)
                  ·
                    refine ⟨7378459580141217850115909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19675892213709914266975757 7378459580141217850115909)
                    ·
                      refine ⟨1383461171276478346896733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7378459580141217850115909 1383461171276478346896733)
                      ·
                        rfl

theorem cell23_2694281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_2694281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694281 prefixEnd_2694281 := by exact prefixLift 2694281
  have htrace : WordTrace (prefixWord ++ tailWord_2694281) baseStart_2694281 baseEnd_2694281 := by
    simpa [prefixWord, tailWord_2694281, baseEnd_2694281] using wordTrace_append hprefix tailTrace_2694281
  have hstable : (prefixWord ++ tailWord_2694281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694281).length < 2 ^ (prefixWord ++ tailWord_2694281).sum := by decide
  have hdescent : baseEnd_2694281 < baseStart_2694281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694298 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2694298 : Nat := 118140960795 + 2694298 * 2 ^ 59
def prefixEnd_2694298 : Nat := 4983230072969 + 3 ^ 40 * 2694298 * 2
def baseEnd_2694298 : Nat := 1383469900447604780384155

theorem tailTrace_2694298 : CollatzResearch.WordTrace tailWord_2694298 prefixEnd_2694298 1383469900447604780384155 := by
  unfold tailWord_2694298
  simp only [CollatzResearch.WordTrace]
  refine ⟨24567280298256492577284887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65512747462017313539426365 24567280298256492577284887)
  ·
    refine ⟨36850920447384738865927331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24567280298256492577284887 36850920447384738865927331)
    ·
      refine ⟨55276380671077108298890997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36850920447384738865927331 55276380671077108298890997)
      ·
        refine ⟨5182160687913478903021031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55276380671077108298890997 5182160687913478903021031)
        ·
          refine ⟨7773241031870218354531547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5182160687913478903021031 7773241031870218354531547)
          ·
            refine ⟨11659861547805327531797321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7773241031870218354531547 11659861547805327531797321)
            ·
              refine ⟨8744896160853995648847991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11659861547805327531797321 8744896160853995648847991)
              ·
                refine ⟨13117344241280993473271987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8744896160853995648847991 13117344241280993473271987)
                ·
                  refine ⟨19676016361921490209907981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13117344241280993473271987 19676016361921490209907981)
                  ·
                    refine ⟨7378506135720558828715493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19676016361921490209907981 7378506135720558828715493)
                    ·
                      refine ⟨1383469900447604780384155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7378506135720558828715493 1383469900447604780384155)
                      ·
                        rfl

theorem cell23_2694298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2694298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694298 prefixEnd_2694298 := by exact prefixLift 2694298
  have htrace : WordTrace (prefixWord ++ tailWord_2694298) baseStart_2694298 baseEnd_2694298 := by
    simpa [prefixWord, tailWord_2694298, baseEnd_2694298] using wordTrace_append hprefix tailTrace_2694298
  have hstable : (prefixWord ++ tailWord_2694298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694298).length < 2 ^ (prefixWord ++ tailWord_2694298).sum := by decide
  have hdescent : baseEnd_2694298 < baseStart_2694298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694331 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 3]
def baseStart_2694331 : Nat := 118140960795 + 2694331 * 2 ^ 59
def prefixEnd_2694331 : Nat := 4983230072969 + 3 ^ 40 * 2694331 * 2
def baseEnd_2694331 : Nat := 1383486845309203151271503

theorem tailTrace_2694331 : CollatzResearch.WordTrace tailWord_2694331 prefixEnd_2694331 1383486845309203151271503 := by
  unfold tailWord_2694331
  simp only [CollatzResearch.WordTrace]
  refine ⟨98270324801906416945090847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65513549867937611296727231 98270324801906416945090847)
  ·
    refine ⟨147405487202859625417636271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98270324801906416945090847 147405487202859625417636271)
    ·
      refine ⟨221108230804289438126454407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147405487202859625417636271 221108230804289438126454407)
      ·
        refine ⟨331662346206434157189681611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221108230804289438126454407 331662346206434157189681611)
        ·
          refine ⟨497493519309651235784522417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331662346206434157189681611 497493519309651235784522417)
          ·
            refine ⟨373120139482238426838391813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497493519309651235784522417 373120139482238426838391813)
            ·
              refine ⟨69960026152919705032198465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 373120139482238426838391813 69960026152919705032198465)
              ·
                refine ⟨52470019614689778774148849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69960026152919705032198465 52470019614689778774148849)
                ·
                  refine ⟨39352514711017334080611637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52470019614689778774148849 39352514711017334080611637)
                  ·
                    refine ⟨3689298254157875070057341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39352514711017334080611637 3689298254157875070057341)
                    ·
                      refine ⟨1383486845309203151271503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3689298254157875070057341 1383486845309203151271503)
                      ·
                        rfl

theorem cell23_2694331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 3].length) (baseStart_2694331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694331 prefixEnd_2694331 := by exact prefixLift 2694331
  have htrace : WordTrace (prefixWord ++ tailWord_2694331) baseStart_2694331 baseEnd_2694331 := by
    simpa [prefixWord, tailWord_2694331, baseEnd_2694331] using wordTrace_append hprefix tailTrace_2694331
  have hstable : (prefixWord ++ tailWord_2694331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694331).length < 2 ^ (prefixWord ++ tailWord_2694331).sum := by decide
  have hdescent : baseEnd_2694331 < baseStart_2694331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694349 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2694349 : Nat := 118140960795 + 2694349 * 2 ^ 59
def prefixEnd_2694349 : Nat := 4983230072969 + 3 ^ 40 * 2694349 * 2
def baseEnd_2694349 : Nat := 1383496087960984080846421

theorem tailTrace_2694349 : CollatzResearch.WordTrace tailWord_2694349 prefixEnd_2694349 1383496087960984080846421 := by
  unfold tailWord_2694349
  simp only [CollatzResearch.WordTrace]
  refine ⟨98270981315841206019246101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65513987543894137346164067 98270981315841206019246101)
  ·
    refine ⟨4606452249180056532152161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98270981315841206019246101 4606452249180056532152161)
    ·
      refine ⟨3454839186885042399114121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4606452249180056532152161 3454839186885042399114121)
      ·
        refine ⟨2591129390163781799335591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3454839186885042399114121 2591129390163781799335591)
        ·
          refine ⟨3886694085245672699003387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591129390163781799335591 3886694085245672699003387)
          ·
            refine ⟨5830041127868509048505081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3886694085245672699003387 5830041127868509048505081)
            ·
              refine ⟨4372530845901381786378811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5830041127868509048505081 4372530845901381786378811)
              ·
                refine ⟨6558796268852072679568217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4372530845901381786378811 6558796268852072679568217)
                ·
                  refine ⟨4919097201639054509676163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6558796268852072679568217 4919097201639054509676163)
                  ·
                    refine ⟨7378645802458581764514245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4919097201639054509676163 7378645802458581764514245)
                    ·
                      refine ⟨1383496087960984080846421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7378645802458581764514245 1383496087960984080846421)
                      ·
                        rfl

theorem cell23_2694349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2694349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694349 prefixEnd_2694349 := by exact prefixLift 2694349
  have htrace : WordTrace (prefixWord ++ tailWord_2694349) baseStart_2694349 baseEnd_2694349 := by
    simpa [prefixWord, tailWord_2694349, baseEnd_2694349] using wordTrace_append hprefix tailTrace_2694349
  have hstable : (prefixWord ++ tailWord_2694349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694349).length < 2 ^ (prefixWord ++ tailWord_2694349).sum := by decide
  have hdescent : baseEnd_2694349 < baseStart_2694349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694441 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 6, 7]
def baseStart_2694441 : Nat := 118140960795 + 2694441 * 2 ^ 59
def prefixEnd_2694441 : Nat := 4983230072969 + 3 ^ 40 * 2694441 * 2
def baseEnd_2694441 : Nat := 461181109393732573631999

theorem tailTrace_2694441 : CollatzResearch.WordTrace tailWord_2694441 prefixEnd_2694441 461181109393732573631999 := by
  unfold tailWord_2694441
  simp only [CollatzResearch.WordTrace]
  refine ⟨98274336831507905731595177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65516224554338603821063451 98274336831507905731595177)
  ·
    refine ⟨73705752623630929298696383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98274336831507905731595177 73705752623630929298696383)
    ·
      refine ⟨110558628935446393948044575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73705752623630929298696383 110558628935446393948044575)
      ·
        refine ⟨165837943403169590922066863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110558628935446393948044575 165837943403169590922066863)
        ·
          refine ⟨248756915104754386383100295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165837943403169590922066863 248756915104754386383100295)
          ·
            refine ⟨373135372657131579574650443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248756915104754386383100295 373135372657131579574650443)
            ·
              refine ⟨559703058985697369361975665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373135372657131579574650443 559703058985697369361975665)
              ·
                refine ⟨419777294239273027021481749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 559703058985697369361975665 419777294239273027021481749)
                ·
                  refine ⟨19677060667465923141631957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 419777294239273027021481749 19677060667465923141631957)
                  ·
                    refine ⟨461181109393732573631999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19677060667465923141631957 461181109393732573631999)
                    ·
                      rfl

theorem cell23_2694441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_2694441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694441 prefixEnd_2694441 := by exact prefixLift 2694441
  have htrace : WordTrace (prefixWord ++ tailWord_2694441) baseStart_2694441 baseEnd_2694441 := by
    simpa [prefixWord, tailWord_2694441, baseEnd_2694441] using wordTrace_append hprefix tailTrace_2694441
  have hstable : (prefixWord ++ tailWord_2694441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694441).length < 2 ^ (prefixWord ++ tailWord_2694441).sum := by decide
  have hdescent : baseEnd_2694441 < baseStart_2694441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694529 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_2694529 : Nat := 118140960795 + 2694529 * 2 ^ 59
def prefixEnd_2694529 : Nat := 4983230072969 + 3 ^ 40 * 2694529 * 2
def baseEnd_2694529 : Nat := 1383588514478793376595593

theorem tailTrace_2694529 : CollatzResearch.WordTrace tailWord_2694529 prefixEnd_2694529 1383588514478793376595593 := by
  unfold tailWord_2694529
  simp only [CollatzResearch.WordTrace]
  refine ⟨98277546455189096760798641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65518364303459397840532427 98277546455189096760798641)
  ·
    refine ⟨73708159841391822570598981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98277546455189096760798641 73708159841391822570598981)
    ·
      refine ⟨13820279970260966731987309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73708159841391822570598981 13820279970260966731987309)
      ·
        refine ⟨5182604988847862524495241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13820279970260966731987309 5182604988847862524495241)
        ·
          refine ⟨3886953741635896893371431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5182604988847862524495241 3886953741635896893371431)
          ·
            refine ⟨5830430612453845340057147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3886953741635896893371431 5830430612453845340057147)
            ·
              refine ⟨8745645918680768010085721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830430612453845340057147 8745645918680768010085721)
              ·
                refine ⟨6559234439010576007564291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8745645918680768010085721 6559234439010576007564291)
                ·
                  refine ⟨9838851658515864011346437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6559234439010576007564291 9838851658515864011346437)
                  ·
                    refine ⟨1844784685971724502127457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9838851658515864011346437 1844784685971724502127457)
                    ·
                      refine ⟨1383588514478793376595593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844784685971724502127457 1383588514478793376595593)
                      ·
                        rfl

theorem cell23_2694529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_2694529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694529 prefixEnd_2694529 := by exact prefixLift 2694529
  have htrace : WordTrace (prefixWord ++ tailWord_2694529) baseStart_2694529 baseEnd_2694529 := by
    simpa [prefixWord, tailWord_2694529, baseEnd_2694529] using wordTrace_append hprefix tailTrace_2694529
  have hstable : (prefixWord ++ tailWord_2694529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694529).length < 2 ^ (prefixWord ++ tailWord_2694529).sum := by decide
  have hdescent : baseEnd_2694529 < baseStart_2694529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694562 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_2694562 : Nat := 118140960795 + 2694562 * 2 ^ 59
def prefixEnd_2694562 : Nat := 4983230072969 + 3 ^ 40 * 2694562 * 2
def baseEnd_2694562 : Nat := 1383605459340391747482941

theorem tailTrace_2694562 : CollatzResearch.WordTrace tailWord_2694562 prefixEnd_2694562 1383605459340391747482941 := by
  unfold tailWord_2694562
  simp only [CollatzResearch.WordTrace]
  refine ⟨24569687516017385849187485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65519166709379695597833293 24569687516017385849187485)
  ·
    refine ⟨9213632818506519693445307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24569687516017385849187485 9213632818506519693445307)
    ·
      refine ⟨13820449227759779540167961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9213632818506519693445307 13820449227759779540167961)
      ·
        refine ⟨10365336920819834655125971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13820449227759779540167961 10365336920819834655125971)
        ·
          refine ⟨15548005381229751982688957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10365336920819834655125971 15548005381229751982688957)
          ·
            refine ⟨5830502017961156993508359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15548005381229751982688957 5830502017961156993508359)
            ·
              refine ⟨8745753026941735490262539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830502017961156993508359 8745753026941735490262539)
              ·
                refine ⟨13118629540412603235393809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8745753026941735490262539 13118629540412603235393809)
                ·
                  refine ⟨9838972155309452426545357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13118629540412603235393809 9838972155309452426545357)
                  ·
                    refine ⟨3689614558241044659954509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9838972155309452426545357 3689614558241044659954509)
                    ·
                      refine ⟨1383605459340391747482941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3689614558241044659954509 1383605459340391747482941)
                      ·
                        rfl

theorem cell23_2694562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_2694562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694562 prefixEnd_2694562 := by exact prefixLift 2694562
  have htrace : WordTrace (prefixWord ++ tailWord_2694562) baseStart_2694562 baseEnd_2694562 := by
    simpa [prefixWord, tailWord_2694562, baseEnd_2694562] using wordTrace_append hprefix tailTrace_2694562
  have hstable : (prefixWord ++ tailWord_2694562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694562).length < 2 ^ (prefixWord ++ tailWord_2694562).sum := by decide
  have hdescent : baseEnd_2694562 < baseStart_2694562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694578 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_2694578 : Nat := 118140960795 + 2694578 * 2 ^ 59
def prefixEnd_2694578 : Nat := 4983230072969 + 3 ^ 40 * 2694578 * 2
def baseEnd_2694578 : Nat := 461204558343621228294289

theorem tailTrace_2694578 : CollatzResearch.WordTrace tailWord_2694578 prefixEnd_2694578 461204558343621228294289 := by
  unfold tailWord_2694578
  simp only [CollatzResearch.WordTrace]
  refine ⟨24569833408002894532333097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65519555754674385419554925 24569833408002894532333097)
  ·
    refine ⟨18427375056002170899249823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24569833408002894532333097 18427375056002170899249823)
    ·
      refine ⟨27641062584003256348874735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18427375056002170899249823 27641062584003256348874735)
      ·
        refine ⟨41461593876004884523312103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27641062584003256348874735 41461593876004884523312103)
        ·
          refine ⟨62192390814007326784968155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41461593876004884523312103 62192390814007326784968155)
          ·
            refine ⟨93288586221010990177452233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62192390814007326784968155 93288586221010990177452233)
            ·
              refine ⟨69966439665758242633089175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93288586221010990177452233 69966439665758242633089175)
              ·
                refine ⟨104949659498637363949633763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69966439665758242633089175 104949659498637363949633763)
                ·
                  refine ⟨157424489247956045924450645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104949659498637363949633763 157424489247956045924450645)
                  ·
                    refine ⟨461204558343621228294289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 157424489247956045924450645 461204558343621228294289)
                    ·
                      rfl

theorem cell23_2694578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_2694578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694578 prefixEnd_2694578 := by exact prefixLift 2694578
  have htrace : WordTrace (prefixWord ++ tailWord_2694578) baseStart_2694578 baseEnd_2694578 := by
    simpa [prefixWord, tailWord_2694578, baseEnd_2694578] using wordTrace_append hprefix tailTrace_2694578
  have hstable : (prefixWord ++ tailWord_2694578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694578).length < 2 ^ (prefixWord ++ tailWord_2694578).sum := by decide
  have hdescent : baseEnd_2694578 < baseStart_2694578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694602 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2]
def baseStart_2694602 : Nat := 118140960795 + 2694602 * 2 ^ 59
def prefixEnd_2694602 : Nat := 4983230072969 + 3 ^ 40 * 2694602 * 2
def baseEnd_2694602 : Nat := 1383625998566571590982757

theorem tailTrace_2694602 : CollatzResearch.WordTrace tailWord_2694602 prefixEnd_2694602 1383625998566571590982757 := by
  unfold tailWord_2694602
  simp only [CollatzResearch.WordTrace]
  refine ⟨24570052245981157557051515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65520139322616420152137373 24570052245981157557051515)
  ·
    refine ⟨36855078368971736335577273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24570052245981157557051515 36855078368971736335577273)
    ·
      refine ⟨27641308776728802251682955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36855078368971736335577273 27641308776728802251682955)
      ·
        refine ⟨41461963165093203377524433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27641308776728802251682955 41461963165093203377524433)
        ·
          refine ⟨31096472373819902533143325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41461963165093203377524433 31096472373819902533143325)
          ·
            refine ⟨11661177140182463449928747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31096472373819902533143325 11661177140182463449928747)
            ·
              refine ⟨17491765710273695174893121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11661177140182463449928747 17491765710273695174893121)
              ·
                refine ⟨13118824282705271381169841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17491765710273695174893121 13118824282705271381169841)
                ·
                  refine ⟨9839118212028953535877381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13118824282705271381169841 9839118212028953535877381)
                  ·
                    refine ⟨1844834664755428787977009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9839118212028953535877381 1844834664755428787977009)
                    ·
                      refine ⟨1383625998566571590982757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844834664755428787977009 1383625998566571590982757)
                      ·
                        rfl

theorem cell23_2694602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_2694602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694602 prefixEnd_2694602 := by exact prefixLift 2694602
  have htrace : WordTrace (prefixWord ++ tailWord_2694602) baseStart_2694602 baseEnd_2694602 := by
    simpa [prefixWord, tailWord_2694602, baseEnd_2694602] using wordTrace_append hprefix tailTrace_2694602
  have hstable : (prefixWord ++ tailWord_2694602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694602).length < 2 ^ (prefixWord ++ tailWord_2694602).sum := by decide
  have hdescent : baseEnd_2694602 < baseStart_2694602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694608 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 8]
def baseStart_2694608 : Nat := 118140960795 + 2694608 * 2 ^ 59
def prefixEnd_2694608 : Nat := 4983230072969 + 3 ^ 40 * 2694608 * 2
def baseEnd_2694608 : Nat := 153736564383388729723081

theorem tailTrace_2694608 : CollatzResearch.WordTrace tailWord_2694608 prefixEnd_2694608 153736564383388729723081 := by
  unfold tailWord_2694608
  simp only [CollatzResearch.WordTrace]
  refine ⟨49140213910951446626462239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65520285214601928835282985 49140213910951446626462239)
  ·
    refine ⟨73710320866427169939693359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49140213910951446626462239 73710320866427169939693359)
    ·
      refine ⟨110565481299640754909540039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73710320866427169939693359 110565481299640754909540039)
      ·
        refine ⟨165848221949461132364310059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110565481299640754909540039 165848221949461132364310059)
        ·
          refine ⟨248772332924191698546465089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165848221949461132364310059 248772332924191698546465089)
          ·
            refine ⟨186579249693143773909848817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248772332924191698546465089 186579249693143773909848817)
            ·
              refine ⟨139934437269857830432386613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186579249693143773909848817 139934437269857830432386613)
              ·
                refine ⟨13118853494049171603036245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139934437269857830432386613 13118853494049171603036245)
                ·
                  refine ⟨153736564383388729723081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13118853494049171603036245 153736564383388729723081)
                  ·
                    rfl

theorem cell23_2694608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 8].length) (baseStart_2694608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694608 prefixEnd_2694608 := by exact prefixLift 2694608
  have htrace : WordTrace (prefixWord ++ tailWord_2694608) baseStart_2694608 baseEnd_2694608 := by
    simpa [prefixWord, tailWord_2694608, baseEnd_2694608] using wordTrace_append hprefix tailTrace_2694608
  have hstable : (prefixWord ++ tailWord_2694608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694608).length < 2 ^ (prefixWord ++ tailWord_2694608).sum := by decide
  have hdescent : baseEnd_2694608 < baseStart_2694608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694646 : List Nat := [5, 1, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_2694646 : Nat := 118140960795 + 2694646 * 2 ^ 59
def prefixEnd_2694646 : Nat := 4983230072969 + 3 ^ 40 * 2694646 * 2
def baseEnd_2694646 : Nat := 461216197238456472944185

theorem tailTrace_2694646 : CollatzResearch.WordTrace tailWord_2694646 prefixEnd_2694646 461216197238456472944185 := by
  unfold tailWord_2694646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6142613362235326608925487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65521209197176817161871861 6142613362235326608925487)
  ·
    refine ⟨9213920043352989913388231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6142613362235326608925487 9213920043352989913388231)
    ·
      refine ⟨13820880065029484870082347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9213920043352989913388231 13820880065029484870082347)
      ·
        refine ⟨20731320097544227305123521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13820880065029484870082347 20731320097544227305123521)
        ·
          refine ⟨15548490073158170478842641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20731320097544227305123521 15548490073158170478842641)
          ·
            refine ⟨11661367554868627859131981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15548490073158170478842641 11661367554868627859131981)
            ·
              refine ⟨4373012833075735447174493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11661367554868627859131981 4373012833075735447174493)
              ·
                refine ⟨1639879812403400792690435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4373012833075735447174493 1639879812403400792690435)
                ·
                  refine ⟨2459819718605101189035653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639879812403400792690435 2459819718605101189035653)
                  ·
                    refine ⟨461216197238456472944185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2459819718605101189035653 461216197238456472944185)
                    ·
                      rfl

theorem cell23_2694646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_2694646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694646 prefixEnd_2694646 := by exact prefixLift 2694646
  have htrace : WordTrace (prefixWord ++ tailWord_2694646) baseStart_2694646 baseEnd_2694646 := by
    simpa [prefixWord, tailWord_2694646, baseEnd_2694646] using wordTrace_append hprefix tailTrace_2694646
  have hstable : (prefixWord ++ tailWord_2694646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694646).length < 2 ^ (prefixWord ++ tailWord_2694646).sum := by decide
  have hdescent : baseEnd_2694646 < baseStart_2694646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694652 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_2694652 : Nat := 118140960795 + 2694652 * 2 ^ 59
def prefixEnd_2694652 : Nat := 4983230072969 + 3 ^ 40 * 2694652 * 2
def baseEnd_2694652 : Nat := 1383651672599296395357527

theorem tailTrace_2694652 : CollatzResearch.WordTrace tailWord_2694652 prefixEnd_2694652 1383651672599296395357527 := by
  unfold tailWord_2694652
  simp only [CollatzResearch.WordTrace]
  refine ⟨49141016316871744383763105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65521355089162325845017473 49141016316871744383763105)
  ·
    refine ⟨36855762237653808287822329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49141016316871744383763105 36855762237653808287822329)
    ·
      refine ⟨27641821678240356215866747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36855762237653808287822329 27641821678240356215866747)
      ·
        refine ⟨41462732517360534323800121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27641821678240356215866747 41462732517360534323800121)
        ·
          refine ⟨31097049388020400742850091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41462732517360534323800121 31097049388020400742850091)
          ·
            refine ⟨46645574082030601114275137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31097049388020400742850091 46645574082030601114275137)
            ·
              refine ⟨34984180561522950835706353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46645574082030601114275137 34984180561522950835706353)
              ·
                refine ⟨26238135421142213126779765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34984180561522950835706353 26238135421142213126779765)
                ·
                  refine ⟨2459825195732082480635603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26238135421142213126779765 2459825195732082480635603)
                  ·
                    refine ⟨3689737793598123720953405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2459825195732082480635603 3689737793598123720953405)
                    ·
                      refine ⟨1383651672599296395357527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3689737793598123720953405 1383651672599296395357527)
                      ·
                        rfl

theorem cell23_2694652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_2694652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694652 prefixEnd_2694652 := by exact prefixLift 2694652
  have htrace : WordTrace (prefixWord ++ tailWord_2694652) baseStart_2694652 baseEnd_2694652 := by
    simpa [prefixWord, tailWord_2694652, baseEnd_2694652] using wordTrace_append hprefix tailTrace_2694652
  have hstable : (prefixWord ++ tailWord_2694652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694652).length < 2 ^ (prefixWord ++ tailWord_2694652).sum := by decide
  have hdescent : baseEnd_2694652 < baseStart_2694652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694689 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 1, 5]
def baseStart_2694689 : Nat := 118140960795 + 2694689 * 2 ^ 59
def prefixEnd_2694689 : Nat := 4983230072969 + 3 ^ 40 * 2694689 * 2
def baseEnd_2694689 : Nat := 461223557127837583531619

theorem tailTrace_2694689 : CollatzResearch.WordTrace tailWord_2694689 prefixEnd_2694689 461223557127837583531619 := by
  unfold tailWord_2694689
  simp only [CollatzResearch.WordTrace]
  refine ⟨98283382134609444086623121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65522254756406296057748747 98283382134609444086623121)
  ·
    refine ⟨73712536600957083064967341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98283382134609444086623121 73712536600957083064967341)
    ·
      refine ⟨27642201225358906149362753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73712536600957083064967341 27642201225358906149362753)
      ·
        refine ⟨20731650919019179612022065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27642201225358906149362753 20731650919019179612022065)
        ·
          refine ⟨15548738189264384709016549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20731650919019179612022065 15548738189264384709016549)
          ·
            refine ⟨2915388410487072132940603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15548738189264384709016549 2915388410487072132940603)
            ·
              refine ⟨4373082615730608199410905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2915388410487072132940603 4373082615730608199410905)
              ·
                refine ⟨3279811961797956149558179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4373082615730608199410905 3279811961797956149558179)
                ·
                  refine ⟨4919717942696934224337269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3279811961797956149558179 4919717942696934224337269)
                  ·
                    refine ⟨461223557127837583531619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4919717942696934224337269 461223557127837583531619)
                    ·
                      rfl

theorem cell23_2694689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_2694689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694689 prefixEnd_2694689 := by exact prefixLift 2694689
  have htrace : WordTrace (prefixWord ++ tailWord_2694689) baseStart_2694689 baseEnd_2694689 := by
    simpa [prefixWord, tailWord_2694689, baseEnd_2694689] using wordTrace_append hprefix tailTrace_2694689
  have hstable : (prefixWord ++ tailWord_2694689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694689).length < 2 ^ (prefixWord ++ tailWord_2694689).sum := by decide
  have hdescent : baseEnd_2694689 < baseStart_2694689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694702 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2694702 : Nat := 118140960795 + 2694702 * 2 ^ 59
def prefixEnd_2694702 : Nat := 4983230072969 + 3 ^ 40 * 2694702 * 2
def baseEnd_2694702 : Nat := 461225782210673733244099

theorem tailTrace_2694702 : CollatzResearch.WordTrace tailWord_2694702 prefixEnd_2694702 461225782210673733244099 := by
  unfold tailWord_2694702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12285482035445293413355795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65522570855708231537897573 12285482035445293413355795)
  ·
    refine ⟨18428223053167940120033693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12285482035445293413355795 18428223053167940120033693)
    ·
      refine ⟨6910583644937977545012635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18428223053167940120033693 6910583644937977545012635)
      ·
        refine ⟨10365875467406966317518953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6910583644937977545012635 10365875467406966317518953)
        ·
          refine ⟨7774406600555224738139215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10365875467406966317518953 7774406600555224738139215)
          ·
            refine ⟨11661609900832837107208823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774406600555224738139215 11661609900832837107208823)
            ·
              refine ⟨17492414851249255660813235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11661609900832837107208823 17492414851249255660813235)
              ·
                refine ⟨26238622276873883491219853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17492414851249255660813235 26238622276873883491219853)
                ·
                  refine ⟨9839483353827706309207445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26238622276873883491219853 9839483353827706309207445)
                  ·
                    refine ⟨461225782210673733244099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9839483353827706309207445 461225782210673733244099)
                    ·
                      rfl

theorem cell23_2694702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2694702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694702 prefixEnd_2694702 := by exact prefixLift 2694702
  have htrace : WordTrace (prefixWord ++ tailWord_2694702) baseStart_2694702 baseEnd_2694702 := by
    simpa [prefixWord, tailWord_2694702, baseEnd_2694702] using wordTrace_append hprefix tailTrace_2694702
  have hstable : (prefixWord ++ tailWord_2694702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694702).length < 2 ^ (prefixWord ++ tailWord_2694702).sum := by decide
  have hdescent : baseEnd_2694702 < baseStart_2694702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694712 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 1, 1, 5]
def baseStart_2694712 : Nat := 118140960795 + 2694712 * 2 ^ 59
def prefixEnd_2694712 : Nat := 4983230072969 + 3 ^ 40 * 2694712 * 2
def baseEnd_2694712 : Nat := 1383682481438566160607251

theorem tailTrace_2694712 : CollatzResearch.WordTrace tailWord_2694712 prefixEnd_2694712 1383682481438566160607251 := by
  unfold tailWord_2694712
  simp only [CollatzResearch.WordTrace]
  refine ⟨49142110506763059507355195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65522814009017412676473593 49142110506763059507355195)
  ·
    refine ⟨73713165760144589261032793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49142110506763059507355195 73713165760144589261032793)
    ·
      refine ⟨55284874320108441945774595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73713165760144589261032793 55284874320108441945774595)
      ·
        refine ⟨82927311480162662918661893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55284874320108441945774595 82927311480162662918661893)
        ·
          refine ⟨15548870902530499297249105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82927311480162662918661893 15548870902530499297249105)
          ·
            refine ⟨11661653176897874472936829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15548870902530499297249105 11661653176897874472936829)
            ·
              refine ⟨4373119941336702927351311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11661653176897874472936829 4373119941336702927351311)
              ·
                refine ⟨6559679912005054391026967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4373119941336702927351311 6559679912005054391026967)
                ·
                  refine ⟨9839519868007581586540451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6559679912005054391026967 9839519868007581586540451)
                  ·
                    refine ⟨14759279802011372379810677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9839519868007581586540451 14759279802011372379810677)
                    ·
                      refine ⟨1383682481438566160607251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14759279802011372379810677 1383682481438566160607251)
                      ·
                        rfl

theorem cell23_2694712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_2694712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694712 prefixEnd_2694712 := by exact prefixLift 2694712
  have htrace : WordTrace (prefixWord ++ tailWord_2694712) baseStart_2694712 baseEnd_2694712 := by
    simpa [prefixWord, tailWord_2694712, baseEnd_2694712] using wordTrace_append hprefix tailTrace_2694712
  have hstable : (prefixWord ++ tailWord_2694712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694712).length < 2 ^ (prefixWord ++ tailWord_2694712).sum := by decide
  have hdescent : baseEnd_2694712 < baseStart_2694712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694719 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 2, 4]
def baseStart_2694719 : Nat := 118140960795 + 2694719 * 2 ^ 59
def prefixEnd_2694719 : Nat := 4983230072969 + 3 ^ 40 * 2694719 * 2
def baseEnd_2694719 : Nat := 461228691934382544406573

theorem tailTrace_2694719 : CollatzResearch.WordTrace tailWord_2694719 prefixEnd_2694719 461228691934382544406573 := by
  unfold tailWord_2694719
  simp only [CollatzResearch.WordTrace]
  refine ⟨98284476324500759210215211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65522984216333839473476807 98284476324500759210215211)
  ·
    refine ⟨147426714486751138815322817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98284476324500759210215211 147426714486751138815322817)
    ·
      refine ⟨110570035865063354111492113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147426714486751138815322817 110570035865063354111492113)
      ·
        refine ⟨82927526898797515583619085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110570035865063354111492113 82927526898797515583619085)
        ·
          refine ⟨31097822587049068343857157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82927526898797515583619085 31097822587049068343857157)
          ·
            refine ⟨5830841735071700314473217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31097822587049068343857157 5830841735071700314473217)
            ·
              refine ⟨4373131301303775235854913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5830841735071700314473217 4373131301303775235854913)
              ·
                refine ⟨3279848475977831426891185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4373131301303775235854913 3279848475977831426891185)
                ·
                  refine ⟨2459886356983373570168389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3279848475977831426891185 2459886356983373570168389)
                  ·
                    refine ⟨461228691934382544406573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2459886356983373570168389 461228691934382544406573)
                    ·
                      rfl

theorem cell23_2694719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 4].length) (baseStart_2694719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694719 prefixEnd_2694719 := by exact prefixLift 2694719
  have htrace : WordTrace (prefixWord ++ tailWord_2694719) baseStart_2694719 baseEnd_2694719 := by
    simpa [prefixWord, tailWord_2694719, baseEnd_2694719] using wordTrace_append hprefix tailTrace_2694719
  have hstable : (prefixWord ++ tailWord_2694719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694719).length < 2 ^ (prefixWord ++ tailWord_2694719).sum := by decide
  have hdescent : baseEnd_2694719 < baseStart_2694719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694732 : List Nat := [2, 2, 1, 3, 1, 5, 1, 8]
def baseStart_2694732 : Nat := 118140960795 + 2694732 * 2 ^ 59
def prefixEnd_2694732 : Nat := 4983230072969 + 3 ^ 40 * 2694732 * 2
def baseEnd_2694732 : Nat := 51247879668579854902117

theorem tailTrace_2694732 : CollatzResearch.WordTrace tailWord_2694732 prefixEnd_2694732 51247879668579854902117 := by
  unfold tailWord_2694732
  simp only [CollatzResearch.WordTrace]
  refine ⟨49142475236726831215219225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65523300315635774953625633 49142475236726831215219225)
  ·
    refine ⟨36856856427545123411414419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49142475236726831215219225 36856856427545123411414419)
    ·
      refine ⟨55285284641317685117121629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36856856427545123411414419 55285284641317685117121629)
      ·
        refine ⟨20731981740494131918920611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55285284641317685117121629 20731981740494131918920611)
        ·
          refine ⟨31097972610741197878380917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20731981740494131918920611 31097972610741197878380917)
          ·
            refine ⟨2915434932256987301098211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31097972610741197878380917 2915434932256987301098211)
            ·
              refine ⟨4373152398385480951647317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2915434932256987301098211 4373152398385480951647317)
              ·
                refine ⟨51247879668579854902117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4373152398385480951647317 51247879668579854902117)
                ·
                  rfl

theorem cell23_2694732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 8].length) (baseStart_2694732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694732 prefixEnd_2694732 := by exact prefixLift 2694732
  have htrace : WordTrace (prefixWord ++ tailWord_2694732) baseStart_2694732 baseEnd_2694732 := by
    simpa [prefixWord, tailWord_2694732, baseEnd_2694732] using wordTrace_append hprefix tailTrace_2694732
  have hstable : (prefixWord ++ tailWord_2694732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694732).length < 2 ^ (prefixWord ++ tailWord_2694732).sum := by decide
  have hdescent : baseEnd_2694732 < baseStart_2694732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694760 : List Nat := [2, 1, 4, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2694760 : Nat := 118140960795 + 2694760 * 2 ^ 59
def prefixEnd_2694760 : Nat := 4983230072969 + 3 ^ 40 * 2694760 * 2
def baseEnd_2694760 : Nat := 1383707128509981972807031

theorem tailTrace_2694760 : CollatzResearch.WordTrace tailWord_2694760 prefixEnd_2694760 1383707128509981972807031 := by
  unfold tailWord_2694760
  simp only [CollatzResearch.WordTrace]
  refine ⟨49142985858676111606228867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65523981144901482141638489 49142985858676111606228867)
  ·
    refine ⟨73714478788014167409343301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49142985858676111606228867 73714478788014167409343301)
    ·
      refine ⟨13821464772752656389251869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73714478788014167409343301 13821464772752656389251869)
      ·
        refine ⟨5183049289782246145969451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13821464772752656389251869 5183049289782246145969451)
        ·
          refine ⟨7774573934673369218954177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5183049289782246145969451 7774573934673369218954177)
          ·
            refine ⟨5830930451005026914215633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7774573934673369218954177 5830930451005026914215633)
            ·
              refine ⟨4373197838253770185661725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5830930451005026914215633 4373197838253770185661725)
              ·
                refine ⟨1639949189345163819623147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4373197838253770185661725 1639949189345163819623147)
                ·
                  refine ⟨2459923784017745729434721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639949189345163819623147 2459923784017745729434721)
                  ·
                    refine ⟨1844942838013309297076041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2459923784017745729434721 1844942838013309297076041)
                    ·
                      refine ⟨1383707128509981972807031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844942838013309297076041 1383707128509981972807031)
                      ·
                        rfl

theorem cell23_2694760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2694760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694760 prefixEnd_2694760 := by exact prefixLift 2694760
  have htrace : WordTrace (prefixWord ++ tailWord_2694760) baseStart_2694760 baseEnd_2694760 := by
    simpa [prefixWord, tailWord_2694760, baseEnd_2694760] using wordTrace_append hprefix tailTrace_2694760
  have hstable : (prefixWord ++ tailWord_2694760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694760).length < 2 ^ (prefixWord ++ tailWord_2694760).sum := by decide
  have hdescent : baseEnd_2694760 < baseStart_2694760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694799 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 8, 2, 2]
def baseStart_2694799 : Nat := 118140960795 + 2694799 * 2 ^ 59
def prefixEnd_2694799 : Nat := 4983230072969 + 3 ^ 40 * 2694799 * 2
def baseEnd_2694799 : Nat := 1383727154255507320219351

theorem tailTrace_2694799 : CollatzResearch.WordTrace tailWord_2694799 prefixEnd_2694799 1383727154255507320219351 := by
  unfold tailWord_2694799
  simp only [CollatzResearch.WordTrace]
  refine ⟨98287394164210932873127451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65524929442807288582084967 98287394164210932873127451)
  ·
    refine ⟨147431091246316399309691177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98287394164210932873127451 147431091246316399309691177)
    ·
      refine ⟨110573318434737299482268383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147431091246316399309691177 110573318434737299482268383)
      ·
        refine ⟨165859977652105949223402575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110573318434737299482268383 165859977652105949223402575)
        ·
          refine ⟨248789966478158923835103863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165859977652105949223402575 248789966478158923835103863)
          ·
            refine ⟨373184949717238385752655795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248789966478158923835103863 373184949717238385752655795)
            ·
              refine ⟨559777424575857578628983693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373184949717238385752655795 559777424575857578628983693)
              ·
                refine ⟨209916534215946591985868885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559777424575857578628983693 209916534215946591985868885)
                ·
                  refine ⟨2459959385343124124834401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 209916534215946591985868885 2459959385343124124834401)
                  ·
                    refine ⟨1844969539007343093625801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2459959385343124124834401 1844969539007343093625801)
                    ·
                      refine ⟨1383727154255507320219351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844969539007343093625801 1383727154255507320219351)
                      ·
                        rfl

theorem cell23_2694799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 2, 2].length) (baseStart_2694799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694799 prefixEnd_2694799 := by exact prefixLift 2694799
  have htrace : WordTrace (prefixWord ++ tailWord_2694799) baseStart_2694799 baseEnd_2694799 := by
    simpa [prefixWord, tailWord_2694799, baseEnd_2694799] using wordTrace_append hprefix tailTrace_2694799
  have hstable : (prefixWord ++ tailWord_2694799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694799).length < 2 ^ (prefixWord ++ tailWord_2694799).sum := by decide
  have hdescent : baseEnd_2694799 < baseStart_2694799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694816 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 4, 2, 2]
def baseStart_2694816 : Nat := 118140960795 + 2694816 * 2 ^ 59
def prefixEnd_2694816 : Nat := 4983230072969 + 3 ^ 40 * 2694816 * 2
def baseEnd_2694816 : Nat := 1383735883426633753706773

theorem tailTrace_2694816 : CollatzResearch.WordTrace tailWord_2694816 prefixEnd_2694816 1383735883426633753706773 := by
  unfold tailWord_2694816
  simp only [CollatzResearch.WordTrace]
  refine ⟨49144007102574672388248151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65525342803432896517664201 49144007102574672388248151)
  ·
    refine ⟨73716010653862008582372227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49144007102574672388248151 73716010653862008582372227)
    ·
      refine ⟨110574015980793012873558341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73716010653862008582372227 110574015980793012873558341)
      ·
        refine ⟨20732627996398689913792189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110574015980793012873558341 20732627996398689913792189)
        ·
          refine ⟨7774735498649508717672071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20732627996398689913792189 7774735498649508717672071)
          ·
            refine ⟨11662103247974263076508107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774735498649508717672071 11662103247974263076508107)
            ·
              refine ⟨17493154871961394614762161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11662103247974263076508107 17493154871961394614762161)
              ·
                refine ⟨13119866153971045961071621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17493154871961394614762161 13119866153971045961071621)
                ·
                  refine ⟨2459974903869571117700929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13119866153971045961071621 2459974903869571117700929)
                  ·
                    refine ⟨1844981177902178338275697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2459974903869571117700929 1844981177902178338275697)
                    ·
                      refine ⟨1383735883426633753706773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1844981177902178338275697 1383735883426633753706773)
                      ·
                        rfl

theorem cell23_2694816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_2694816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694816 prefixEnd_2694816 := by exact prefixLift 2694816
  have htrace : WordTrace (prefixWord ++ tailWord_2694816) baseStart_2694816 baseEnd_2694816 := by
    simpa [prefixWord, tailWord_2694816, baseEnd_2694816] using wordTrace_append hprefix tailTrace_2694816
  have hstable : (prefixWord ++ tailWord_2694816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694816).length < 2 ^ (prefixWord ++ tailWord_2694816).sum := by decide
  have hdescent : baseEnd_2694816 < baseStart_2694816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694825 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_2694825 : Nat := 118140960795 + 2694825 * 2 ^ 59
def prefixEnd_2694825 : Nat := 4983230072969 + 3 ^ 40 * 2694825 * 2
def baseEnd_2694825 : Nat := 1383740504752524218494231

theorem tailTrace_2694825 : CollatzResearch.WordTrace tailWord_2694825 prefixEnd_2694825 1383740504752524218494231 := by
  unfold tailWord_2694825
  simp only [CollatzResearch.WordTrace]
  refine ⟨98288342462116739313573929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65525561641411159542382619 98288342462116739313573929)
  ·
    refine ⟨73716256846587554485180447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98288342462116739313573929 73716256846587554485180447)
    ·
      refine ⟨110574385269881331727770671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73716256846587554485180447 110574385269881331727770671)
      ·
        refine ⟨165861577904821997591656007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110574385269881331727770671 165861577904821997591656007)
        ·
          refine ⟨248792366857232996387484011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165861577904821997591656007 248792366857232996387484011)
          ·
            refine ⟨373188550285849494581226017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248792366857232996387484011 373188550285849494581226017)
            ·
              refine ⟨279891412714387120935919513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373188550285849494581226017 279891412714387120935919513)
              ·
                refine ⟨209918559535790340701939635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279891412714387120935919513 209918559535790340701939635)
                ·
                  refine ⟨314877839303685511052909453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209918559535790340701939635 314877839303685511052909453)
                  ·
                    refine ⟨118079189738882066644841045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 314877839303685511052909453 118079189738882066644841045)
                    ·
                      refine ⟨1383740504752524218494231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 118079189738882066644841045 1383740504752524218494231)
                      ·
                        rfl

theorem cell23_2694825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_2694825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694825 prefixEnd_2694825 := by exact prefixLift 2694825
  have htrace : WordTrace (prefixWord ++ tailWord_2694825) baseStart_2694825 baseEnd_2694825 := by
    simpa [prefixWord, tailWord_2694825, baseEnd_2694825] using wordTrace_append hprefix tailTrace_2694825
  have hstable : (prefixWord ++ tailWord_2694825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694825).length < 2 ^ (prefixWord ++ tailWord_2694825).sum := by decide
  have hdescent : baseEnd_2694825 < baseStart_2694825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694832 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 3]
def baseStart_2694832 : Nat := 118140960795 + 2694832 * 2 ^ 59
def prefixEnd_2694832 : Nat := 4983230072969 + 3 ^ 40 * 2694832 * 2
def baseEnd_2694832 : Nat := 1383744099117105691106699

theorem tailTrace_2694832 : CollatzResearch.WordTrace tailWord_2694832 prefixEnd_2694832 1383744099117105691106699 := by
  unfold tailWord_2694832
  simp only [CollatzResearch.WordTrace]
  refine ⟨49144298886545689754539375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65525731848727586339385833 49144298886545689754539375)
  ·
    refine ⟨73716448329818534631809063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49144298886545689754539375 73716448329818534631809063)
    ·
      refine ⟨110574672494727801947713595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73716448329818534631809063 110574672494727801947713595)
      ·
        refine ⟨165862008742091702921570393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110574672494727801947713595 165862008742091702921570393)
        ·
          refine ⟨124396506556568777191177795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165862008742091702921570393 124396506556568777191177795)
          ·
            refine ⟨186594759834853165786766693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124396506556568777191177795 186594759834853165786766693)
            ·
              refine ⟨34986517469034968585018755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186594759834853165786766693 34986517469034968585018755)
              ·
                refine ⟨52479776203552452877528133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34986517469034968585018755 52479776203552452877528133)
                ·
                  refine ⟨9839958038166084914536525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52479776203552452877528133 9839958038166084914536525)
                  ·
                    refine ⟨3689984264312281842951197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9839958038166084914536525 3689984264312281842951197)
                    ·
                      refine ⟨1383744099117105691106699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3689984264312281842951197 1383744099117105691106699)
                      ·
                        rfl

theorem cell23_2694832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 3].length) (baseStart_2694832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694832 prefixEnd_2694832 := by exact prefixLift 2694832
  have htrace : WordTrace (prefixWord ++ tailWord_2694832) baseStart_2694832 baseEnd_2694832 := by
    simpa [prefixWord, tailWord_2694832, baseEnd_2694832] using wordTrace_append hprefix tailTrace_2694832
  have hstable : (prefixWord ++ tailWord_2694832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694832).length < 2 ^ (prefixWord ++ tailWord_2694832).sum := by decide
  have hdescent : baseEnd_2694832 < baseStart_2694832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694839 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 7]
def baseStart_2694839 : Nat := 118140960795 + 2694839 * 2 ^ 59
def prefixEnd_2694839 : Nat := 4983230072969 + 3 ^ 40 * 2694839 * 2
def baseEnd_2694839 : Nat := 153749743720187462635463

theorem tailTrace_2694839 : CollatzResearch.WordTrace tailWord_2694839 prefixEnd_2694839 153749743720187462635463 := by
  unfold tailWord_2694839
  simp only [CollatzResearch.WordTrace]
  refine ⟨98288853084066019704583571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65525902056044013136389047 98288853084066019704583571)
  ·
    refine ⟨147433279626099029556875357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98288853084066019704583571 147433279626099029556875357)
    ·
      refine ⟨55287479859787136083828259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147433279626099029556875357 55287479859787136083828259)
      ·
        refine ⟨82931219789680704125742389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55287479859787136083828259 82931219789680704125742389)
        ·
          refine ⟨7774801855282566011788349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82931219789680704125742389 7774801855282566011788349)
          ·
            refine ⟨2915550695730962254420631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7774801855282566011788349 2915550695730962254420631)
            ·
              refine ⟨4373326043596443381630947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2915550695730962254420631 4373326043596443381630947)
              ·
                refine ⟨6559989065394665072446421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4373326043596443381630947 6559989065394665072446421)
                ·
                  refine ⟨153749743720187462635463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6559989065394665072446421 153749743720187462635463)
                  ·
                    rfl

theorem cell23_2694839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 7].length) (baseStart_2694839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694839 prefixEnd_2694839 := by exact prefixLift 2694839
  have htrace : WordTrace (prefixWord ++ tailWord_2694839) baseStart_2694839 baseEnd_2694839 := by
    simpa [prefixWord, tailWord_2694839, baseEnd_2694839] using wordTrace_append hprefix tailTrace_2694839
  have hstable : (prefixWord ++ tailWord_2694839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694839).length < 2 ^ (prefixWord ++ tailWord_2694839).sum := by decide
  have hdescent : baseEnd_2694839 < baseStart_2694839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694862 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2694862 : Nat := 118140960795 + 2694862 * 2 ^ 59
def prefixEnd_2694862 : Nat := 4983230072969 + 3 ^ 40 * 2694862 * 2
def baseEnd_2694862 : Nat := 1383759503536740573731561

theorem tailTrace_2694862 : CollatzResearch.WordTrace tailWord_2694862 prefixEnd_2694862 1383759503536740573731561 := by
  unfold tailWord_2694862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12286211495372836829083855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65526461308655129755113893 12286211495372836829083855)
  ·
    refine ⟨18429317243059255243625783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12286211495372836829083855 18429317243059255243625783)
    ·
      refine ⟨27643975864588882865438675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18429317243059255243625783 27643975864588882865438675)
      ·
        refine ⟨41465963796883324298158013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27643975864588882865438675 41465963796883324298158013)
        ·
          refine ⟨15549736423831246611809255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41465963796883324298158013 15549736423831246611809255)
          ·
            refine ⟨23324604635746869917713883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15549736423831246611809255 23324604635746869917713883)
            ·
              refine ⟨34986906953620304876570825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23324604635746869917713883 34986906953620304876570825)
              ·
                refine ⟨26240180215215228657428119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34986906953620304876570825 26240180215215228657428119)
                ·
                  refine ⟨39360270322822842986142179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26240180215215228657428119 39360270322822842986142179)
                  ·
                    refine ⟨59040405484234264479213269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39360270322822842986142179 59040405484234264479213269)
                    ·
                      refine ⟨1383759503536740573731561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59040405484234264479213269 1383759503536740573731561)
                      ·
                        rfl

theorem cell23_2694862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2694862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694862 prefixEnd_2694862 := by exact prefixLift 2694862
  have htrace : WordTrace (prefixWord ++ tailWord_2694862) baseStart_2694862 baseEnd_2694862 := by
    simpa [prefixWord, tailWord_2694862, baseEnd_2694862] using wordTrace_append hprefix tailTrace_2694862
  have hstable : (prefixWord ++ tailWord_2694862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694862).length < 2 ^ (prefixWord ++ tailWord_2694862).sum := by decide
  have hdescent : baseEnd_2694862 < baseStart_2694862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694889 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 2, 4, 2]
def baseStart_2694889 : Nat := 118140960795 + 2694889 * 2 ^ 59
def prefixEnd_2694889 : Nat := 4983230072969 + 3 ^ 40 * 2694889 * 2
def baseEnd_2694889 : Nat := 1383773367514411968093937

theorem tailTrace_2694889 : CollatzResearch.WordTrace tailWord_2694889 prefixEnd_2694889 1383773367514411968093937 := by
  unfold tailWord_2694889
  simp only [CollatzResearch.WordTrace]
  refine ⟨98290676733884878243903721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65527117822589918829269147 98290676733884878243903721)
  ·
    refine ⟨73718007550413658682927791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98290676733884878243903721 73718007550413658682927791)
    ·
      refine ⟨110577011325620488024391687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73718007550413658682927791 110577011325620488024391687)
      ·
        refine ⟨165865516988430732036587531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110577011325620488024391687 165865516988430732036587531)
        ·
          refine ⟨248798275482646098054881297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165865516988430732036587531 248798275482646098054881297)
          ·
            refine ⟨186598706611984573541160973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248798275482646098054881297 186598706611984573541160973)
            ·
              refine ⟨69974514979494215077935365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186598706611984573541160973 69974514979494215077935365)
              ·
                refine ⟨13120221558655165327112881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69974514979494215077935365 13120221558655165327112881)
                ·
                  refine ⟨9840166168991373995334661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13120221558655165327112881 9840166168991373995334661)
                  ·
                    refine ⟨1845031156685882624125249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9840166168991373995334661 1845031156685882624125249)
                    ·
                      refine ⟨1383773367514411968093937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845031156685882624125249 1383773367514411968093937)
                      ·
                        rfl

theorem cell23_2694889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 4, 2].length) (baseStart_2694889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694889 prefixEnd_2694889 := by exact prefixLift 2694889
  have htrace : WordTrace (prefixWord ++ tailWord_2694889) baseStart_2694889 baseEnd_2694889 := by
    simpa [prefixWord, tailWord_2694889, baseEnd_2694889] using wordTrace_append hprefix tailTrace_2694889
  have hstable : (prefixWord ++ tailWord_2694889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694889).length < 2 ^ (prefixWord ++ tailWord_2694889).sum := by decide
  have hdescent : baseEnd_2694889 < baseStart_2694889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694916 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_2694916 : Nat := 118140960795 + 2694916 * 2 ^ 59
def prefixEnd_2694916 : Nat := 4983230072969 + 3 ^ 40 * 2694916 * 2
def baseEnd_2694916 : Nat := 461262410497361120818771

theorem tailTrace_2694916 : CollatzResearch.WordTrace tailWord_2694916 prefixEnd_2694916 461262410497361120818771 := by
  unfold tailWord_2694916
  simp only [CollatzResearch.WordTrace]
  refine ⟨49145830752393530927568301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65527774336524707903424401 49145830752393530927568301)
  ·
    refine ⟨18429686532147574097838113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49145830752393530927568301 18429686532147574097838113)
    ·
      refine ⟨13822264899110680573378585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18429686532147574097838113 13822264899110680573378585)
      ·
        refine ⟨10366698674333010430033939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13822264899110680573378585 10366698674333010430033939)
        ·
          refine ⟨15550048011499515645050909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10366698674333010430033939 15550048011499515645050909)
          ·
            refine ⟨5831268004312318366894091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15550048011499515645050909 5831268004312318366894091)
            ·
              refine ⟨8746902006468477550341137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5831268004312318366894091 8746902006468477550341137)
              ·
                refine ⟨6560176504851358162755853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8746902006468477550341137 6560176504851358162755853)
                ·
                  refine ⟨2460066189319259311033445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6560176504851358162755853 2460066189319259311033445)
                  ·
                    refine ⟨461262410497361120818771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2460066189319259311033445 461262410497361120818771)
                    ·
                      rfl

theorem cell23_2694916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_2694916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694916 prefixEnd_2694916 := by exact prefixLift 2694916
  have htrace : WordTrace (prefixWord ++ tailWord_2694916) baseStart_2694916 baseEnd_2694916 := by
    simpa [prefixWord, tailWord_2694916, baseEnd_2694916] using wordTrace_append hprefix tailTrace_2694916
  have hstable : (prefixWord ++ tailWord_2694916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694916).length < 2 ^ (prefixWord ++ tailWord_2694916).sum := by decide
  have hdescent : baseEnd_2694916 < baseStart_2694916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694926 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2694926 : Nat := 118140960795 + 2694926 * 2 ^ 59
def prefixEnd_2694926 : Nat := 4983230072969 + 3 ^ 40 * 2694926 * 2
def baseEnd_2694926 : Nat := 1383792366298628323331267

theorem tailTrace_2694926 : CollatzResearch.WordTrace tailWord_2694926 prefixEnd_2694926 1383792366298628323331267 := by
  unfold tailWord_2694926
  simp only [CollatzResearch.WordTrace]
  refine ⟨12286503279343854195375079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65528017489833889042000421 12286503279343854195375079)
  ·
    refine ⟨18429754919015781293062619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12286503279343854195375079 18429754919015781293062619)
    ·
      refine ⟨27644632378523671939593929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18429754919015781293062619 27644632378523671939593929)
      ·
        refine ⟨20733474283892753954695447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27644632378523671939593929 20733474283892753954695447)
        ·
          refine ⟨31100211425839130932043171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20733474283892753954695447 31100211425839130932043171)
          ·
            refine ⟨46650317138758696398064757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31100211425839130932043171 46650317138758696398064757)
            ·
              refine ⟨4373467231758627787318571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46650317138758696398064757 4373467231758627787318571)
              ·
                refine ⟨6560200847637941680977857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4373467231758627787318571 6560200847637941680977857)
                ·
                  refine ⟨4920150635728456260733393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6560200847637941680977857 4920150635728456260733393)
                  ·
                    refine ⟨3690112976796342195550045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4920150635728456260733393 3690112976796342195550045)
                    ·
                      refine ⟨1383792366298628323331267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3690112976796342195550045 1383792366298628323331267)
                      ·
                        rfl

theorem cell23_2694926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2694926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694926 prefixEnd_2694926 := by exact prefixLift 2694926
  have htrace : WordTrace (prefixWord ++ tailWord_2694926) baseStart_2694926 baseEnd_2694926 := by
    simpa [prefixWord, tailWord_2694926, baseEnd_2694926] using wordTrace_append hprefix tailTrace_2694926
  have hstable : (prefixWord ++ tailWord_2694926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694926).length < 2 ^ (prefixWord ++ tailWord_2694926).sum := by decide
  have hdescent : baseEnd_2694926 < baseStart_2694926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694933 : List Nat := [1, 3, 2, 1, 2, 4, 2, 3, 1, 4]
def baseStart_2694933 : Nat := 118140960795 + 2694933 * 2 ^ 59
def prefixEnd_2694933 : Nat := 4983230072969 + 3 ^ 40 * 2694933 * 2
def baseEnd_2694933 : Nat := 461265320221069931981245

theorem tailTrace_2694933 : CollatzResearch.WordTrace tailWord_2694933 prefixEnd_2694933 461265320221069931981245 := by
  unfold tailWord_2694933
  simp only [CollatzResearch.WordTrace]
  refine ⟨98292281545725473758505453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65528187697150315839003635 98292281545725473758505453)
  ·
    refine ⟨36859605579647052659439545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98292281545725473758505453 36859605579647052659439545)
    ·
      refine ⟨27644704184735289494579659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36859605579647052659439545 27644704184735289494579659)
      ·
        refine ⟨41467056277102934241869489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27644704184735289494579659 41467056277102934241869489)
        ·
          refine ⟨31100292207827200681402117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41467056277102934241869489 31100292207827200681402117)
          ·
            refine ⟨5831304788967600127762897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31100292207827200681402117 5831304788967600127762897)
            ·
              refine ⟨4373478591725700095822173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5831304788967600127762897 4373478591725700095822173)
              ·
                refine ⟨1640054471897137535933315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4373478591725700095822173 1640054471897137535933315)
                ·
                  refine ⟨2460081707845706303899973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640054471897137535933315 2460081707845706303899973)
                  ·
                    refine ⟨461265320221069931981245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2460081707845706303899973 461265320221069931981245)
                    ·
                      rfl

theorem cell23_2694933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_2694933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694933 prefixEnd_2694933 := by exact prefixLift 2694933
  have htrace : WordTrace (prefixWord ++ tailWord_2694933) baseStart_2694933 baseEnd_2694933 := by
    simpa [prefixWord, tailWord_2694933, baseEnd_2694933] using wordTrace_append hprefix tailTrace_2694933
  have hstable : (prefixWord ++ tailWord_2694933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694933).length < 2 ^ (prefixWord ++ tailWord_2694933).sum := by decide
  have hdescent : baseEnd_2694933 < baseStart_2694933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694956 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 3]
def baseStart_2694956 : Nat := 118140960795 + 2694956 * 2 ^ 59
def prefixEnd_2694956 : Nat := 4983230072969 + 3 ^ 40 * 2694956 * 2
def baseEnd_2694956 : Nat := 1383807770718263205956129

theorem tailTrace_2694956 : CollatzResearch.WordTrace tailWord_2694956 prefixEnd_2694956 1383807770718263205956129 := by
  unfold tailWord_2694956
  simp only [CollatzResearch.WordTrace]
  refine ⟨49146560212321074343296361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65528746949761432457728481 49146560212321074343296361)
  ·
    refine ⟨36859920159240805757472271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49146560212321074343296361 36859920159240805757472271)
    ·
      refine ⟨55289880238861208636208407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36859920159240805757472271 55289880238861208636208407)
      ·
        refine ⟨82934820358291812954312611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55289880238861208636208407 82934820358291812954312611)
        ·
          refine ⟨124402230537437719431468917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82934820358291812954312611 124402230537437719431468917)
          ·
            refine ⟨11662709112884786196700211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124402230537437719431468917 11662709112884786196700211)
            ·
              refine ⟨17494063669327179295050317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11662709112884786196700211 17494063669327179295050317)
              ·
                refine ⟨6560273875997692235643869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17494063669327179295050317 6560273875997692235643869)
                ·
                  refine ⟨2460102703499134588366451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6560273875997692235643869 2460102703499134588366451)
                  ·
                    refine ⟨3690154055248701882549677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2460102703499134588366451 3690154055248701882549677)
                    ·
                      refine ⟨1383807770718263205956129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3690154055248701882549677 1383807770718263205956129)
                      ·
                        rfl

theorem cell23_2694956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_2694956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694956 prefixEnd_2694956 := by exact prefixLift 2694956
  have htrace : WordTrace (prefixWord ++ tailWord_2694956) baseStart_2694956 baseEnd_2694956 := by
    simpa [prefixWord, tailWord_2694956, baseEnd_2694956] using wordTrace_append hprefix tailTrace_2694956
  have hstable : (prefixWord ++ tailWord_2694956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694956).length < 2 ^ (prefixWord ++ tailWord_2694956).sum := by decide
  have hdescent : baseEnd_2694956 < baseStart_2694956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694973 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2694973 : Nat := 118140960795 + 2694973 * 2 ^ 59
def prefixEnd_2694973 : Nat := 4983230072969 + 3 ^ 40 * 2694973 * 2
def baseEnd_2694973 : Nat := 1383816499889389639443551

theorem tailTrace_2694973 : CollatzResearch.WordTrace tailWord_2694973 prefixEnd_2694973 1383816499889389639443551 := by
  unfold tailWord_2694973
  simp only [CollatzResearch.WordTrace]
  refine ⟨98293740465580560589961573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65529160310387040393307715 98293740465580560589961573)
  ·
    refine ⟨18430076337296355110617795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98293740465580560589961573 18430076337296355110617795)
    ·
      refine ⟨27645114505944532665926693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18430076337296355110617795 27645114505944532665926693)
      ·
        refine ⟨5183458969864599874861255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27645114505944532665926693 5183458969864599874861255)
        ·
          refine ⟨7775188454796899812291883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5183458969864599874861255 7775188454796899812291883)
          ·
            refine ⟨11662782682195349718437825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7775188454796899812291883 11662782682195349718437825)
            ·
              refine ⟨8747087011646512288828369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11662782682195349718437825 8747087011646512288828369)
              ·
                refine ⟨6560315258734884216621277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8747087011646512288828369 6560315258734884216621277)
                ·
                  refine ⟨2460118222025581581232979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6560315258734884216621277 2460118222025581581232979)
                  ·
                    refine ⟨3690177333038372371849469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2460118222025581581232979 3690177333038372371849469)
                    ·
                      refine ⟨1383816499889389639443551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3690177333038372371849469 1383816499889389639443551)
                      ·
                        rfl

theorem cell23_2694973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2694973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2694973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2694973 prefixEnd_2694973 := by exact prefixLift 2694973
  have htrace : WordTrace (prefixWord ++ tailWord_2694973) baseStart_2694973 baseEnd_2694973 := by
    simpa [prefixWord, tailWord_2694973, baseEnd_2694973] using wordTrace_append hprefix tailTrace_2694973
  have hstable : (prefixWord ++ tailWord_2694973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694973).length < 2 ^ (prefixWord ++ tailWord_2694973).sum := by decide
  have hdescent : baseEnd_2694973 < baseStart_2694973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695016 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2695016 : Nat := 118140960795 + 2695016 * 2 ^ 59
def prefixEnd_2695016 : Nat := 4983230072969 + 3 ^ 40 * 2695016 * 2
def baseEnd_2695016 : Nat := 1383838579557532971205853

theorem tailTrace_2695016 : CollatzResearch.WordTrace tailWord_2695016 prefixEnd_2695016 1383838579557532971205853 := by
  unfold tailWord_2695016
  simp only [CollatzResearch.WordTrace]
  refine ⟨49147654402212389466888451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65530205869616519289184601 49147654402212389466888451)
  ·
    refine ⟨73721481603318584200332677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49147654402212389466888451 73721481603318584200332677)
    ·
      refine ⟨13822777800622234537562377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73721481603318584200332677 13822777800622234537562377)
      ·
        refine ⟨10367083350466675903171783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13822777800622234537562377 10367083350466675903171783)
        ·
          refine ⟨15550625025700013854757675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10367083350466675903171783 15550625025700013854757675)
          ·
            refine ⟨23325937538550020782136513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15550625025700013854757675 23325937538550020782136513)
            ·
              refine ⟨17494453153912515586602385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23325937538550020782136513 17494453153912515586602385)
              ·
                refine ⟨13120839865434386689951789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17494453153912515586602385 13120839865434386689951789)
                ·
                  refine ⟨4920314949537895008731921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13120839865434386689951789 4920314949537895008731921)
                  ·
                    refine ⟨3690236212153421256548941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4920314949537895008731921 3690236212153421256548941)
                    ·
                      refine ⟨1383838579557532971205853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3690236212153421256548941 1383838579557532971205853)
                      ·
                        rfl

theorem cell23_2695016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2695016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695016 prefixEnd_2695016 := by exact prefixLift 2695016
  have htrace : WordTrace (prefixWord ++ tailWord_2695016) baseStart_2695016 baseEnd_2695016 := by
    simpa [prefixWord, tailWord_2695016, baseEnd_2695016] using wordTrace_append hprefix tailTrace_2695016
  have hstable : (prefixWord ++ tailWord_2695016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695016).length < 2 ^ (prefixWord ++ tailWord_2695016).sum := by decide
  have hdescent : baseEnd_2695016 < baseStart_2695016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695050 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5]
def baseStart_2695050 : Nat := 118140960795 + 2695050 * 2 ^ 59
def prefixEnd_2695050 : Nat := 4983230072969 + 3 ^ 40 * 2695050 * 2
def baseEnd_2695050 : Nat := 1383856037899785838180697

theorem tailTrace_2695050 : CollatzResearch.WordTrace tailWord_2695050 prefixEnd_2695050 1383856037899785838180697 := by
  unfold tailWord_2695050
  simp only [CollatzResearch.WordTrace]
  refine ⟨24574137221575400685128651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65531032590867735160343069 24574137221575400685128651)
  ·
    refine ⟨36861205832363101027692977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24574137221575400685128651 36861205832363101027692977)
    ·
      refine ⟨27645904374272325770769733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36861205832363101027692977 27645904374272325770769733)
      ·
        refine ⟨5183607070176061082019325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27645904374272325770769733 5183607070176061082019325)
        ·
          refine ⟨1943852651316022905757247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5183607070176061082019325 1943852651316022905757247)
          ·
            refine ⟨2915778976974034358635871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943852651316022905757247 2915778976974034358635871)
            ·
              refine ⟨4373668465461051537953807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2915778976974034358635871 4373668465461051537953807)
              ·
                refine ⟨6560502698191577306930711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4373668465461051537953807 6560502698191577306930711)
                ·
                  refine ⟨9840754047287365960396067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6560502698191577306930711 9840754047287365960396067)
                  ·
                    refine ⟨14761131070931048940594101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9840754047287365960396067 14761131070931048940594101)
                    ·
                      refine ⟨1383856037899785838180697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14761131070931048940594101 1383856037899785838180697)
                      ·
                        rfl

theorem cell23_2695050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_2695050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695050 prefixEnd_2695050 := by exact prefixLift 2695050
  have htrace : WordTrace (prefixWord ++ tailWord_2695050) baseStart_2695050 baseEnd_2695050 := by
    simpa [prefixWord, tailWord_2695050, baseEnd_2695050] using wordTrace_append hprefix tailTrace_2695050
  have hstable : (prefixWord ++ tailWord_2695050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695050).length < 2 ^ (prefixWord ++ tailWord_2695050).sum := by decide
  have hdescent : baseEnd_2695050 < baseStart_2695050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695056 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 5, 3, 2]
def baseStart_2695056 : Nat := 118140960795 + 2695056 * 2 ^ 59
def prefixEnd_2695056 : Nat := 4983230072969 + 3 ^ 40 * 2695056 * 2
def baseEnd_2695056 : Nat := 1383859118783712814705669

theorem tailTrace_2695056 : CollatzResearch.WordTrace tailWord_2695056 prefixEnd_2695056 1383859118783712814705669 := by
  unfold tailWord_2695056
  simp only [CollatzResearch.WordTrace]
  refine ⟨49148383862139932882616511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65531178482853243843488681 49148383862139932882616511)
  ·
    refine ⟨73722575793209899323924767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49148383862139932882616511 73722575793209899323924767)
    ·
      refine ⟨110583863689814848985887151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73722575793209899323924767 110583863689814848985887151)
      ·
        refine ⟨165875795534722273478830727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110583863689814848985887151 165875795534722273478830727)
        ·
          refine ⟨248813693302083410218246091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165875795534722273478830727 248813693302083410218246091)
          ·
            refine ⟨373220539953125115327369137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248813693302083410218246091 373220539953125115327369137)
            ·
              refine ⟨279915404964843836495526853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373220539953125115327369137 279915404964843836495526853)
              ·
                refine ⟨52484138430908219342911285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279915404964843836495526853 52484138430908219342911285)
                ·
                  refine ⟨4920387977897645563397933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52484138430908219342911285 4920387977897645563397933)
                  ·
                    refine ⟨1845145491711617086274225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4920387977897645563397933 1845145491711617086274225)
                    ·
                      refine ⟨1383859118783712814705669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845145491711617086274225 1383859118783712814705669)
                      ·
                        rfl

theorem cell23_2695056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 3, 2].length) (baseStart_2695056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695056 prefixEnd_2695056 := by exact prefixLift 2695056
  have htrace : WordTrace (prefixWord ++ tailWord_2695056) baseStart_2695056 baseEnd_2695056 := by
    simpa [prefixWord, tailWord_2695056, baseEnd_2695056] using wordTrace_append hprefix tailTrace_2695056
  have hstable : (prefixWord ++ tailWord_2695056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695056).length < 2 ^ (prefixWord ++ tailWord_2695056).sum := by decide
  have hdescent : baseEnd_2695056 < baseStart_2695056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695063 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 2, 1, 3]
def baseStart_2695063 : Nat := 118140960795 + 2695063 * 2 ^ 59
def prefixEnd_2695063 : Nat := 4983230072969 + 3 ^ 40 * 2695063 * 2
def baseEnd_2695063 : Nat := 1383862713148294287318137

theorem tailTrace_2695063 : CollatzResearch.WordTrace tailWord_2695063 prefixEnd_2695063 1383862713148294287318137 := by
  unfold tailWord_2695063
  simp only [CollatzResearch.WordTrace]
  refine ⟨98297023035254505960737843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65531348690169670640491895 98297023035254505960737843)
  ·
    refine ⟨147445534552881758941106765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98297023035254505960737843 147445534552881758941106765)
    ·
      refine ⟨55292075457330659602915037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147445534552881758941106765 55292075457330659602915037)
      ·
        refine ⟨20734528296498997351093139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55292075457330659602915037 20734528296498997351093139)
        ·
          refine ⟨31101792444748496026639709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20734528296498997351093139 31101792444748496026639709)
          ·
            refine ⟨11663172166780686009989891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31101792444748496026639709 11663172166780686009989891)
            ·
              refine ⟨17494758250171029014984837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11663172166780686009989891 17494758250171029014984837)
              ·
                refine ⟨3280267171907067940309657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17494758250171029014984837 3280267171907067940309657)
                ·
                  refine ⟨2460200378930300955232243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3280267171907067940309657 2460200378930300955232243)
                  ·
                    refine ⟨3690300568395451432848365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2460200378930300955232243 3690300568395451432848365)
                    ·
                      refine ⟨1383862713148294287318137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3690300568395451432848365 1383862713148294287318137)
                      ·
                        rfl

theorem cell23_2695063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_2695063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695063 prefixEnd_2695063 := by exact prefixLift 2695063
  have htrace : WordTrace (prefixWord ++ tailWord_2695063) baseStart_2695063 baseEnd_2695063 := by
    simpa [prefixWord, tailWord_2695063, baseEnd_2695063] using wordTrace_append hprefix tailTrace_2695063
  have hstable : (prefixWord ++ tailWord_2695063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695063).length < 2 ^ (prefixWord ++ tailWord_2695063).sum := by decide
  have hdescent : baseEnd_2695063 < baseStart_2695063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695064 : List Nat := [2, 1, 2, 6, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2695064 : Nat := 118140960795 + 2695064 * 2 ^ 59
def prefixEnd_2695064 : Nat := 4983230072969 + 3 ^ 40 * 2695064 * 2
def baseEnd_2695064 : Nat := 1383863226628948783405633

theorem tailTrace_2695064 : CollatzResearch.WordTrace tailWord_2695064 prefixEnd_2695064 1383863226628948783405633 := by
  unfold tailWord_2695064
  simp only [CollatzResearch.WordTrace]
  refine ⟨49148529754125441565762123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65531373005500588754349497 49148529754125441565762123)
  ·
    refine ⟨73722794631188162348643185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49148529754125441565762123 73722794631188162348643185)
    ·
      refine ⟨55292095973391121761482389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73722794631188162348643185 55292095973391121761482389)
      ·
        refine ⟨2591816998752708832569487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55292095973391121761482389 2591816998752708832569487)
        ·
          refine ⟨3887725498129063248854231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591816998752708832569487 3887725498129063248854231)
          ·
            refine ⟨5831588247193594873281347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887725498129063248854231 5831588247193594873281347)
            ·
              refine ⟨8747382370790392309922021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5831588247193594873281347 8747382370790392309922021)
              ·
                refine ⟨1640134194523198558110379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8747382370790392309922021 1640134194523198558110379)
                ·
                  refine ⟨2460201291784797837165569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640134194523198558110379 2460201291784797837165569)
                  ·
                    refine ⟨1845150968838598377874177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2460201291784797837165569 1845150968838598377874177)
                    ·
                      refine ⟨1383863226628948783405633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845150968838598377874177 1383863226628948783405633)
                      ·
                        rfl

theorem cell23_2695064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2695064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695064 prefixEnd_2695064 := by exact prefixLift 2695064
  have htrace : WordTrace (prefixWord ++ tailWord_2695064) baseStart_2695064 baseEnd_2695064 := by
    simpa [prefixWord, tailWord_2695064, baseEnd_2695064] using wordTrace_append hprefix tailTrace_2695064
  have hstable : (prefixWord ++ tailWord_2695064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695064).length < 2 ^ (prefixWord ++ tailWord_2695064).sum := by decide
  have hdescent : baseEnd_2695064 < baseStart_2695064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695070 : List Nat := [4, 3, 1, 3, 1, 2, 1, 8]
def baseStart_2695070 : Nat := 118140960795 + 2695070 * 2 ^ 59
def prefixEnd_2695070 : Nat := 4983230072969 + 3 ^ 40 * 2695070 * 2
def baseEnd_2695070 : Nat := 51254307685662065182615

theorem tailTrace_2695070 : CollatzResearch.WordTrace tailWord_2695070 prefixEnd_2695070 51254307685662065182615 := by
  unfold tailWord_2695070
  simp only [CollatzResearch.WordTrace]
  refine ⟨12287159793278643269530333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65531518897486097437495109 12287159793278643269530333)
  ·
    refine ⟨4607684922479491226073875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12287159793278643269530333 4607684922479491226073875)
    ·
      refine ⟨6911527383719236839110813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4607684922479491226073875 6911527383719236839110813)
      ·
        refine ⟨2591822768894713814666555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6911527383719236839110813 2591822768894713814666555)
        ·
          refine ⟨3887734153342070721999833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591822768894713814666555 3887734153342070721999833)
          ·
            refine ⟨2915800615006553041499875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3887734153342070721999833 2915800615006553041499875)
            ·
              refine ⟨4373700922509829562249813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2915800615006553041499875 4373700922509829562249813)
              ·
                refine ⟨51254307685662065182615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4373700922509829562249813 51254307685662065182615)
                ·
                  rfl

theorem cell23_2695070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_2695070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695070 prefixEnd_2695070 := by exact prefixLift 2695070
  have htrace : WordTrace (prefixWord ++ tailWord_2695070) baseStart_2695070 baseEnd_2695070 := by
    simpa [prefixWord, tailWord_2695070, baseEnd_2695070] using wordTrace_append hprefix tailTrace_2695070
  have hstable : (prefixWord ++ tailWord_2695070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695070).length < 2 ^ (prefixWord ++ tailWord_2695070).sum := by decide
  have hdescent : baseEnd_2695070 < baseStart_2695070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695099 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 4]
def baseStart_2695099 : Nat := 118140960795 + 2695099 * 2 ^ 59
def prefixEnd_2695099 : Nat := 4983230072969 + 3 ^ 40 * 2695099 * 2
def baseEnd_2695099 : Nat := 1383881198451856146467971

theorem tailTrace_2695099 : CollatzResearch.WordTrace tailWord_2695099 prefixEnd_2695099 1383881198451856146467971 := by
  unfold tailWord_2695099
  simp only [CollatzResearch.WordTrace]
  refine ⟨98298336063124084109048351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65532224042082722739365567 98298336063124084109048351)
  ·
    refine ⟨147447504094686126163572527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98298336063124084109048351 147447504094686126163572527)
    ·
      refine ⟨221171256142029189245358791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147447504094686126163572527 221171256142029189245358791)
      ·
        refine ⟨331756884213043783868038187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221171256142029189245358791 331756884213043783868038187)
        ·
          refine ⟨497635326319565675802057281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331756884213043783868038187 497635326319565675802057281)
          ·
            refine ⟨373226494739674256851542961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497635326319565675802057281 373226494739674256851542961)
            ·
              refine ⟨279919871054755692638657221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373226494739674256851542961 279919871054755692638657221)
              ·
                refine ⟨52484975822766692369748229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279919871054755692638657221 52484975822766692369748229)
                ·
                  refine ⟨9840932966768754819327793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52484975822766692369748229 9840932966768754819327793)
                  ·
                    refine ⟨7380699725076566114495845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9840932966768754819327793 7380699725076566114495845)
                    ·
                      refine ⟨1383881198451856146467971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7380699725076566114495845 1383881198451856146467971)
                      ·
                        rfl

theorem cell23_2695099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 4].length) (baseStart_2695099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695099 prefixEnd_2695099 := by exact prefixLift 2695099
  have htrace : WordTrace (prefixWord ++ tailWord_2695099) baseStart_2695099 baseEnd_2695099 := by
    simpa [prefixWord, tailWord_2695099, baseEnd_2695099] using wordTrace_append hprefix tailTrace_2695099
  have hstable : (prefixWord ++ tailWord_2695099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695099).length < 2 ^ (prefixWord ++ tailWord_2695099).sum := by decide
  have hdescent : baseEnd_2695099 < baseStart_2695099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695103 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 4, 2, 2]
def baseStart_2695103 : Nat := 118140960795 + 2695103 * 2 ^ 59
def prefixEnd_2695103 : Nat := 4983230072969 + 3 ^ 40 * 2695103 * 2
def baseEnd_2695103 : Nat := 1383883252374474130817953

theorem tailTrace_2695103 : CollatzResearch.WordTrace tailWord_2695103 prefixEnd_2695103 1383883252374474130817953 := by
  unfold tailWord_2695103
  simp only [CollatzResearch.WordTrace]
  refine ⟨98298481955109592792193963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65532321303406395194795975 98298481955109592792193963)
  ·
    refine ⟨147447722932664389188290945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98298481955109592792193963 147447722932664389188290945)
    ·
      refine ⟨110585792199498291891218209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147447722932664389188290945 110585792199498291891218209)
      ·
        refine ⟨82939344149623718918413657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110585792199498291891218209 82939344149623718918413657)
        ·
          refine ⟨62204508112217789188810243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82939344149623718918413657 62204508112217789188810243)
          ·
            refine ⟨93306762168326683783215365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62204508112217789188810243 93306762168326683783215365)
            ·
              refine ⟨17495017906561253209352881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93306762168326683783215365 17495017906561253209352881)
              ·
                refine ⟨13121263429920939907014661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17495017906561253209352881 13121263429920939907014661)
                ·
                  refine ⟨2460236893110176232565249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13121263429920939907014661 2460236893110176232565249)
                  ·
                    refine ⟨1845177669832632174423937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2460236893110176232565249 1845177669832632174423937)
                    ·
                      refine ⟨1383883252374474130817953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845177669832632174423937 1383883252374474130817953)
                      ·
                        rfl

theorem cell23_2695103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_2695103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695103 prefixEnd_2695103 := by exact prefixLift 2695103
  have htrace : WordTrace (prefixWord ++ tailWord_2695103) baseStart_2695103 baseEnd_2695103 := by
    simpa [prefixWord, tailWord_2695103, baseEnd_2695103] using wordTrace_append hprefix tailTrace_2695103
  have hstable : (prefixWord ++ tailWord_2695103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695103).length < 2 ^ (prefixWord ++ tailWord_2695103).sum := by decide
  have hdescent : baseEnd_2695103 < baseStart_2695103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695116 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2695116 : Nat := 118140960795 + 2695116 * 2 ^ 59
def prefixEnd_2695116 : Nat := 4983230072969 + 3 ^ 40 * 2695116 * 2
def baseEnd_2695116 : Nat := 1383889927622982579955393

theorem tailTrace_2695116 : CollatzResearch.WordTrace tailWord_2695116 prefixEnd_2695116 1383889927622982579955393 := by
  unfold tailWord_2695116
  simp only [CollatzResearch.WordTrace]
  refine ⟨49149478052031248006208601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65532637402708330674944801 49149478052031248006208601)
  ·
    refine ⟨36862108539023436004656451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49149478052031248006208601 36862108539023436004656451)
    ·
      refine ⟨55293162808535154006984677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36862108539023436004656451 55293162808535154006984677)
      ·
        refine ⟨10367468026600341376309627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55293162808535154006984677 10367468026600341376309627)
        ·
          refine ⟨15551202039900512064464441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10367468026600341376309627 15551202039900512064464441)
          ·
            refine ⟨11663401529925384048348331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15551202039900512064464441 11663401529925384048348331)
            ·
              refine ⟨17495102294888076072522497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11663401529925384048348331 17495102294888076072522497)
              ·
                refine ⟨13121326721166057054391873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17495102294888076072522497 13121326721166057054391873)
                ·
                  refine ⟨9840995040874542790793905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13121326721166057054391873 9840995040874542790793905)
                  ·
                    refine ⟨7380746280655907093095429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9840995040874542790793905 7380746280655907093095429)
                    ·
                      refine ⟨1383889927622982579955393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7380746280655907093095429 1383889927622982579955393)
                      ·
                        rfl

theorem cell23_2695116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2695116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695116 prefixEnd_2695116 := by exact prefixLift 2695116
  have htrace : WordTrace (prefixWord ++ tailWord_2695116) baseStart_2695116 baseEnd_2695116 := by
    simpa [prefixWord, tailWord_2695116, baseEnd_2695116] using wordTrace_append hprefix tailTrace_2695116
  have hstable : (prefixWord ++ tailWord_2695116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695116).length < 2 ^ (prefixWord ++ tailWord_2695116).sum := by decide
  have hdescent : baseEnd_2695116 < baseStart_2695116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695120 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 2, 2, 2]
def baseStart_2695120 : Nat := 118140960795 + 2695120 * 2 ^ 59
def prefixEnd_2695120 : Nat := 4983230072969 + 3 ^ 40 * 2695120 * 2
def baseEnd_2695120 : Nat := 1383891981545600564305375

theorem tailTrace_2695120 : CollatzResearch.WordTrace tailWord_2695120 prefixEnd_2695120 1383891981545600564305375 := by
  unfold tailWord_2695120
  simp only [CollatzResearch.WordTrace]
  refine ⟨49149550998024002347781407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65532734664032003130375209 49149550998024002347781407)
  ·
    refine ⟨73724326497036003521672111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49149550998024002347781407 73724326497036003521672111)
    ·
      refine ⟨110586489745554005282508167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73724326497036003521672111 110586489745554005282508167)
      ·
        refine ⟨165879734618331007923762251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110586489745554005282508167 165879734618331007923762251)
        ·
          refine ⟨248819601927496511885643377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165879734618331007923762251 248819601927496511885643377)
          ·
            refine ⟨186614701445622383914232533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248819601927496511885643377 186614701445622383914232533)
            ·
              refine ⟨4373782065131774622989825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 186614701445622383914232533 4373782065131774622989825)
              ·
                refine ⟨3280336548848830967242369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4373782065131774622989825 3280336548848830967242369)
                ·
                  refine ⟨2460252411636623225431777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3280336548848830967242369 2460252411636623225431777)
                  ·
                    refine ⟨1845189308727467419073833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2460252411636623225431777 1845189308727467419073833)
                    ·
                      refine ⟨1383891981545600564305375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845189308727467419073833 1383891981545600564305375)
                      ·
                        rfl

theorem cell23_2695120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2, 2, 2].length) (baseStart_2695120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695120 prefixEnd_2695120 := by exact prefixLift 2695120
  have htrace : WordTrace (prefixWord ++ tailWord_2695120) baseStart_2695120 baseEnd_2695120 := by
    simpa [prefixWord, tailWord_2695120, baseEnd_2695120] using wordTrace_append hprefix tailTrace_2695120
  have hstable : (prefixWord ++ tailWord_2695120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695120).length < 2 ^ (prefixWord ++ tailWord_2695120).sum := by decide
  have hdescent : baseEnd_2695120 < baseStart_2695120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695188 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_2695188 : Nat := 118140960795 + 2695188 * 2 ^ 59
def prefixEnd_2695188 : Nat := 4983230072969 + 3 ^ 40 * 2695188 * 2
def baseEnd_2695188 : Nat := 1383926898230106298255063

theorem tailTrace_2695188 : CollatzResearch.WordTrace tailWord_2695188 prefixEnd_2695188 1383926898230106298255063 := by
  unfold tailWord_2695188
  simp only [CollatzResearch.WordTrace]
  refine ⟨49150791079900826154519109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65534388106534434872692145 49150791079900826154519109)
  ·
    refine ⟨9215773327481404903972333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49150791079900826154519109 9215773327481404903972333)
    ·
      refine ⟨3455914997805526838989625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9215773327481404903972333 3455914997805526838989625)
      ·
        refine ⟨2591936248354145129242219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3455914997805526838989625 2591936248354145129242219)
        ·
          refine ⟨3887904372531217693863329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591936248354145129242219 3887904372531217693863329)
          ·
            refine ⟨2915928279398413270397497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3887904372531217693863329 2915928279398413270397497)
            ·
              refine ⟨2186946209548809952798123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2915928279398413270397497 2186946209548809952798123)
              ·
                refine ⟨3280419314323214929197185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2186946209548809952798123 3280419314323214929197185)
                ·
                  refine ⟨2460314485742411196897889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3280419314323214929197185 2460314485742411196897889)
                  ·
                    refine ⟨1845235864306808397673417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2460314485742411196897889 1845235864306808397673417)
                    ·
                      refine ⟨1383926898230106298255063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845235864306808397673417 1383926898230106298255063)
                      ·
                        rfl

theorem cell23_2695188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_2695188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695188 prefixEnd_2695188 := by exact prefixLift 2695188
  have htrace : WordTrace (prefixWord ++ tailWord_2695188) baseStart_2695188 baseEnd_2695188 := by
    simpa [prefixWord, tailWord_2695188, baseEnd_2695188] using wordTrace_append hprefix tailTrace_2695188
  have hstable : (prefixWord ++ tailWord_2695188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695188).length < 2 ^ (prefixWord ++ tailWord_2695188).sum := by decide
  have hdescent : baseEnd_2695188 < baseStart_2695188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695210 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_2695210 : Nat := 118140960795 + 2695210 * 2 ^ 59
def prefixEnd_2695210 : Nat := 4983230072969 + 3 ^ 40 * 2695210 * 2
def baseEnd_2695210 : Nat := 1383938194804505212179961

theorem tailTrace_2695210 : CollatzResearch.WordTrace tailWord_2695210 prefixEnd_2695210 1383938194804505212179961 := by
  unfold tailWord_2695210
  simp only [CollatzResearch.WordTrace]
  refine ⟨24575596141430487516584771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65534923043814633377559389 24575596141430487516584771)
  ·
    refine ⟨36863394212145731274877157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24575596141430487516584771 36863394212145731274877157)
    ·
      refine ⟨6911886414777324614039467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36863394212145731274877157 6911886414777324614039467)
      ·
        refine ⟨10367829622165986921059201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6911886414777324614039467 10367829622165986921059201)
        ·
          refine ⟨7775872216624490190794401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10367829622165986921059201 7775872216624490190794401)
          ·
            refine ⟨5831904162468367643095801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7775872216624490190794401 5831904162468367643095801)
            ·
              refine ⟨4373928121851275732321851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5831904162468367643095801 4373928121851275732321851)
              ·
                refine ⟨6560892182776913598482777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4373928121851275732321851 6560892182776913598482777)
                ·
                  refine ⟨4920669137082685198862083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6560892182776913598482777 4920669137082685198862083)
                  ·
                    refine ⟨7381003705624027798293125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4920669137082685198862083 7381003705624027798293125)
                    ·
                      refine ⟨1383938194804505212179961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7381003705624027798293125 1383938194804505212179961)
                      ·
                        rfl

theorem cell23_2695210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_2695210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695210 prefixEnd_2695210 := by exact prefixLift 2695210
  have htrace : WordTrace (prefixWord ++ tailWord_2695210) baseStart_2695210 baseEnd_2695210 := by
    simpa [prefixWord, tailWord_2695210, baseEnd_2695210] using wordTrace_append hprefix tailTrace_2695210
  have hstable : (prefixWord ++ tailWord_2695210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695210).length < 2 ^ (prefixWord ++ tailWord_2695210).sum := by decide
  have hdescent : baseEnd_2695210 < baseStart_2695210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695233 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 6]
def baseStart_2695233 : Nat := 118140960795 + 2695233 * 2 ^ 59
def prefixEnd_2695233 : Nat := 4983230072969 + 3 ^ 40 * 2695233 * 2
def baseEnd_2695233 : Nat := 153772222762173180243595

theorem tailTrace_2695233 : CollatzResearch.WordTrace tailWord_2695233 prefixEnd_2695233 153772222762173180243595 := by
  unfold tailWord_2695233
  simp only [CollatzResearch.WordTrace]
  refine ⟨98303223444638624994426353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65535482296425749996284235 98303223444638624994426353)
  ·
    refine ⟨73727417583478968745819765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98303223444638624994426353 73727417583478968745819765)
    ·
      refine ⟨6911945398451153319920603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73727417583478968745819765 6911945398451153319920603)
      ·
        refine ⟨10367918097676729979880905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6911945398451153319920603 10367918097676729979880905)
        ·
          refine ⟨7775938573257547484910679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10367918097676729979880905 7775938573257547484910679)
          ·
            refine ⟨11663907859886321227366019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7775938573257547484910679 11663907859886321227366019)
            ·
              refine ⟨17495861789829481841049029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11663907859886321227366019 17495861789829481841049029)
              ·
                refine ⟨3280474085593027845196693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17495861789829481841049029 3280474085593027845196693)
                ·
                  refine ⟨153772222762173180243595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3280474085593027845196693 153772222762173180243595)
                  ·
                    rfl

theorem cell23_2695233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 6].length) (baseStart_2695233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695233 prefixEnd_2695233 := by exact prefixLift 2695233
  have htrace : WordTrace (prefixWord ++ tailWord_2695233) baseStart_2695233 baseEnd_2695233 := by
    simpa [prefixWord, tailWord_2695233, baseEnd_2695233] using wordTrace_append hprefix tailTrace_2695233
  have hstable : (prefixWord ++ tailWord_2695233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695233).length < 2 ^ (prefixWord ++ tailWord_2695233).sum := by decide
  have hdescent : baseEnd_2695233 < baseStart_2695233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695260 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2695260 : Nat := 118140960795 + 2695260 * 2 ^ 59
def prefixEnd_2695260 : Nat := 4983230072969 + 3 ^ 40 * 2695260 * 2
def baseEnd_2695260 : Nat := 1383963868837230016554731

theorem tailTrace_2695260 : CollatzResearch.WordTrace tailWord_2695260 prefixEnd_2695260 1383963868837230016554731 := by
  unfold tailWord_2695260
  simp only [CollatzResearch.WordTrace]
  refine ⟨49152104107770404302829617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65536138810360539070439489 49152104107770404302829617)
  ·
    refine ⟨36864078080827803227122213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49152104107770404302829617 36864078080827803227122213)
    ·
      refine ⟨6912014640155213105085415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36864078080827803227122213 6912014640155213105085415)
      ·
        refine ⟨10368021960232819657628123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6912014640155213105085415 10368021960232819657628123)
        ·
          refine ⟨15552032940349229486442185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10368021960232819657628123 15552032940349229486442185)
          ·
            refine ⟨11664024705261922114831639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15552032940349229486442185 11664024705261922114831639)
            ·
              refine ⟨17496037057892883172247459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11664024705261922114831639 17496037057892883172247459)
              ·
                refine ⟨26244055586839324758371189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17496037057892883172247459 26244055586839324758371189)
                ·
                  refine ⟨2460380211266186696097299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26244055586839324758371189 2460380211266186696097299)
                  ·
                    refine ⟨3690570316899280044145949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2460380211266186696097299 3690570316899280044145949)
                    ·
                      refine ⟨1383963868837230016554731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3690570316899280044145949 1383963868837230016554731)
                      ·
                        rfl

theorem cell23_2695260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2695260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695260 prefixEnd_2695260 := by exact prefixLift 2695260
  have htrace : WordTrace (prefixWord ++ tailWord_2695260) baseStart_2695260 baseEnd_2695260 := by
    simpa [prefixWord, tailWord_2695260, baseEnd_2695260] using wordTrace_append hprefix tailTrace_2695260
  have hstable : (prefixWord ++ tailWord_2695260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695260).length < 2 ^ (prefixWord ++ tailWord_2695260).sum := by decide
  have hdescent : baseEnd_2695260 < baseStart_2695260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695280 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 1, 5]
def baseStart_2695280 : Nat := 118140960795 + 2695280 * 2 ^ 59
def prefixEnd_2695280 : Nat := 4983230072969 + 3 ^ 40 * 2695280 * 2
def baseEnd_2695280 : Nat := 461324712816773312768213

theorem tailTrace_2695280 : CollatzResearch.WordTrace tailWord_2695280 prefixEnd_2695280 461324712816773312768213 := by
  unfold tailWord_2695280
  simp only [CollatzResearch.WordTrace]
  refine ⟨49152468837734176010693647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65536625116978901347591529 49152468837734176010693647)
  ·
    refine ⟨73728703256601264016040471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49152468837734176010693647 73728703256601264016040471)
    ·
      refine ⟨110593054884901896024060707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73728703256601264016040471 110593054884901896024060707)
      ·
        refine ⟨165889582327352844036091061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110593054884901896024060707 165889582327352844036091061)
        ·
          refine ⟨15552148343189329128383537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165889582327352844036091061 15552148343189329128383537)
          ·
            refine ⟨11664111257391996846287653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15552148343189329128383537 11664111257391996846287653)
            ·
              refine ⟨2187020860760999408678935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11664111257391996846287653 2187020860760999408678935)
              ·
                refine ⟨3280531291141499113018403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187020860760999408678935 3280531291141499113018403)
                ·
                  refine ⟨4920796936712248669527605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3280531291141499113018403 4920796936712248669527605)
                  ·
                    refine ⟨461324712816773312768213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4920796936712248669527605 461324712816773312768213)
                    ·
                      rfl

theorem cell23_2695280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 5].length) (baseStart_2695280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695280 prefixEnd_2695280 := by exact prefixLift 2695280
  have htrace : WordTrace (prefixWord ++ tailWord_2695280) baseStart_2695280 baseEnd_2695280 := by
    simpa [prefixWord, tailWord_2695280, baseEnd_2695280] using wordTrace_append hprefix tailTrace_2695280
  have hstable : (prefixWord ++ tailWord_2695280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695280).length < 2 ^ (prefixWord ++ tailWord_2695280).sum := by decide
  have hdescent : baseEnd_2695280 < baseStart_2695280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695296 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_2695296 : Nat := 118140960795 + 2695296 * 2 ^ 59
def prefixEnd_2695296 : Nat := 4983230072969 + 3 ^ 40 * 2695296 * 2
def baseEnd_2695296 : Nat := 1383982354140791875704565

theorem tailTrace_2695296 : CollatzResearch.WordTrace tailWord_2695296 prefixEnd_2695296 1383982354140791875704565 := by
  unfold tailWord_2695296
  simp only [CollatzResearch.WordTrace]
  refine ⟨49152760621705193376984871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65537014162273591169313161 49152760621705193376984871)
  ·
    refine ⟨73729140932557790065477307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49152760621705193376984871 73729140932557790065477307)
    ·
      refine ⟨110593711398836685098215961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73729140932557790065477307 110593711398836685098215961)
      ·
        refine ⟨82945283549127513823661971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110593711398836685098215961 82945283549127513823661971)
        ·
          refine ⟨124417925323691270735492957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82945283549127513823661971 124417925323691270735492957)
          ·
            refine ⟨46656721996384226525809859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124417925323691270735492957 46656721996384226525809859)
            ·
              refine ⟨69985082994576339788714789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46656721996384226525809859 69985082994576339788714789)
              ·
                refine ⟨13122203061483063710384023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69985082994576339788714789 13122203061483063710384023)
                ·
                  refine ⟨19683304592224595565576035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13122203061483063710384023 19683304592224595565576035)
                  ·
                    refine ⟨29524956888336893348364053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19683304592224595565576035 29524956888336893348364053)
                    ·
                      refine ⟨1383982354140791875704565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29524956888336893348364053 1383982354140791875704565)
                      ·
                        rfl

theorem cell23_2695296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_2695296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695296 prefixEnd_2695296 := by exact prefixLift 2695296
  have htrace : WordTrace (prefixWord ++ tailWord_2695296) baseStart_2695296 baseEnd_2695296 := by
    simpa [prefixWord, tailWord_2695296, baseEnd_2695296] using wordTrace_append hprefix tailTrace_2695296
  have hstable : (prefixWord ++ tailWord_2695296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695296).length < 2 ^ (prefixWord ++ tailWord_2695296).sum := by decide
  have hdescent : baseEnd_2695296 < baseStart_2695296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695303 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_2695303 : Nat := 118140960795 + 2695303 * 2 ^ 59
def prefixEnd_2695303 : Nat := 4983230072969 + 3 ^ 40 * 2695303 * 2
def baseEnd_2695303 : Nat := 1383985948505373348317033

theorem tailTrace_2695303 : CollatzResearch.WordTrace tailWord_2695303 prefixEnd_2695303 1383985948505373348317033 := by
  unfold tailWord_2695303
  simp only [CollatzResearch.WordTrace]
  refine ⟨98305776554385026949474563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65537184369590017966316375 98305776554385026949474563)
  ·
    refine ⟨147458664831577540424211845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98305776554385026949474563 147458664831577540424211845)
    ·
      refine ⟨27648499655920788829539721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147458664831577540424211845 27648499655920788829539721)
      ·
        refine ⟨20736374741940591622154791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27648499655920788829539721 20736374741940591622154791)
        ·
          refine ⟨31104562112910887433232187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20736374741940591622154791 31104562112910887433232187)
          ·
            refine ⟨46656843169366331149848281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31104562112910887433232187 46656843169366331149848281)
            ·
              refine ⟨34992632377024748362386211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46656843169366331149848281 34992632377024748362386211)
              ·
                refine ⟨52488948565537122543579317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34992632377024748362386211 52488948565537122543579317)
                ·
                  refine ⟨4920838928019105238460561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52488948565537122543579317 4920838928019105238460561)
                  ·
                    refine ⟨3690629196014328928845421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4920838928019105238460561 3690629196014328928845421)
                    ·
                      refine ⟨1383985948505373348317033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3690629196014328928845421 1383985948505373348317033)
                      ·
                        rfl

theorem cell23_2695303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_2695303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695303 prefixEnd_2695303 := by exact prefixLift 2695303
  have htrace : WordTrace (prefixWord ++ tailWord_2695303) baseStart_2695303 baseEnd_2695303 := by
    simpa [prefixWord, tailWord_2695303, baseEnd_2695303] using wordTrace_append hprefix tailTrace_2695303
  have hstable : (prefixWord ++ tailWord_2695303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695303).length < 2 ^ (prefixWord ++ tailWord_2695303).sum := by decide
  have hdescent : baseEnd_2695303 < baseStart_2695303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695333 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 3, 3, 3]
def baseStart_2695333 : Nat := 118140960795 + 2695333 * 2 ^ 59
def prefixEnd_2695333 : Nat := 4983230072969 + 3 ^ 40 * 2695333 * 2
def baseEnd_2695333 : Nat := 1384001352925008230941895

theorem tailTrace_2695333 : CollatzResearch.WordTrace tailWord_2695333 prefixEnd_2695333 1384001352925008230941895 := by
  unfold tailWord_2695333
  simp only [CollatzResearch.WordTrace]
  refine ⟨98306870744276342073066653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65537913829517561382044435 98306870744276342073066653)
  ·
    refine ⟨36865076529103628277399995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98306870744276342073066653 36865076529103628277399995)
    ·
      refine ⟨55297614793655442416099993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36865076529103628277399995 55297614793655442416099993)
      ·
        refine ⟨41473211095241581812074995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55297614793655442416099993 41473211095241581812074995)
        ·
          refine ⟨62209816642862372718112493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41473211095241581812074995 62209816642862372718112493)
          ·
            refine ⟨23328681241073389769292185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62209816642862372718112493 23328681241073389769292185)
            ·
              refine ⟨17496510930805042326969139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23328681241073389769292185 17496510930805042326969139)
              ·
                refine ⟨26244766396207563490453709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17496510930805042326969139 26244766396207563490453709)
                ·
                  refine ⟨9841787398577836308920141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26244766396207563490453709 9841787398577836308920141)
                  ·
                    refine ⟨3690670274466688615845053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9841787398577836308920141 3690670274466688615845053)
                    ·
                      refine ⟨1384001352925008230941895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3690670274466688615845053 1384001352925008230941895)
                      ·
                        rfl

theorem cell23_2695333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_2695333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695333 prefixEnd_2695333 := by exact prefixLift 2695333
  have htrace : WordTrace (prefixWord ++ tailWord_2695333) baseStart_2695333 baseEnd_2695333 := by
    simpa [prefixWord, tailWord_2695333, baseEnd_2695333] using wordTrace_append hprefix tailTrace_2695333
  have hstable : (prefixWord ++ tailWord_2695333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695333).length < 2 ^ (prefixWord ++ tailWord_2695333).sum := by decide
  have hdescent : baseEnd_2695333 < baseStart_2695333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695351 : List Nat := [1, 1, 3, 1, 4, 3, 3, 2, 1, 2, 2]
def baseStart_2695351 : Nat := 118140960795 + 2695351 * 2 ^ 59
def prefixEnd_2695351 : Nat := 4983230072969 + 3 ^ 40 * 2695351 * 2
def baseEnd_2695351 : Nat := 1384010595576789160516813

theorem tailTrace_2695351 : CollatzResearch.WordTrace tailWord_2695351 prefixEnd_2695351 1384010595576789160516813 := by
  unfold tailWord_2695351
  simp only [CollatzResearch.WordTrace]
  refine ⟨98307527258211131147221907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65538351505474087431481271 98307527258211131147221907)
  ·
    refine ⟨147461290887316696720832861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98307527258211131147221907 147461290887316696720832861)
    ·
      refine ⟨55297984082743761270312323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147461290887316696720832861 55297984082743761270312323)
      ·
        refine ⟨82946976124115641905468485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55297984082743761270312323 82946976124115641905468485)
        ·
          refine ⟨15552558023271682857275341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82946976124115641905468485 15552558023271682857275341)
          ·
            refine ⟨5832209258726881071478253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15552558023271682857275341 5832209258726881071478253)
            ·
              refine ⟨2187078472022580401804345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5832209258726881071478253 2187078472022580401804345)
              ·
                refine ⟨1640308854016935301353259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187078472022580401804345 1640308854016935301353259)
                ·
                  refine ⟨2460463281025402952029889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640308854016935301353259 2460463281025402952029889)
                  ·
                    refine ⟨1845347460769052214022417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2460463281025402952029889 1845347460769052214022417)
                    ·
                      refine ⟨1384010595576789160516813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845347460769052214022417 1384010595576789160516813)
                      ·
                        rfl

theorem cell23_2695351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 1, 2, 2].length) (baseStart_2695351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695351 prefixEnd_2695351 := by exact prefixLift 2695351
  have htrace : WordTrace (prefixWord ++ tailWord_2695351) baseStart_2695351 baseEnd_2695351 := by
    simpa [prefixWord, tailWord_2695351, baseEnd_2695351] using wordTrace_append hprefix tailTrace_2695351
  have hstable : (prefixWord ++ tailWord_2695351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695351).length < 2 ^ (prefixWord ++ tailWord_2695351).sum := by decide
  have hdescent : baseEnd_2695351 < baseStart_2695351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695361 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2695361 : Nat := 118140960795 + 2695361 * 2 ^ 59
def prefixEnd_2695361 : Nat := 4983230072969 + 3 ^ 40 * 2695361 * 2
def baseEnd_2695361 : Nat := 461338576794444707130589

theorem tailTrace_2695361 : CollatzResearch.WordTrace tailWord_2695361 prefixEnd_2695361 461338576794444707130589 := by
  unfold tailWord_2695361
  simp only [CollatzResearch.WordTrace]
  refine ⟨98307891988174902855085937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65538594658783268570057291 98307891988174902855085937)
  ·
    refine ⟨73730918991131177141314453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98307891988174902855085937 73730918991131177141314453)
    ·
      refine ⟨3456136827709273928499115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73730918991131177141314453 3456136827709273928499115)
      ·
        refine ⟨5184205241563910892748673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3456136827709273928499115 5184205241563910892748673)
        ·
          refine ⟨3888153931172933169561505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5184205241563910892748673 3888153931172933169561505)
          ·
            refine ⟨2916115448379699877171129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3888153931172933169561505 2916115448379699877171129)
            ·
              refine ⟨2187086586284774907878347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2916115448379699877171129 2187086586284774907878347)
              ·
                refine ⟨3280629879427162361817521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187086586284774907878347 3280629879427162361817521)
                ·
                  refine ⟨2460472409570371771363141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3280629879427162361817521 2460472409570371771363141)
                  ·
                    refine ⟨461338576794444707130589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2460472409570371771363141 461338576794444707130589)
                    ·
                      rfl

theorem cell23_2695361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2695361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695361 prefixEnd_2695361 := by exact prefixLift 2695361
  have htrace : WordTrace (prefixWord ++ tailWord_2695361) baseStart_2695361 baseEnd_2695361 := by
    simpa [prefixWord, tailWord_2695361, baseEnd_2695361] using wordTrace_append hprefix tailTrace_2695361
  have hstable : (prefixWord ++ tailWord_2695361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695361).length < 2 ^ (prefixWord ++ tailWord_2695361).sum := by decide
  have hdescent : baseEnd_2695361 < baseStart_2695361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695376 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_2695376 : Nat := 118140960795 + 2695376 * 2 ^ 59
def prefixEnd_2695376 : Nat := 4983230072969 + 3 ^ 40 * 2695376 * 2
def baseEnd_2695376 : Nat := 1384023432593151562704197

theorem tailTrace_2695376 : CollatzResearch.WordTrace tailWord_2695376 prefixEnd_2695376 1384023432593151562704197 := by
  unfold tailWord_2695376
  simp only [CollatzResearch.WordTrace]
  refine ⟨49154219541560280208440991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65538959388747040277921321 49154219541560280208440991)
  ·
    refine ⟨73731329312340420312661487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49154219541560280208440991 73731329312340420312661487)
    ·
      refine ⟨110596993968510630468992231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73731329312340420312661487 110596993968510630468992231)
      ·
        refine ⟨165895490952765945703488347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110596993968510630468992231 165895490952765945703488347)
        ·
          refine ⟨248843236429148918555232521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165895490952765945703488347 248843236429148918555232521)
          ·
            refine ⟨186632427321861688916424391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248843236429148918555232521 186632427321861688916424391)
            ·
              refine ⟨279948640982792533374636587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186632427321861688916424391 279948640982792533374636587)
              ·
                refine ⟨419922961474188800061954881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279948640982792533374636587 419922961474188800061954881)
                ·
                  refine ⟨314942221105641600046466161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419922961474188800061954881 314942221105641600046466161)
                  ·
                    refine ⟨236206665829231200034849621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 314942221105641600046466161 236206665829231200034849621)
                    ·
                      refine ⟨1384023432593151562704197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 236206665829231200034849621 1384023432593151562704197)
                      ·
                        rfl

theorem cell23_2695376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_2695376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695376 prefixEnd_2695376 := by exact prefixLift 2695376
  have htrace : WordTrace (prefixWord ++ tailWord_2695376) baseStart_2695376 baseEnd_2695376 := by
    simpa [prefixWord, tailWord_2695376, baseEnd_2695376] using wordTrace_append hprefix tailTrace_2695376
  have hstable : (prefixWord ++ tailWord_2695376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695376).length < 2 ^ (prefixWord ++ tailWord_2695376).sum := by decide
  have hdescent : baseEnd_2695376 < baseStart_2695376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695377 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 1, 3, 2]
def baseStart_2695377 : Nat := 118140960795 + 2695377 * 2 ^ 59
def prefixEnd_2695377 : Nat := 4983230072969 + 3 ^ 40 * 2695377 * 2
def baseEnd_2695377 : Nat := 1384023946073806058791693

theorem tailTrace_2695377 : CollatzResearch.WordTrace tailWord_2695377 prefixEnd_2695377 1384023946073806058791693 := by
  unfold tailWord_2695377
  simp only [CollatzResearch.WordTrace]
  refine ⟨98308475556116937587668385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65538983704077958391778923 98308475556116937587668385)
  ·
    refine ⟨73731356667087703190751289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98308475556116937587668385 73731356667087703190751289)
    ·
      refine ⟨55298517500315777393063467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73731356667087703190751289 55298517500315777393063467)
      ·
        refine ⟨82947776250473666089595201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55298517500315777393063467 82947776250473666089595201)
        ·
          refine ⟨62210832187855249567196401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82947776250473666089595201 62210832187855249567196401)
          ·
            refine ⟨46658124140891437175397301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62210832187855249567196401 46658124140891437175397301)
            ·
              refine ⟨4374199138208572235193497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46658124140891437175397301 4374199138208572235193497)
              ·
                refine ⟨3280649353656429176395123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4374199138208572235193497 3280649353656429176395123)
                ·
                  refine ⟨4920974030484643764592685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3280649353656429176395123 4920974030484643764592685)
                  ·
                    refine ⟨1845365261431741411722257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4920974030484643764592685 1845365261431741411722257)
                    ·
                      refine ⟨1384023946073806058791693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845365261431741411722257 1384023946073806058791693)
                      ·
                        rfl

theorem cell23_2695377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_2695377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695377 prefixEnd_2695377 := by exact prefixLift 2695377
  have htrace : WordTrace (prefixWord ++ tailWord_2695377) baseStart_2695377 baseEnd_2695377 := by
    simpa [prefixWord, tailWord_2695377, baseEnd_2695377] using wordTrace_append hprefix tailTrace_2695377
  have hstable : (prefixWord ++ tailWord_2695377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695377).length < 2 ^ (prefixWord ++ tailWord_2695377).sum := by decide
  have hdescent : baseEnd_2695377 < baseStart_2695377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695393 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_2695393 : Nat := 118140960795 + 2695393 * 2 ^ 59
def prefixEnd_2695393 : Nat := 4983230072969 + 3 ^ 40 * 2695393 * 2
def baseEnd_2695393 : Nat := 1384032161764277996191619

theorem tailTrace_2695393 : CollatzResearch.WordTrace tailWord_2695393 prefixEnd_2695393 1384032161764277996191619 := by
  unfold tailWord_2695393
  simp only [CollatzResearch.WordTrace]
  refine ⟨98309059124058972320250833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65539372749372648213500555 98309059124058972320250833)
  ·
    refine ⟨73731794343044229240188125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98309059124058972320250833 73731794343044229240188125)
    ·
      refine ⟨27649422878641585965070547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73731794343044229240188125 27649422878641585965070547)
      ·
        refine ⟨41474134317962378947605821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27649422878641585965070547 41474134317962378947605821)
        ·
          refine ⟨15552800369235892105352183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41474134317962378947605821 15552800369235892105352183)
          ·
            refine ⟨23329200553853838158028275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15552800369235892105352183 23329200553853838158028275)
            ·
              refine ⟨34993800830780757237042413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23329200553853838158028275 34993800830780757237042413)
              ·
                refine ⟨13122675311542783963890905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34993800830780757237042413 13122675311542783963890905)
                ·
                  refine ⟨9842006483657087972918179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13122675311542783963890905 9842006483657087972918179)
                  ·
                    refine ⟨14763009725485631959377269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9842006483657087972918179 14763009725485631959377269)
                    ·
                      refine ⟨1384032161764277996191619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14763009725485631959377269 1384032161764277996191619)
                      ·
                        rfl

theorem cell23_2695393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_2695393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695393 prefixEnd_2695393 := by exact prefixLift 2695393
  have htrace : WordTrace (prefixWord ++ tailWord_2695393) baseStart_2695393 baseEnd_2695393 := by
    simpa [prefixWord, tailWord_2695393, baseEnd_2695393] using wordTrace_append hprefix tailTrace_2695393
  have hstable : (prefixWord ++ tailWord_2695393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695393).length < 2 ^ (prefixWord ++ tailWord_2695393).sum := by decide
  have hdescent : baseEnd_2695393 < baseStart_2695393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695403 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 4]
def baseStart_2695403 : Nat := 118140960795 + 2695403 * 2 ^ 59
def prefixEnd_2695403 : Nat := 4983230072969 + 3 ^ 40 * 2695403 * 2
def baseEnd_2695403 : Nat := 1384037296570822957066573

theorem tailTrace_2695403 : CollatzResearch.WordTrace tailWord_2695403 prefixEnd_2695403 1384037296570822957066573 := by
  unfold tailWord_2695403
  simp only [CollatzResearch.WordTrace]
  refine ⟨98309423854022744028114863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65539615902681829352076575 98309423854022744028114863)
  ·
    refine ⟨147464135781034116042172295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98309423854022744028114863 147464135781034116042172295)
    ·
      refine ⟨221196203671551174063258443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147464135781034116042172295 221196203671551174063258443)
      ·
        refine ⟨331794305507326761094887665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221196203671551174063258443 331794305507326761094887665)
        ·
          refine ⟨248845729130495070821165749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331794305507326761094887665 248845729130495070821165749)
          ·
            refine ⟨23329287105983912889484289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 248845729130495070821165749 23329287105983912889484289)
            ·
              refine ⟨17496965329487934667113217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23329287105983912889484289 17496965329487934667113217)
              ·
                refine ⟨13122723997115951000334913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17496965329487934667113217 13122723997115951000334913)
                ·
                  refine ⟨9842042997836963250251185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13122723997115951000334913 9842042997836963250251185)
                  ·
                    refine ⟨7381532248377722437688389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9842042997836963250251185 7381532248377722437688389)
                    ·
                      refine ⟨1384037296570822957066573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7381532248377722437688389 1384037296570822957066573)
                      ·
                        rfl

theorem cell23_2695403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 4].length) (baseStart_2695403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695403 prefixEnd_2695403 := by exact prefixLift 2695403
  have htrace : WordTrace (prefixWord ++ tailWord_2695403) baseStart_2695403 baseEnd_2695403 := by
    simpa [prefixWord, tailWord_2695403, baseEnd_2695403] using wordTrace_append hprefix tailTrace_2695403
  have hstable : (prefixWord ++ tailWord_2695403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695403).length < 2 ^ (prefixWord ++ tailWord_2695403).sum := by decide
  have hdescent : baseEnd_2695403 < baseStart_2695403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695410 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2695410 : Nat := 118140960795 + 2695410 * 2 ^ 59
def prefixEnd_2695410 : Nat := 4983230072969 + 3 ^ 40 * 2695410 * 2
def baseEnd_2695410 : Nat := 1384040890935404429679041

theorem tailTrace_2695410 : CollatzResearch.WordTrace tailWord_2695410 prefixEnd_2695410 1384040890935404429679041 := by
  unfold tailWord_2695410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24577419791249346055904921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65539786109998256149079789 24577419791249346055904921)
  ·
    refine ⟨18433064843437009541928691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24577419791249346055904921 18433064843437009541928691)
    ·
      refine ⟨27649597265155514312893037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18433064843437009541928691 27649597265155514312893037)
      ·
        refine ⟨10368598974433317867334889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27649597265155514312893037 10368598974433317867334889)
        ·
          refine ⟨7776449230824988400501167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10368598974433317867334889 7776449230824988400501167)
          ·
            refine ⟨11664673846237482600751751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7776449230824988400501167 11664673846237482600751751)
            ·
              refine ⟨17497010769356223901127627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11664673846237482600751751 17497010769356223901127627)
              ·
                refine ⟨26245516154034335851691441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17497010769356223901127627 26245516154034335851691441)
                ·
                  refine ⟨19684137115525751888768581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26245516154034335851691441 19684137115525751888768581)
                  ·
                    refine ⟨3690775709161078479144109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19684137115525751888768581 3690775709161078479144109)
                    ·
                      refine ⟨1384040890935404429679041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3690775709161078479144109 1384040890935404429679041)
                      ·
                        rfl

theorem cell23_2695410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2695410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695410 prefixEnd_2695410 := by exact prefixLift 2695410
  have htrace : WordTrace (prefixWord ++ tailWord_2695410) baseStart_2695410 baseEnd_2695410 := by
    simpa [prefixWord, tailWord_2695410, baseEnd_2695410] using wordTrace_append hprefix tailTrace_2695410
  have hstable : (prefixWord ++ tailWord_2695410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695410).length < 2 ^ (prefixWord ++ tailWord_2695410).sum := by decide
  have hdescent : baseEnd_2695410 < baseStart_2695410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695420 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_2695420 : Nat := 118140960795 + 2695420 * 2 ^ 59
def prefixEnd_2695420 : Nat := 4983230072969 + 3 ^ 40 * 2695420 * 2
def baseEnd_2695420 : Nat := 1384046025741949390553995

theorem tailTrace_2695420 : CollatzResearch.WordTrace tailWord_2695420 prefixEnd_2695420 1384046025741949390553995 := by
  unfold tailWord_2695420
  simp only [CollatzResearch.WordTrace]
  refine ⟨49155021947480577965741857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65540029263307437287655809 49155021947480577965741857)
  ·
    refine ⟨36866266460610433474306393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49155021947480577965741857 36866266460610433474306393)
    ·
      refine ⟨27649699845457825105729795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36866266460610433474306393 27649699845457825105729795)
      ·
        refine ⟨41474549768186737658594693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27649699845457825105729795 41474549768186737658594693)
        ·
          refine ⟨7776478081535013310986505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41474549768186737658594693 7776478081535013310986505)
          ·
            refine ⟨5832358561151259983239879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7776478081535013310986505 5832358561151259983239879)
            ·
              refine ⟨8748537841726889974859819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832358561151259983239879 8748537841726889974859819)
              ·
                refine ⟨13122806762590334962289729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8748537841726889974859819 13122806762590334962289729)
                ·
                  refine ⟨9842105071942751221717297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13122806762590334962289729 9842105071942751221717297)
                  ·
                    refine ⟨7381578803957063416287973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9842105071942751221717297 7381578803957063416287973)
                    ·
                      refine ⟨1384046025741949390553995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7381578803957063416287973 1384046025741949390553995)
                      ·
                        rfl

theorem cell23_2695420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_2695420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695420 prefixEnd_2695420 := by exact prefixLift 2695420
  have htrace : WordTrace (prefixWord ++ tailWord_2695420) baseStart_2695420 baseEnd_2695420 := by
    simpa [prefixWord, tailWord_2695420, baseEnd_2695420] using wordTrace_append hprefix tailTrace_2695420
  have hstable : (prefixWord ++ tailWord_2695420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695420).length < 2 ^ (prefixWord ++ tailWord_2695420).sum := by decide
  have hdescent : baseEnd_2695420 < baseStart_2695420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695447 : List Nat := [1, 1, 3, 4, 1, 3, 2, 3, 5]
def baseStart_2695447 : Nat := 118140960795 + 2695447 * 2 ^ 59
def prefixEnd_2695447 : Nat := 4983230072969 + 3 ^ 40 * 2695447 * 2
def baseEnd_2695447 : Nat := 153784432191068976101819

theorem tailTrace_2695447 : CollatzResearch.WordTrace tailWord_2695447 prefixEnd_2695447 153784432191068976101819 := by
  unfold tailWord_2695447
  simp only [CollatzResearch.WordTrace]
  refine ⟨98311028665863339542716595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65540685777242226361811063 98311028665863339542716595)
  ·
    refine ⟨147466542998795009314074893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98311028665863339542716595 147466542998795009314074893)
    ·
      refine ⟨55299953624548128492778085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147466542998795009314074893 55299953624548128492778085)
      ·
        refine ⟨10368741304602774092395891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55299953624548128492778085 10368741304602774092395891)
        ·
          refine ⟨15553111956904161138593837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10368741304602774092395891 15553111956904161138593837)
          ·
            refine ⟨5832416983839060426972689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15553111956904161138593837 5832416983839060426972689)
            ·
              refine ⟨4374312737879295320229517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5832416983839060426972689 4374312737879295320229517)
              ·
                refine ⟨1640367276704735745086069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4374312737879295320229517 1640367276704735745086069)
                ·
                  refine ⟨153784432191068976101819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1640367276704735745086069 153784432191068976101819)
                  ·
                    rfl

theorem cell23_2695447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 5].length) (baseStart_2695447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695447 prefixEnd_2695447 := by exact prefixLift 2695447
  have htrace : WordTrace (prefixWord ++ tailWord_2695447) baseStart_2695447 baseEnd_2695447 := by
    simpa [prefixWord, tailWord_2695447, baseEnd_2695447] using wordTrace_append hprefix tailTrace_2695447
  have hstable : (prefixWord ++ tailWord_2695447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695447).length < 2 ^ (prefixWord ++ tailWord_2695447).sum := by decide
  have hdescent : baseEnd_2695447 < baseStart_2695447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695500 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2695500 : Nat := 118140960795 + 2695500 * 2 ^ 59
def prefixEnd_2695500 : Nat := 4983230072969 + 3 ^ 40 * 2695500 * 2
def baseEnd_2695500 : Nat := 1384087104194309077553627

theorem tailTrace_2695500 : CollatzResearch.WordTrace tailWord_2695500 prefixEnd_2695500 1384087104194309077553627 := by
  unfold tailWord_2695500
  simp only [CollatzResearch.WordTrace]
  refine ⟨49156480867335664797197977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65541974489780886396263969 49156480867335664797197977)
  ·
    refine ⟨36867360650501748597898483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49156480867335664797197977 36867360650501748597898483)
    ·
      refine ⟨55301040975752622896847725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36867360650501748597898483 55301040975752622896847725)
      ·
        refine ⟨20737890365907233586317897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55301040975752622896847725 20737890365907233586317897)
        ·
          refine ⟨15553417774430425189738423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20737890365907233586317897 15553417774430425189738423)
          ·
            refine ⟨23330126661645637784607635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15553417774430425189738423 23330126661645637784607635)
            ·
              refine ⟨34995189992468456676911453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23330126661645637784607635 34995189992468456676911453)
              ·
                refine ⟨13123196247175671253841795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34995189992468456676911453 13123196247175671253841795)
                ·
                  refine ⟨19684794370763506880762693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13123196247175671253841795 19684794370763506880762693)
                  ·
                    refine ⟨3690898944518157540143005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19684794370763506880762693 3690898944518157540143005)
                    ·
                      refine ⟨1384087104194309077553627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3690898944518157540143005 1384087104194309077553627)
                      ·
                        rfl

theorem cell23_2695500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2695500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695500 prefixEnd_2695500 := by exact prefixLift 2695500
  have htrace : WordTrace (prefixWord ++ tailWord_2695500) baseStart_2695500 baseEnd_2695500 := by
    simpa [prefixWord, tailWord_2695500, baseEnd_2695500] using wordTrace_append hprefix tailTrace_2695500
  have hstable : (prefixWord ++ tailWord_2695500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695500).length < 2 ^ (prefixWord ++ tailWord_2695500).sum := by decide
  have hdescent : baseEnd_2695500 < baseStart_2695500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695507 : List Nat := [1, 1, 1, 2, 1, 1, 4, 7, 1, 4]
def baseStart_2695507 : Nat := 118140960795 + 2695507 * 2 ^ 59
def prefixEnd_2695507 : Nat := 4983230072969 + 3 ^ 40 * 2695507 * 2
def baseEnd_2695507 : Nat := 461363566186296850055365

theorem tailTrace_2695507 : CollatzResearch.WordTrace tailWord_2695507 prefixEnd_2695507 461363566186296850055365 := by
  unfold tailWord_2695507
  simp only [CollatzResearch.WordTrace]
  refine ⟨98313217045645969789900775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65542144697097313193267183 98313217045645969789900775)
  ·
    refine ⟨147469825568468954684851163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98313217045645969789900775 147469825568468954684851163)
    ·
      refine ⟨221204738352703432027276745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147469825568468954684851163 221204738352703432027276745)
      ·
        refine ⟨165903553764527574020457559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221204738352703432027276745 165903553764527574020457559)
        ·
          refine ⟨248855330646791361030686339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165903553764527574020457559 248855330646791361030686339)
          ·
            refine ⟨373282995970187041546029509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248855330646791361030686339 373282995970187041546029509)
            ·
              refine ⟨69990561744410070289880533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 373282995970187041546029509 69990561744410070289880533)
              ·
                refine ⟨1640403790884611022419075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 69990561744410070289880533 1640403790884611022419075)
                ·
                  refine ⟨2460605686326916533628613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640403790884611022419075 2460605686326916533628613)
                  ·
                    refine ⟨461363566186296850055365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2460605686326916533628613 461363566186296850055365)
                    ·
                      rfl

theorem cell23_2695507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 1, 4].length) (baseStart_2695507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695507 prefixEnd_2695507 := by exact prefixLift 2695507
  have htrace : WordTrace (prefixWord ++ tailWord_2695507) baseStart_2695507 baseEnd_2695507 := by
    simpa [prefixWord, tailWord_2695507, baseEnd_2695507] using wordTrace_append hprefix tailTrace_2695507
  have hstable : (prefixWord ++ tailWord_2695507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695507).length < 2 ^ (prefixWord ++ tailWord_2695507).sum := by decide
  have hdescent : baseEnd_2695507 < baseStart_2695507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695543 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_2695543 : Nat := 118140960795 + 2695543 * 2 ^ 59
def prefixEnd_2695543 : Nat := 4983230072969 + 3 ^ 40 * 2695543 * 2
def baseEnd_2695543 : Nat := 1384109183862452409315929

theorem tailTrace_2695543 : CollatzResearch.WordTrace tailWord_2695543 prefixEnd_2695543 1384109183862452409315929 := by
  unfold tailWord_2695543
  simp only [CollatzResearch.WordTrace]
  refine ⟨98314530073515547938211283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65543020049010365292140855 98314530073515547938211283)
  ·
    refine ⟨147471795110273321907316925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98314530073515547938211283 147471795110273321907316925)
    ·
      refine ⟨55301923166352495715243847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147471795110273321907316925 55301923166352495715243847)
      ·
        refine ⟨82952884749528743572865771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55301923166352495715243847 82952884749528743572865771)
        ·
          refine ⟨124429327124293115359298657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82952884749528743572865771 124429327124293115359298657)
          ·
            refine ⟨93321995343219836519473993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124429327124293115359298657 93321995343219836519473993)
            ·
              refine ⟨69991496507414877389605495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93321995343219836519473993 69991496507414877389605495)
              ·
                refine ⟨104987244761122316084408243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69991496507414877389605495 104987244761122316084408243)
                ·
                  refine ⟨157480867141683474126612365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104987244761122316084408243 157480867141683474126612365)
                  ·
                    refine ⟨59055325178131302797479637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 157480867141683474126612365 59055325178131302797479637)
                    ·
                      refine ⟨1384109183862452409315929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59055325178131302797479637 1384109183862452409315929)
                      ·
                        rfl

theorem cell23_2695543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_2695543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695543 prefixEnd_2695543 := by exact prefixLift 2695543
  have htrace : WordTrace (prefixWord ++ tailWord_2695543) baseStart_2695543 baseEnd_2695543 := by
    simpa [prefixWord, tailWord_2695543, baseEnd_2695543] using wordTrace_append hprefix tailTrace_2695543
  have hstable : (prefixWord ++ tailWord_2695543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695543).length < 2 ^ (prefixWord ++ tailWord_2695543).sum := by decide
  have hdescent : baseEnd_2695543 < baseStart_2695543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695607 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 3]
def baseStart_2695607 : Nat := 118140960795 + 2695607 * 2 ^ 59
def prefixEnd_2695607 : Nat := 4983230072969 + 3 ^ 40 * 2695607 * 2
def baseEnd_2695607 : Nat := 1384142046624340158915635

theorem tailTrace_2695607 : CollatzResearch.WordTrace tailWord_2695607 prefixEnd_2695607 1384142046624340158915635 := by
  unfold tailWord_2695607
  simp only [CollatzResearch.WordTrace]
  refine ⟨98316864345283686868541075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65544576230189124579027383 98316864345283686868541075)
  ·
    refine ⟨147475296517925530302811613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98316864345283686868541075 147475296517925530302811613)
    ·
      refine ⟨55303236194222073863554355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147475296517925530302811613 55303236194222073863554355)
      ·
        refine ⟨82954854291333110795331533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55303236194222073863554355 82954854291333110795331533)
        ·
          refine ⟨31108070359249916548249325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82954854291333110795331533 31108070359249916548249325)
          ·
            refine ⟨11665526384718718705593497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31108070359249916548249325 11665526384718718705593497)
            ·
              refine ⟨8749144788539039029195123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11665526384718718705593497 8749144788539039029195123)
              ·
                refine ⟨13123717182808558543792685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8749144788539039029195123 13123717182808558543792685)
                ·
                  refine ⟨4921393943553209453922257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13123717182808558543792685 4921393943553209453922257)
                  ·
                    refine ⟨3691045457664907090441693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4921393943553209453922257 3691045457664907090441693)
                    ·
                      refine ⟨1384142046624340158915635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3691045457664907090441693 1384142046624340158915635)
                      ·
                        rfl

theorem cell23_2695607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_2695607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695607 prefixEnd_2695607 := by exact prefixLift 2695607
  have htrace : WordTrace (prefixWord ++ tailWord_2695607) baseStart_2695607 baseEnd_2695607 := by
    simpa [prefixWord, tailWord_2695607, baseEnd_2695607] using wordTrace_append hprefix tailTrace_2695607
  have hstable : (prefixWord ++ tailWord_2695607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695607).length < 2 ^ (prefixWord ++ tailWord_2695607).sum := by decide
  have hdescent : baseEnd_2695607 < baseStart_2695607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695624 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_2695624 : Nat := 118140960795 + 2695624 * 2 ^ 59
def prefixEnd_2695624 : Nat := 4983230072969 + 3 ^ 40 * 2695624 * 2
def baseEnd_2695624 : Nat := 1384150775795466592403057

theorem tailTrace_2695624 : CollatzResearch.WordTrace tailWord_2695624 prefixEnd_2695624 1384150775795466592403057 := by
  unfold tailWord_2695624
  simp only [CollatzResearch.WordTrace]
  refine ⟨49158742193111049385954963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65544989590814732514606617 49158742193111049385954963)
  ·
    refine ⟨73738113289666574078932445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49158742193111049385954963 73738113289666574078932445)
    ·
      refine ⟨27651792483624965279599667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73738113289666574078932445 27651792483624965279599667)
      ·
        refine ⟨41477688725437447919399501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27651792483624965279599667 41477688725437447919399501)
        ·
          refine ⟨15554133272039042969774813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41477688725437447919399501 15554133272039042969774813)
          ·
            refine ⟨5832799977014641113665555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15554133272039042969774813 5832799977014641113665555)
            ·
              refine ⟨8749199965521961670498333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832799977014641113665555 8749199965521961670498333)
              ·
                refine ⟨3280949987070735626436875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8749199965521961670498333 3280949987070735626436875)
                ·
                  refine ⟨4921424980606103439655313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3280949987070735626436875 4921424980606103439655313)
                  ·
                    refine ⟨3691068735454577579741485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4921424980606103439655313 3691068735454577579741485)
                    ·
                      refine ⟨1384150775795466592403057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3691068735454577579741485 1384150775795466592403057)
                      ·
                        rfl

theorem cell23_2695624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_2695624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695624 prefixEnd_2695624 := by exact prefixLift 2695624
  have htrace : WordTrace (prefixWord ++ tailWord_2695624) baseStart_2695624 baseEnd_2695624 := by
    simpa [prefixWord, tailWord_2695624, baseEnd_2695624] using wordTrace_append hprefix tailTrace_2695624
  have hstable : (prefixWord ++ tailWord_2695624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695624).length < 2 ^ (prefixWord ++ tailWord_2695624).sum := by decide
  have hdescent : baseEnd_2695624 < baseStart_2695624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695630 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2695630 : Nat := 118140960795 + 2695630 * 2 ^ 59
def prefixEnd_2695630 : Nat := 4983230072969 + 3 ^ 40 * 2695630 * 2
def baseEnd_2695630 : Nat := 1384153856679393568928029

theorem tailTrace_2695630 : CollatzResearch.WordTrace tailWord_2695630 prefixEnd_2695630 1384153856679393568928029 := by
  unfold tailWord_2695630
  simp only [CollatzResearch.WordTrace]
  refine ⟨12289712903025045224578543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65545135482800241197752229 12289712903025045224578543)
  ·
    refine ⟨18434569354537567836867815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12289712903025045224578543 18434569354537567836867815)
    ·
      refine ⟨27651854031806351755301723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18434569354537567836867815 27651854031806351755301723)
      ·
        refine ⟨41477781047709527632952585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27651854031806351755301723 41477781047709527632952585)
        ·
          refine ⟨31108335785782145724714439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41477781047709527632952585 31108335785782145724714439)
          ·
            refine ⟨46662503678673218587071659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31108335785782145724714439 46662503678673218587071659)
            ·
              refine ⟨69993755518009827880607489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46662503678673218587071659 69993755518009827880607489)
              ·
                refine ⟨52495316638507370910455617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69993755518009827880607489 52495316638507370910455617)
                ·
                  refine ⟨39371487478880528182841713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52495316638507370910455617 39371487478880528182841713)
                  ·
                    refine ⟨29528615609160396137131285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39371487478880528182841713 29528615609160396137131285)
                    ·
                      refine ⟨1384153856679393568928029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29528615609160396137131285 1384153856679393568928029)
                      ·
                        rfl

theorem cell23_2695630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2695630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695630 prefixEnd_2695630 := by exact prefixLift 2695630
  have htrace : WordTrace (prefixWord ++ tailWord_2695630) baseStart_2695630 baseEnd_2695630 := by
    simpa [prefixWord, tailWord_2695630, baseEnd_2695630] using wordTrace_append hprefix tailTrace_2695630
  have hstable : (prefixWord ++ tailWord_2695630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695630).length < 2 ^ (prefixWord ++ tailWord_2695630).sum := by decide
  have hdescent : baseEnd_2695630 < baseStart_2695630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695638 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_2695638 : Nat := 118140960795 + 2695638 * 2 ^ 59
def prefixEnd_2695638 : Nat := 4983230072969 + 3 ^ 40 * 2695638 * 2
def baseEnd_2695638 : Nat := 1384157964524629537627993

theorem tailTrace_2695638 : CollatzResearch.WordTrace tailWord_2695638 prefixEnd_2695638 1384157964524629537627993 := by
  unfold tailWord_2695638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144874688010711197682473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65545330005447586108613045 6144874688010711197682473)
  ·
    refine ⟨4608656016008033398261855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6144874688010711197682473 4608656016008033398261855)
    ·
      refine ⟨6912984024012050097392783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4608656016008033398261855 6912984024012050097392783)
      ·
        refine ⟨10369476036018075146089175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6912984024012050097392783 10369476036018075146089175)
        ·
          refine ⟨15554214054027112719133763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10369476036018075146089175 15554214054027112719133763)
          ·
            refine ⟨23331321081040669078700645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15554214054027112719133763 23331321081040669078700645)
            ·
              refine ⟨4374622702695125452256371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23331321081040669078700645 4374622702695125452256371)
              ·
                refine ⟨6561934054042688178384557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374622702695125452256371 6561934054042688178384557)
                ·
                  refine ⟨2460725270266008066894209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6561934054042688178384557 2460725270266008066894209)
                  ·
                    refine ⟨1845543952699506050170657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2460725270266008066894209 1845543952699506050170657)
                    ·
                      refine ⟨1384157964524629537627993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845543952699506050170657 1384157964524629537627993)
                      ·
                        rfl

theorem cell23_2695638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_2695638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695638 prefixEnd_2695638 := by exact prefixLift 2695638
  have htrace : WordTrace (prefixWord ++ tailWord_2695638) baseStart_2695638 baseEnd_2695638 := by
    simpa [prefixWord, tailWord_2695638, baseEnd_2695638] using wordTrace_append hprefix tailTrace_2695638
  have hstable : (prefixWord ++ tailWord_2695638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695638).length < 2 ^ (prefixWord ++ tailWord_2695638).sum := by decide
  have hdescent : baseEnd_2695638 < baseStart_2695638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695651 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 1, 2, 4]
def baseStart_2695651 : Nat := 118140960795 + 2695651 * 2 ^ 59
def prefixEnd_2695651 : Nat := 4983230072969 + 3 ^ 40 * 2695651 * 2
def baseEnd_2695651 : Nat := 1384164639773137986765433

theorem tailTrace_2695651 : CollatzResearch.WordTrace tailWord_2695651 prefixEnd_2695651 1384164639773137986765433 := by
  unfold tailWord_2695651
  simp only [CollatzResearch.WordTrace]
  refine ⟨98318469157124282383142807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65545646104749521588761871 98318469157124282383142807)
  ·
    refine ⟨147477703735686423574714211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98318469157124282383142807 147477703735686423574714211)
    ·
      refine ⟨221216555603529635362071317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147477703735686423574714211 221216555603529635362071317)
      ·
        refine ⟨10369526043915451657597093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 221216555603529635362071317 10369526043915451657597093)
        ·
          refine ⟨1944286133234147185799455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10369526043915451657597093 1944286133234147185799455)
          ·
            refine ⟨2916429199851220778699183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944286133234147185799455 2916429199851220778699183)
            ·
              refine ⟨4374643799776831168048775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916429199851220778699183 4374643799776831168048775)
              ·
                refine ⟨6561965699665246752073163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374643799776831168048775 6561965699665246752073163)
                ·
                  refine ⟨9842948549497870128109745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6561965699665246752073163 9842948549497870128109745)
                  ·
                    refine ⟨7382211412123402596082309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9842948549497870128109745 7382211412123402596082309)
                    ·
                      refine ⟨1384164639773137986765433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7382211412123402596082309 1384164639773137986765433)
                      ·
                        rfl

theorem cell23_2695651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_2695651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695651 prefixEnd_2695651 := by exact prefixLift 2695651
  have htrace : WordTrace (prefixWord ++ tailWord_2695651) baseStart_2695651 baseEnd_2695651 := by
    simpa [prefixWord, tailWord_2695651, baseEnd_2695651] using wordTrace_append hprefix tailTrace_2695651
  have hstable : (prefixWord ++ tailWord_2695651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695651).length < 2 ^ (prefixWord ++ tailWord_2695651).sum := by decide
  have hdescent : baseEnd_2695651 < baseStart_2695651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695681 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_2695681 : Nat := 118140960795 + 2695681 * 2 ^ 59
def prefixEnd_2695681 : Nat := 4983230072969 + 3 ^ 40 * 2695681 * 2
def baseEnd_2695681 : Nat := 1384180044192772869390295

theorem tailTrace_2695681 : CollatzResearch.WordTrace tailWord_2695681 prefixEnd_2695681 1384180044192772869390295 := by
  unfold tailWord_2695681
  simp only [CollatzResearch.WordTrace]
  refine ⟨98319563347015597506734897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65546375564677065004489931 98319563347015597506734897)
  ·
    refine ⟨73739672510261698130051173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98319563347015597506734897 73739672510261698130051173)
    ·
      refine ⟨13826188595674068399384595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73739672510261698130051173 13826188595674068399384595)
      ·
        refine ⟨20739282893511102599076893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13826188595674068399384595 20739282893511102599076893)
        ·
          refine ⟨7777231085066663474653835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20739282893511102599076893 7777231085066663474653835)
          ·
            refine ⟨11665846627599995211980753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7777231085066663474653835 11665846627599995211980753)
            ·
              refine ⟨8749384970699996408985565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11665846627599995211980753 8749384970699996408985565)
              ·
                refine ⟨3281019364012498653369587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8749384970699996408985565 3281019364012498653369587)
                ·
                  refine ⟨4921529046018747980054381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281019364012498653369587 4921529046018747980054381)
                  ·
                    refine ⟨1845573392257030492520393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4921529046018747980054381 1845573392257030492520393)
                    ·
                      refine ⟨1384180044192772869390295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845573392257030492520393 1384180044192772869390295)
                      ·
                        rfl

theorem cell23_2695681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_2695681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695681 prefixEnd_2695681 := by exact prefixLift 2695681
  have htrace : WordTrace (prefixWord ++ tailWord_2695681) baseStart_2695681 baseEnd_2695681 := by
    simpa [prefixWord, tailWord_2695681, baseEnd_2695681] using wordTrace_append hprefix tailTrace_2695681
  have hstable : (prefixWord ++ tailWord_2695681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695681).length < 2 ^ (prefixWord ++ tailWord_2695681).sum := by decide
  have hdescent : baseEnd_2695681 < baseStart_2695681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695732 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2695732 : Nat := 118140960795 + 2695732 * 2 ^ 59
def prefixEnd_2695732 : Nat := 4983230072969 + 3 ^ 40 * 2695732 * 2
def baseEnd_2695732 : Nat := 1384206231706152169852561

theorem tailTrace_2695732 : CollatzResearch.WordTrace tailWord_2695732 prefixEnd_2695732 1384206231706152169852561 := by
  unfold tailWord_2695732
  simp only [CollatzResearch.WordTrace]
  refine ⟨49160711734915416608420725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65547615646553888811227633 49160711734915416608420725)
  ·
    refine ⟨4608816725148320307039443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49160711734915416608420725 4608816725148320307039443)
    ·
      refine ⟨6913225087722480460559165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4608816725148320307039443 6913225087722480460559165)
      ·
        refine ⟨2592459407895930172709687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6913225087722480460559165 2592459407895930172709687)
        ·
          refine ⟨3888689111843895259064531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2592459407895930172709687 3888689111843895259064531)
          ·
            refine ⟨5833033667765842888596797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888689111843895259064531 5833033667765842888596797)
            ·
              refine ⟨2187387625412191083223799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5833033667765842888596797 2187387625412191083223799)
              ·
                refine ⟨3281081438118286624835699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187387625412191083223799 3281081438118286624835699)
                ·
                  refine ⟨4921622157177429937253549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281081438118286624835699 4921622157177429937253549)
                  ·
                    refine ⟨1845608308941536226470081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4921622157177429937253549 1845608308941536226470081)
                    ·
                      refine ⟨1384206231706152169852561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845608308941536226470081 1384206231706152169852561)
                      ·
                        rfl

theorem cell23_2695732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2695732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695732 prefixEnd_2695732 := by exact prefixLift 2695732
  have htrace : WordTrace (prefixWord ++ tailWord_2695732) baseStart_2695732 baseEnd_2695732 := by
    simpa [prefixWord, tailWord_2695732, baseEnd_2695732] using wordTrace_append hprefix tailTrace_2695732
  have hstable : (prefixWord ++ tailWord_2695732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695732).length < 2 ^ (prefixWord ++ tailWord_2695732).sum := by decide
  have hdescent : baseEnd_2695732 < baseStart_2695732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695751 : List Nat := [1, 1, 4, 1, 4, 1, 4, 2, 5]
def baseStart_2695751 : Nat := 118140960795 + 2695751 * 2 ^ 59
def prefixEnd_2695751 : Nat := 4983230072969 + 3 ^ 40 * 2695751 * 2
def baseEnd_2695751 : Nat := 153801776426509732834997

theorem tailTrace_2695751 : CollatzResearch.WordTrace tailWord_2695751 prefixEnd_2695751 153801776426509732834997 := by
  unfold tailWord_2695751
  simp only [CollatzResearch.WordTrace]
  refine ⟨98322116456761999461783107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65548077637841332974522071 98322116456761999461783107)
  ·
    refine ⟨147483174685142999192674661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98322116456761999461783107 147483174685142999192674661)
    ·
      refine ⟨27653095253464312348626499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147483174685142999192674661 27653095253464312348626499)
      ·
        refine ⟨41479642880196468522939749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27653095253464312348626499 41479642880196468522939749)
        ·
          refine ⟨7777433040036837848051203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41479642880196468522939749 7777433040036837848051203)
          ·
            refine ⟨11666149560055256772076805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7777433040036837848051203 11666149560055256772076805)
            ·
              refine ⟨2187403042510360644764401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11666149560055256772076805 2187403042510360644764401)
              ·
                refine ⟨1640552281882770483573301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187403042510360644764401 1640552281882770483573301)
                ·
                  refine ⟨153801776426509732834997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1640552281882770483573301 153801776426509732834997)
                  ·
                    rfl

theorem cell23_2695751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 5].length) (baseStart_2695751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695751 prefixEnd_2695751 := by exact prefixLift 2695751
  have htrace : WordTrace (prefixWord ++ tailWord_2695751) baseStart_2695751 baseEnd_2695751 := by
    simpa [prefixWord, tailWord_2695751, baseEnd_2695751] using wordTrace_append hprefix tailTrace_2695751
  have hstable : (prefixWord ++ tailWord_2695751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695751).length < 2 ^ (prefixWord ++ tailWord_2695751).sum := by decide
  have hdescent : baseEnd_2695751 < baseStart_2695751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695754 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2]
def baseStart_2695754 : Nat := 118140960795 + 2695754 * 2 ^ 59
def prefixEnd_2695754 : Nat := 4983230072969 + 3 ^ 40 * 2695754 * 2
def baseEnd_2695754 : Nat := 1384217528280551083777459

theorem tailTrace_2695754 : CollatzResearch.WordTrace tailWord_2695754 prefixEnd_2695754 1384217528280551083777459 := by
  unfold tailWord_2695754
  simp only [CollatzResearch.WordTrace]
  refine ⟨24580556468937782743535579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65548150583834087316094877 24580556468937782743535579)
  ·
    refine ⟨36870834703406674115303369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24580556468937782743535579 36870834703406674115303369)
    ·
      refine ⟨27653126027555005586477527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36870834703406674115303369 27653126027555005586477527)
      ·
        refine ⟨41479689041332508379716291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27653126027555005586477527 41479689041332508379716291)
        ·
          refine ⟨62219533561998762569574437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41479689041332508379716291 62219533561998762569574437)
          ·
            refine ⟨11666162542874767981795207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62219533561998762569574437 11666162542874767981795207)
            ·
              refine ⟨17499243814312151972692811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11666162542874767981795207 17499243814312151972692811)
              ·
                refine ⟨26248865721468227959039217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17499243814312151972692811 26248865721468227959039217)
                ·
                  refine ⟨19686649291101170969279413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26248865721468227959039217 19686649291101170969279413)
                  ·
                    refine ⟨1845623371040734778369945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19686649291101170969279413 1845623371040734778369945)
                    ·
                      refine ⟨1384217528280551083777459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845623371040734778369945 1384217528280551083777459)
                      ·
                        rfl

theorem cell23_2695754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_2695754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695754 prefixEnd_2695754 := by exact prefixLift 2695754
  have htrace : WordTrace (prefixWord ++ tailWord_2695754) baseStart_2695754 baseEnd_2695754 := by
    simpa [prefixWord, tailWord_2695754, baseEnd_2695754] using wordTrace_append hprefix tailTrace_2695754
  have hstable : (prefixWord ++ tailWord_2695754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695754).length < 2 ^ (prefixWord ++ tailWord_2695754).sum := by decide
  have hdescent : baseEnd_2695754 < baseStart_2695754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695767 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_2695767 : Nat := 118140960795 + 2695767 * 2 ^ 59
def prefixEnd_2695767 : Nat := 4983230072969 + 3 ^ 40 * 2695767 * 2
def baseEnd_2695767 : Nat := 1384224203529059532914899

theorem tailTrace_2695767 : CollatzResearch.WordTrace tailWord_2695767 prefixEnd_2695767 1384224203529059532914899 := by
  unfold tailWord_2695767
  simp only [CollatzResearch.WordTrace]
  refine ⟨98322700024704034194365555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65548466683136022796243703 98322700024704034194365555)
  ·
    refine ⟨147484050037056051291548333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98322700024704034194365555 147484050037056051291548333)
    ·
      refine ⟨55306518763896019234330625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147484050037056051291548333 55306518763896019234330625)
      ·
        refine ⟨41479889072922014425747969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55306518763896019234330625 41479889072922014425747969)
        ·
          refine ⟨31109916804691510819310977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41479889072922014425747969 31109916804691510819310977)
          ·
            refine ⟨23332437603518633114483233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31109916804691510819310977 23332437603518633114483233)
            ·
              refine ⟨17499328202638974835862425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23332437603518633114483233 17499328202638974835862425)
              ·
                refine ⟨13124496151979231126896819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17499328202638974835862425 13124496151979231126896819)
                ·
                  refine ⟨19686744227968846690345229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13124496151979231126896819 19686744227968846690345229)
                  ·
                    refine ⟨7382529085488317508879461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19686744227968846690345229 7382529085488317508879461)
                    ·
                      refine ⟨1384224203529059532914899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7382529085488317508879461 1384224203529059532914899)
                      ·
                        rfl

theorem cell23_2695767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_2695767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695767 prefixEnd_2695767 := by exact prefixLift 2695767
  have htrace : WordTrace (prefixWord ++ tailWord_2695767) baseStart_2695767 baseEnd_2695767 := by
    simpa [prefixWord, tailWord_2695767, baseEnd_2695767] using wordTrace_append hprefix tailTrace_2695767
  have hstable : (prefixWord ++ tailWord_2695767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695767).length < 2 ^ (prefixWord ++ tailWord_2695767).sum := by decide
  have hdescent : baseEnd_2695767 < baseStart_2695767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695781 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_2695781 : Nat := 118140960795 + 2695781 * 2 ^ 59
def prefixEnd_2695781 : Nat := 4983230072969 + 3 ^ 40 * 2695781 * 2
def baseEnd_2695781 : Nat := 461410464086074159379945

theorem tailTrace_2695781 : CollatzResearch.WordTrace tailWord_2695781 prefixEnd_2695781 461410464086074159379945 := by
  unfold tailWord_2695781
  simp only [CollatzResearch.WordTrace]
  refine ⟨98323210646653314585375197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65548807097768876390250131 98323210646653314585375197)
  ·
    refine ⟨36871203992494992969515699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98323210646653314585375197 36871203992494992969515699)
    ·
      refine ⟨55306805988742489454273549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36871203992494992969515699 55306805988742489454273549)
      ·
        refine ⟨20740052245778433545352581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55306805988742489454273549 20740052245778433545352581)
        ·
          refine ⟨3888759796083456289753609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20740052245778433545352581 3888759796083456289753609)
          ·
            refine ⟨2916569847062592217315207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3888759796083456289753609 2916569847062592217315207)
            ·
              refine ⟨4374854770593888325972811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916569847062592217315207 4374854770593888325972811)
              ·
                refine ⟨6562282155890832488959217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374854770593888325972811 6562282155890832488959217)
                ·
                  refine ⟨4921711616918124366719413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6562282155890832488959217 4921711616918124366719413)
                  ·
                    refine ⟨461410464086074159379945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4921711616918124366719413 461410464086074159379945)
                    ·
                      rfl

theorem cell23_2695781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_2695781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695781 prefixEnd_2695781 := by exact prefixLift 2695781
  have htrace : WordTrace (prefixWord ++ tailWord_2695781) baseStart_2695781 baseEnd_2695781 := by
    simpa [prefixWord, tailWord_2695781, baseEnd_2695781] using wordTrace_append hprefix tailTrace_2695781
  have hstable : (prefixWord ++ tailWord_2695781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695781).length < 2 ^ (prefixWord ++ tailWord_2695781).sum := by decide
  have hdescent : baseEnd_2695781 < baseStart_2695781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695804 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_2695804 : Nat := 118140960795 + 2695804 * 2 ^ 59
def prefixEnd_2695804 : Nat := 4983230072969 + 3 ^ 40 * 2695804 * 2
def baseEnd_2695804 : Nat := 1384243202313275888152229

theorem tailTrace_2695804 : CollatzResearch.WordTrace tailWord_2695804 prefixEnd_2695804 1384243202313275888152229 := by
  unfold tailWord_2695804
  simp only [CollatzResearch.WordTrace]
  refine ⟨49162024762784994756731233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65549366350379993008974977 49162024762784994756731233)
  ·
    refine ⟨36871518572088746067548425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49162024762784994756731233 36871518572088746067548425)
    ·
      refine ⟨27653638929066559550661319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36871518572088746067548425 27653638929066559550661319)
      ·
        refine ⟨41480458393599839325991979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27653638929066559550661319 41480458393599839325991979)
        ·
          refine ⟨62220687590399758988987969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41480458393599839325991979 62220687590399758988987969)
          ·
            refine ⟨46665515692799819241740977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62220687590399758988987969 46665515692799819241740977)
            ·
              refine ⟨34999136769599864431305733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46665515692799819241740977 34999136769599864431305733)
              ·
                refine ⟨6562338144299974580869825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34999136769599864431305733 6562338144299974580869825)
                ·
                  refine ⟨4921753608224980935652369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6562338144299974580869825 4921753608224980935652369)
                  ·
                    refine ⟨3691315206168735701739277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4921753608224980935652369 3691315206168735701739277)
                    ·
                      refine ⟨1384243202313275888152229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3691315206168735701739277 1384243202313275888152229)
                      ·
                        rfl

theorem cell23_2695804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_2695804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695804 prefixEnd_2695804 := by exact prefixLift 2695804
  have htrace : WordTrace (prefixWord ++ tailWord_2695804) baseStart_2695804 baseEnd_2695804 := by
    simpa [prefixWord, tailWord_2695804, baseEnd_2695804] using wordTrace_append hprefix tailTrace_2695804
  have hstable : (prefixWord ++ tailWord_2695804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695804).length < 2 ^ (prefixWord ++ tailWord_2695804).sum := by decide
  have hdescent : baseEnd_2695804 < baseStart_2695804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695807 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 6]
def baseStart_2695807 : Nat := 118140960795 + 2695807 * 2 ^ 59
def prefixEnd_2695807 : Nat := 4983230072969 + 3 ^ 40 * 2695807 * 2
def baseEnd_2695807 : Nat := 153804971417248819601635

theorem tailTrace_2695807 : CollatzResearch.WordTrace tailWord_2695807 prefixEnd_2695807 153804971417248819601635 := by
  unfold tailWord_2695807
  simp only [CollatzResearch.WordTrace]
  refine ⟨98324158944559121025821675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65549439296372747350547783 98324158944559121025821675)
  ·
    refine ⟨147486238416838681538732513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98324158944559121025821675 147486238416838681538732513)
    ·
      refine ⟨110614678812629011154049385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147486238416838681538732513 110614678812629011154049385)
      ·
        refine ⟨82961009109471758365537039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110614678812629011154049385 82961009109471758365537039)
        ·
          refine ⟨124441513664207637548305559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82961009109471758365537039 124441513664207637548305559)
          ·
            refine ⟨186662270496311456322458339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124441513664207637548305559 186662270496311456322458339)
            ·
              refine ⟨279993405744467184483687509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186662270496311456322458339 279993405744467184483687509)
              ·
                refine ⟨3281172723567974818168213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 279993405744467184483687509 3281172723567974818168213)
                ·
                  refine ⟨153804971417248819601635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3281172723567974818168213 153804971417248819601635)
                  ·
                    rfl

theorem cell23_2695807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 6].length) (baseStart_2695807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695807 prefixEnd_2695807 := by exact prefixLift 2695807
  have htrace : WordTrace (prefixWord ++ tailWord_2695807) baseStart_2695807 baseEnd_2695807 := by
    simpa [prefixWord, tailWord_2695807, baseEnd_2695807] using wordTrace_append hprefix tailTrace_2695807
  have hstable : (prefixWord ++ tailWord_2695807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695807).length < 2 ^ (prefixWord ++ tailWord_2695807).sum := by decide
  have hdescent : baseEnd_2695807 < baseStart_2695807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695811 : List Nat := [1, 1, 1, 3, 3, 1, 4, 4, 1, 4]
def baseStart_2695811 : Nat := 118140960795 + 2695811 * 2 ^ 59
def prefixEnd_2695811 : Nat := 4983230072969 + 3 ^ 40 * 2695811 * 2
def baseEnd_2695811 : Nat := 461415598892619120254899

theorem tailTrace_2695811 : CollatzResearch.WordTrace tailWord_2695811 prefixEnd_2695811 461415598892619120254899 := by
  unfold tailWord_2695811
  simp only [CollatzResearch.WordTrace]
  refine ⟨98324304836544629708967287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65549536557696419805978191 98324304836544629708967287)
  ·
    refine ⟨147486457254816944563450931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98324304836544629708967287 147486457254816944563450931)
    ·
      refine ⟨221229685882225416845176397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147486457254816944563450931 221229685882225416845176397)
      ·
        refine ⟨82961132205834531316941149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221229685882225416845176397 82961132205834531316941149)
        ·
          refine ⟨31110424577187949243852931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82961132205834531316941149 31110424577187949243852931)
          ·
            refine ⟨46665636865781923865779397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31110424577187949243852931 46665636865781923865779397)
            ·
              refine ⟨8749806912334110724833637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46665636865781923865779397 8749806912334110724833637)
              ·
                refine ⟨1640588796062645760906307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8749806912334110724833637 1640588796062645760906307)
                ·
                  refine ⟨2460883194093968641359461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640588796062645760906307 2460883194093968641359461)
                  ·
                    refine ⟨461415598892619120254899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2460883194093968641359461 461415598892619120254899)
                    ·
                      rfl

theorem cell23_2695811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 1, 4].length) (baseStart_2695811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695811 prefixEnd_2695811 := by exact prefixLift 2695811
  have htrace : WordTrace (prefixWord ++ tailWord_2695811) baseStart_2695811 baseEnd_2695811 := by
    simpa [prefixWord, tailWord_2695811, baseEnd_2695811] using wordTrace_append hprefix tailTrace_2695811
  have hstable : (prefixWord ++ tailWord_2695811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695811).length < 2 ^ (prefixWord ++ tailWord_2695811).sum := by decide
  have hdescent : baseEnd_2695811 < baseStart_2695811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695862 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2695862 : Nat := 118140960795 + 2695862 * 2 ^ 59
def prefixEnd_2695862 : Nat := 4983230072969 + 3 ^ 40 * 2695862 * 2
def baseEnd_2695862 : Nat := 461424328063745553742321

theorem tailTrace_2695862 : CollatzResearch.WordTrace tailWord_2695862 prefixEnd_2695862 461424328063745553742321 := by
  unfold tailWord_2695862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6145385309959991588692115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65550776639573243612715893 6145385309959991588692115)
  ·
    refine ⟨9218077964939987383038173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6145385309959991588692115 9218077964939987383038173)
    ·
      refine ⟨3456779236852495268639315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9218077964939987383038173 3456779236852495268639315)
      ·
        refine ⟨5185168855278742902958973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3456779236852495268639315 5185168855278742902958973)
        ·
          refine ⟨1944438320729528588609615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5185168855278742902958973 1944438320729528588609615)
          ·
            refine ⟨2916657481094292882914423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944438320729528588609615 2916657481094292882914423)
            ·
              refine ⟨4374986221641439324371635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916657481094292882914423 4374986221641439324371635)
              ·
                refine ⟨6562479332462158986557453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374986221641439324371635 6562479332462158986557453)
                ·
                  refine ⟨2460929749673309619959045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6562479332462158986557453 2460929749673309619959045)
                  ·
                    refine ⟨461424328063745553742321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2460929749673309619959045 461424328063745553742321)
                    ·
                      rfl

theorem cell23_2695862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2695862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695862 prefixEnd_2695862 := by exact prefixLift 2695862
  have htrace : WordTrace (prefixWord ++ tailWord_2695862) baseStart_2695862 baseEnd_2695862 := by
    simpa [prefixWord, tailWord_2695862, baseEnd_2695862] using wordTrace_append hprefix tailTrace_2695862
  have hstable : (prefixWord ++ tailWord_2695862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695862).length < 2 ^ (prefixWord ++ tailWord_2695862).sum := by decide
  have hdescent : baseEnd_2695862 < baseStart_2695862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695897 : List Nat := [1, 2, 1, 2, 3, 2, 1, 11]
def baseStart_2695897 : Nat := 118140960795 + 2695897 * 2 ^ 59
def prefixEnd_2695897 : Nat := 4983230072969 + 3 ^ 40 * 2695897 * 2
def baseEnd_2695897 : Nat := 51270035407931260158863

theorem tailTrace_2695897 : CollatzResearch.WordTrace tailWord_2695897 prefixEnd_2695897 51270035407931260158863 := by
  unfold tailWord_2695897
  simp only [CollatzResearch.WordTrace]
  refine ⟨98327441514233066396597945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65551627676155377597731963 98327441514233066396597945)
  ·
    refine ⟨73745581135674799797448459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98327441514233066396597945 73745581135674799797448459)
    ·
      refine ⟨110618371703512199696172689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73745581135674799797448459 110618371703512199696172689)
      ·
        refine ⟨82963778777634149772129517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110618371703512199696172689 82963778777634149772129517)
        ·
          refine ⟨31111417041612806164548569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82963778777634149772129517 31111417041612806164548569)
          ·
            refine ⟨23333562781209604623411427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31111417041612806164548569 23333562781209604623411427)
            ·
              refine ⟨35000344171814406935117141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23333562781209604623411427 35000344171814406935117141)
              ·
                refine ⟨51270035407931260158863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 35000344171814406935117141 51270035407931260158863)
                ·
                  rfl

theorem cell23_2695897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 11].length) (baseStart_2695897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695897 prefixEnd_2695897 := by exact prefixLift 2695897
  have htrace : WordTrace (prefixWord ++ tailWord_2695897) baseStart_2695897 baseEnd_2695897 := by
    simpa [prefixWord, tailWord_2695897, baseEnd_2695897] using wordTrace_append hprefix tailTrace_2695897
  have hstable : (prefixWord ++ tailWord_2695897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695897).length < 2 ^ (prefixWord ++ tailWord_2695897).sum := by decide
  have hdescent : baseEnd_2695897 < baseStart_2695897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695908 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 1, 1, 4]
def baseStart_2695908 : Nat := 118140960795 + 2695908 * 2 ^ 59
def prefixEnd_2695908 : Nat := 4983230072969 + 3 ^ 40 * 2695908 * 2
def baseEnd_2695908 : Nat := 1384296604301343481251751

theorem tailTrace_2695908 : CollatzResearch.WordTrace tailWord_2695908 prefixEnd_2695908 1384296604301343481251751 := by
  unfold tailWord_2695908
  simp only [CollatzResearch.WordTrace]
  refine ⟨49163921358596607637624189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65551895144795476850165585 49163921358596607637624189)
  ·
    refine ⟨18436470509473727864109071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49163921358596607637624189 18436470509473727864109071)
    ·
      refine ⟨27654705764210591796163607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18436470509473727864109071 27654705764210591796163607)
      ·
        refine ⟨41482058646315887694245411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27654705764210591796163607 41482058646315887694245411)
        ·
          refine ⟨62223087969473831541368117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41482058646315887694245411 62223087969473831541368117)
          ·
            refine ⟨5833414497138171707003261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62223087969473831541368117 5833414497138171707003261)
            ·
              refine ⟨2187530436426814390126223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5833414497138171707003261 2187530436426814390126223)
              ·
                refine ⟨3281295654640221585189335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187530436426814390126223 3281295654640221585189335)
                ·
                  refine ⟨4921943481960332377784003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281295654640221585189335 4921943481960332377784003)
                  ·
                    refine ⟨7382915222940498566676005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4921943481960332377784003 7382915222940498566676005)
                    ·
                      refine ⟨1384296604301343481251751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7382915222940498566676005 1384296604301343481251751)
                      ·
                        rfl

theorem cell23_2695908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_2695908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695908 prefixEnd_2695908 := by exact prefixLift 2695908
  have htrace : WordTrace (prefixWord ++ tailWord_2695908) baseStart_2695908 baseEnd_2695908 := by
    simpa [prefixWord, tailWord_2695908, baseEnd_2695908] using wordTrace_append hprefix tailTrace_2695908
  have hstable : (prefixWord ++ tailWord_2695908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695908).length < 2 ^ (prefixWord ++ tailWord_2695908).sum := by decide
  have hdescent : baseEnd_2695908 < baseStart_2695908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695918 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_2695918 : Nat := 118140960795 + 2695918 * 2 ^ 59
def prefixEnd_2695918 : Nat := 4983230072969 + 3 ^ 40 * 2695918 * 2
def baseEnd_2695918 : Nat := 461433913035962814042235

theorem tailTrace_2695918 : CollatzResearch.WordTrace tailWord_2695918 prefixEnd_2695918 461433913035962814042235 := by
  unfold tailWord_2695918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12291025930894623372889051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65552138298104657988741605 12291025930894623372889051)
  ·
    refine ⟨18436538896341935059333577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12291025930894623372889051 18436538896341935059333577)
    ·
      refine ⟨13827404172256451294500183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18436538896341935059333577 13827404172256451294500183)
      ·
        refine ⟨20741106258384676941750275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13827404172256451294500183 20741106258384676941750275)
        ·
          refine ⟨31111659387577015412625413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20741106258384676941750275 31111659387577015412625413)
          ·
            refine ⟨5833436135170690389867265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31111659387577015412625413 5833436135170690389867265)
            ·
              refine ⟨4375077101378017792400449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5833436135170690389867265 4375077101378017792400449)
              ·
                refine ⟨3281307826033513344300337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4375077101378017792400449 3281307826033513344300337)
                ·
                  refine ⟨2460980869525135008225253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3281307826033513344300337 2460980869525135008225253)
                  ·
                    refine ⟨461433913035962814042235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2460980869525135008225253 461433913035962814042235)
                    ·
                      rfl

theorem cell23_2695918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_2695918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695918 prefixEnd_2695918 := by exact prefixLift 2695918
  have htrace : WordTrace (prefixWord ++ tailWord_2695918) baseStart_2695918 baseEnd_2695918 := by
    simpa [prefixWord, tailWord_2695918, baseEnd_2695918] using wordTrace_append hprefix tailTrace_2695918
  have hstable : (prefixWord ++ tailWord_2695918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695918).length < 2 ^ (prefixWord ++ tailWord_2695918).sum := by decide
  have hdescent : baseEnd_2695918 < baseStart_2695918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695938 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_2695938 : Nat := 118140960795 + 2695938 * 2 ^ 59
def prefixEnd_2695938 : Nat := 4983230072969 + 3 ^ 40 * 2695938 * 2
def baseEnd_2695938 : Nat := 1384312008720978363876613

theorem tailTrace_2695938 : CollatzResearch.WordTrace tailWord_2695938 prefixEnd_2695938 1384312008720978363876613 := by
  unfold tailWord_2695938
  simp only [CollatzResearch.WordTrace]
  refine ⟨24582234226771132599710117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65552624604723020265893645 24582234226771132599710117)
  ·
    refine ⟨4609168917519587362445647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24582234226771132599710117 4609168917519587362445647)
    ·
      refine ⟨6913753376279381043668471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4609168917519587362445647 6913753376279381043668471)
      ·
        refine ⟨10370630064419071565502707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6913753376279381043668471 10370630064419071565502707)
        ·
          refine ⟨15555945096628607348254061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10370630064419071565502707 15555945096628607348254061)
          ·
            refine ⟨5833479411235727755595273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15555945096628607348254061 5833479411235727755595273)
            ·
              refine ⟨4375109558426795816696455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5833479411235727755595273 4375109558426795816696455)
              ·
                refine ⟨6562664337640193725044683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375109558426795816696455 6562664337640193725044683)
                ·
                  refine ⟨9843996506460290587567025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6562664337640193725044683 9843996506460290587567025)
                  ·
                    refine ⟨7382997379845217940675269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9843996506460290587567025 7382997379845217940675269)
                    ·
                      refine ⟨1384312008720978363876613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7382997379845217940675269 1384312008720978363876613)
                      ·
                        rfl

theorem cell23_2695938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_2695938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695938 prefixEnd_2695938 := by exact prefixLift 2695938
  have htrace : WordTrace (prefixWord ++ tailWord_2695938) baseStart_2695938 baseEnd_2695938 := by
    simpa [prefixWord, tailWord_2695938, baseEnd_2695938] using wordTrace_append hprefix tailTrace_2695938
  have hstable : (prefixWord ++ tailWord_2695938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695938).length < 2 ^ (prefixWord ++ tailWord_2695938).sum := by decide
  have hdescent : baseEnd_2695938 < baseStart_2695938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695951 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 3, 3, 2]
def baseStart_2695951 : Nat := 118140960795 + 2695951 * 2 ^ 59
def prefixEnd_2695951 : Nat := 4983230072969 + 3 ^ 40 * 2695951 * 2
def baseEnd_2695951 : Nat := 1384318683969486813014053

theorem tailTrace_2695951 : CollatzResearch.WordTrace tailWord_2695951 prefixEnd_2695951 1384318683969486813014053 := by
  unfold tailWord_2695951
  simp only [CollatzResearch.WordTrace]
  refine ⟨98329411056037433619063707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65552940704024955746042471 98329411056037433619063707)
  ·
    refine ⟨147494116584056150428595561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98329411056037433619063707 147494116584056150428595561)
    ·
      refine ⟨110620587438042112821446671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147494116584056150428595561 110620587438042112821446671)
      ·
        refine ⟨165930881157063169232170007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110620587438042112821446671 165930881157063169232170007)
        ·
          refine ⟨248896321735594753848255011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165930881157063169232170007 248896321735594753848255011)
          ·
            refine ⟨373344482603392130772382517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248896321735594753848255011 373344482603392130772382517)
            ·
              refine ⟨35001045244068012259910861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 373344482603392130772382517 35001045244068012259910861)
              ·
                refine ⟨13125391966525504597466573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35001045244068012259910861 13125391966525504597466573)
                ·
                  refine ⟨4922021987447064224049965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13125391966525504597466573 4922021987447064224049965)
                  ·
                    refine ⟨1845758245292649084018737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4922021987447064224049965 1845758245292649084018737)
                    ·
                      refine ⟨1384318683969486813014053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845758245292649084018737 1384318683969486813014053)
                      ·
                        rfl

theorem cell23_2695951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 3, 2].length) (baseStart_2695951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695951 prefixEnd_2695951 := by exact prefixLift 2695951
  have htrace : WordTrace (prefixWord ++ tailWord_2695951) baseStart_2695951 baseEnd_2695951 := by
    simpa [prefixWord, tailWord_2695951, baseEnd_2695951] using wordTrace_append hprefix tailTrace_2695951
  have hstable : (prefixWord ++ tailWord_2695951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695951).length < 2 ^ (prefixWord ++ tailWord_2695951).sum := by decide
  have hdescent : baseEnd_2695951 < baseStart_2695951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2695984 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 3]
def baseStart_2695984 : Nat := 118140960795 + 2695984 * 2 ^ 59
def prefixEnd_2695984 : Nat := 4983230072969 + 3 ^ 40 * 2695984 * 2
def baseEnd_2695984 : Nat := 1384335628831085183901401

theorem tailTrace_2695984 : CollatzResearch.WordTrace tailWord_2695984 prefixEnd_2695984 1384335628831085183901401 := by
  unfold tailWord_2695984
  simp only [CollatzResearch.WordTrace]
  refine ⟨49165307332458940127507503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65553743109945253503343337 49165307332458940127507503)
  ·
    refine ⟨73747960998688410191261255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49165307332458940127507503 73747960998688410191261255)
    ·
      refine ⟨110621941498032615286891883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73747960998688410191261255 110621941498032615286891883)
      ·
        refine ⟨165932912247048922930337825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110621941498032615286891883 165932912247048922930337825)
        ·
          refine ⟨124449684185286692197753369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165932912247048922930337825 124449684185286692197753369)
          ·
            refine ⟨93337263138965019148315027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124449684185286692197753369 93337263138965019148315027)
            ·
              refine ⟨140005894708447528722472541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93337263138965019148315027 140005894708447528722472541)
              ·
                refine ⟨52502210515667823270927203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140005894708447528722472541 52502210515667823270927203)
                ·
                  refine ⟨78753315773501734906390805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52502210515667823270927203 78753315773501734906390805)
                  ·
                    refine ⟨3691561676882893823737069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78753315773501734906390805 3691561676882893823737069)
                    ·
                      refine ⟨1384335628831085183901401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3691561676882893823737069 1384335628831085183901401)
                      ·
                        rfl

theorem cell23_2695984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 3].length) (baseStart_2695984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2695984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2695984 prefixEnd_2695984 := by exact prefixLift 2695984
  have htrace : WordTrace (prefixWord ++ tailWord_2695984) baseStart_2695984 baseEnd_2695984 := by
    simpa [prefixWord, tailWord_2695984, baseEnd_2695984] using wordTrace_append hprefix tailTrace_2695984
  have hstable : (prefixWord ++ tailWord_2695984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2695984).length < 2 ^ (prefixWord ++ tailWord_2695984).sum := by decide
  have hdescent : baseEnd_2695984 < baseStart_2695984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2695984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696138 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_2696138 : Nat := 118140960795 + 2696138 * 2 ^ 59
def prefixEnd_2696138 : Nat := 4983230072969 + 3 ^ 40 * 2696138 * 2
def baseEnd_2696138 : Nat := 1384414704851877581375693

theorem tailTrace_2696138 : CollatzResearch.WordTrace tailWord_2696138 prefixEnd_2696138 1384414704851877581375693 := by
  unfold tailWord_2696138
  simp only [CollatzResearch.WordTrace]
  refine ⟨24584057876589991139030267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65557487670906643037414045 24584057876589991139030267)
  ·
    refine ⟨36876086814884986708545401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24584057876589991139030267 36876086814884986708545401)
    ·
      refine ⟨27657065111163740031409051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36876086814884986708545401 27657065111163740031409051)
      ·
        refine ⟨41485597666745610047113577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27657065111163740031409051 41485597666745610047113577)
        ·
          refine ⟨31114198250059207535335183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41485597666745610047113577 31114198250059207535335183)
          ·
            refine ⟨46671297375088811303002775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31114198250059207535335183 46671297375088811303002775)
            ·
              refine ⟨70006946062633216954504163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46671297375088811303002775 70006946062633216954504163)
              ·
                refine ⟨105010419093949825431756245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70006946062633216954504163 105010419093949825431756245)
                ·
                  refine ⟨2461181697514449033556787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 105010419093949825431756245 2461181697514449033556787)
                  ·
                    refine ⟨3691772546271673550335181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2461181697514449033556787 3691772546271673550335181)
                    ·
                      refine ⟨1384414704851877581375693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3691772546271673550335181 1384414704851877581375693)
                      ·
                        rfl

theorem cell23_2696138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_2696138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696138 prefixEnd_2696138 := by exact prefixLift 2696138
  have htrace : WordTrace (prefixWord ++ tailWord_2696138) baseStart_2696138 baseEnd_2696138 := by
    simpa [prefixWord, tailWord_2696138, baseEnd_2696138] using wordTrace_append hprefix tailTrace_2696138
  have hstable : (prefixWord ++ tailWord_2696138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696138).length < 2 ^ (prefixWord ++ tailWord_2696138).sum := by decide
  have hdescent : baseEnd_2696138 < baseStart_2696138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696162 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 6]
def baseStart_2696162 : Nat := 118140960795 + 2696162 * 2 ^ 59
def prefixEnd_2696162 : Nat := 4983230072969 + 3 ^ 40 * 2696162 * 2
def baseEnd_2696162 : Nat := 153825225376398387497287

theorem tailTrace_2696162 : CollatzResearch.WordTrace tailWord_2696162 prefixEnd_2696162 153825225376398387497287 := by
  unfold tailWord_2696162
  simp only [CollatzResearch.WordTrace]
  refine ⟨24584276714568254163748685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65558071238848677769996493 24584276714568254163748685)
  ·
    refine ⟨9219103767963095311405757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24584276714568254163748685 9219103767963095311405757)
    ·
      refine ⟨3457163912986160741777159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9219103767963095311405757 3457163912986160741777159)
      ·
        refine ⟨5185745869479241112665739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457163912986160741777159 5185745869479241112665739)
        ·
          refine ⟨7778618804218861668998609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5185745869479241112665739 7778618804218861668998609)
          ·
            refine ⟨5833964103164146251748957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7778618804218861668998609 5833964103164146251748957)
            ·
              refine ⟨2187736538686554844405859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5833964103164146251748957 2187736538686554844405859)
              ·
                refine ⟨3281604808029832266608789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187736538686554844405859 3281604808029832266608789)
                ·
                  refine ⟨153825225376398387497287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3281604808029832266608789 153825225376398387497287)
                  ·
                    rfl

theorem cell23_2696162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_2696162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696162 prefixEnd_2696162 := by exact prefixLift 2696162
  have htrace : WordTrace (prefixWord ++ tailWord_2696162) baseStart_2696162 baseEnd_2696162 := by
    simpa [prefixWord, tailWord_2696162, baseEnd_2696162] using wordTrace_append hprefix tailTrace_2696162
  have hstable : (prefixWord ++ tailWord_2696162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696162).length < 2 ^ (prefixWord ++ tailWord_2696162).sum := by decide
  have hdescent : baseEnd_2696162 < baseStart_2696162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696188 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_2696188 : Nat := 118140960795 + 2696188 * 2 ^ 59
def prefixEnd_2696188 : Nat := 4983230072969 + 3 ^ 40 * 2696188 * 2
def baseEnd_2696188 : Nat := 461480126294867461916821

theorem tailTrace_2696188 : CollatzResearch.WordTrace tailWord_2696188 prefixEnd_2696188 461480126294867461916821 := by
  unfold tailWord_2696188
  simp only [CollatzResearch.WordTrace]
  refine ⟨49169027578089411547720609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65558703437452548730294145 49169027578089411547720609)
  ·
    refine ⟨36876770683567058660790457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49169027578089411547720609 36876770683567058660790457)
    ·
      refine ⟨27657578012675293995592843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36876770683567058660790457 27657578012675293995592843)
      ·
        refine ⟨41486367019012940993389265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27657578012675293995592843 41486367019012940993389265)
        ·
          refine ⟨31114775264259705745041949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41486367019012940993389265 31114775264259705745041949)
          ·
            refine ⟨11668040724097389654390731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31114775264259705745041949 11668040724097389654390731)
            ·
              refine ⟨17502061086146084481586097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11668040724097389654390731 17502061086146084481586097)
              ·
                refine ⟨13126545814609563361189573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17502061086146084481586097 13126545814609563361189573)
                ·
                  refine ⟨2461227340239293130223045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13126545814609563361189573 2461227340239293130223045)
                  ·
                    refine ⟨461480126294867461916821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2461227340239293130223045 461480126294867461916821)
                    ·
                      rfl

theorem cell23_2696188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_2696188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696188 prefixEnd_2696188 := by exact prefixLift 2696188
  have htrace : WordTrace (prefixWord ++ tailWord_2696188) baseStart_2696188 baseEnd_2696188 := by
    simpa [prefixWord, tailWord_2696188, baseEnd_2696188] using wordTrace_append hprefix tailTrace_2696188
  have hstable : (prefixWord ++ tailWord_2696188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696188).length < 2 ^ (prefixWord ++ tailWord_2696188).sum := by decide
  have hdescent : baseEnd_2696188 < baseStart_2696188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696251 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 4]
def baseStart_2696251 : Nat := 118140960795 + 2696251 * 2 ^ 59
def prefixEnd_2696251 : Nat := 4983230072969 + 3 ^ 40 * 2696251 * 2
def baseEnd_2696251 : Nat := 1384472728165835639262673

theorem tailTrace_2696251 : CollatzResearch.WordTrace tailWord_2696251 prefixEnd_2696251 1384472728165835639262673 := by
  unfold tailWord_2696251
  simp only [CollatzResearch.WordTrace]
  refine ⟨98340352954950584854984607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65560235303300389903323071 98340352954950584854984607)
  ·
    refine ⟨147510529432425877282476911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98340352954950584854984607 147510529432425877282476911)
    ·
      refine ⟨221265794148638815923715367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147510529432425877282476911 221265794148638815923715367)
      ·
        refine ⟨331898691222958223885573051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221265794148638815923715367 331898691222958223885573051)
        ·
          refine ⟨497848036834437335828359577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331898691222958223885573051 497848036834437335828359577)
          ·
            refine ⟨373386027625828001871269683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497848036834437335828359577 373386027625828001871269683)
            ·
              refine ⟨560079041438742002806904525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373386027625828001871269683 560079041438742002806904525)
              ·
                refine ⟨210029640539528251052589197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 560079041438742002806904525 210029640539528251052589197)
                ·
                  refine ⟨78761115202323094144720949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210029640539528251052589197 78761115202323094144720949)
                  ·
                    refine ⟨7383854550217790076067589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78761115202323094144720949 7383854550217790076067589)
                    ·
                      refine ⟨1384472728165835639262673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7383854550217790076067589 1384472728165835639262673)
                      ·
                        rfl

theorem cell23_2696251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 4].length) (baseStart_2696251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696251 prefixEnd_2696251 := by exact prefixLift 2696251
  have htrace : WordTrace (prefixWord ++ tailWord_2696251) baseStart_2696251 baseEnd_2696251 := by
    simpa [prefixWord, tailWord_2696251, baseEnd_2696251] using wordTrace_append hprefix tailTrace_2696251
  have hstable : (prefixWord ++ tailWord_2696251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696251).length < 2 ^ (prefixWord ++ tailWord_2696251).sum := by decide
  have hdescent : baseEnd_2696251 < baseStart_2696251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696288 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 3]
def baseStart_2696288 : Nat := 118140960795 + 2696288 * 2 ^ 59
def prefixEnd_2696288 : Nat := 4983230072969 + 3 ^ 40 * 2696288 * 2
def baseEnd_2696288 : Nat := 1384491726950051994500003

theorem tailTrace_2696288 : CollatzResearch.WordTrace tailWord_2696288 prefixEnd_2696288 1384491726950051994500003 := by
  unfold tailWord_2696288
  simp only [CollatzResearch.WordTrace]
  refine ⟨49170851227908270087040759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65561134970544360116054345 49170851227908270087040759)
  ·
    refine ⟨73756276841862405130561139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49170851227908270087040759 73756276841862405130561139)
    ·
      refine ⟨110634415262793607695841709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73756276841862405130561139 110634415262793607695841709)
      ·
        refine ⟨41487905723547602885940641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110634415262793607695841709 41487905723547602885940641)
        ·
          refine ⟨31115929292660702164455481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41487905723547602885940641 31115929292660702164455481)
          ·
            refine ⟨23336946969495526623341611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31115929292660702164455481 23336946969495526623341611)
            ·
              refine ⟨35005420454243289935012417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23336946969495526623341611 35005420454243289935012417)
              ·
                refine ⟨26254065340682467451259313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35005420454243289935012417 26254065340682467451259313)
                ·
                  refine ⟨19690549005511850588444485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26254065340682467451259313 19690549005511850588444485)
                  ·
                    refine ⟨3691977938533471985333341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19690549005511850588444485 3691977938533471985333341)
                    ·
                      refine ⟨1384491726950051994500003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3691977938533471985333341 1384491726950051994500003)
                      ·
                        rfl

theorem cell23_2696288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_2696288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696288 prefixEnd_2696288 := by exact prefixLift 2696288
  have htrace : WordTrace (prefixWord ++ tailWord_2696288) baseStart_2696288 baseEnd_2696288 := by
    simpa [prefixWord, tailWord_2696288, baseEnd_2696288] using wordTrace_append hprefix tailTrace_2696288
  have hstable : (prefixWord ++ tailWord_2696288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696288).length < 2 ^ (prefixWord ++ tailWord_2696288).sum := by decide
  have hdescent : baseEnd_2696288 < baseStart_2696288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696302 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_2696302 : Nat := 118140960795 + 2696302 * 2 ^ 59
def prefixEnd_2696302 : Nat := 4983230072969 + 3 ^ 40 * 2696302 * 2
def baseEnd_2696302 : Nat := 1384498915679214939724939

theorem tailTrace_2696302 : CollatzResearch.WordTrace tailWord_2696302 prefixEnd_2696302 1384498915679214939724939 := by
  unfold tailWord_2696302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12292776634720727570636395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65561475385177213710060773 12292776634720727570636395)
  ·
    refine ⟨18439164952081091355954593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12292776634720727570636395 18439164952081091355954593)
    ·
      refine ⟨13829373714060818516965945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18439164952081091355954593 13829373714060818516965945)
      ·
        refine ⟨10372030285545613887724459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13829373714060818516965945 10372030285545613887724459)
        ·
          refine ⟨15558045428318420831586689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10372030285545613887724459 15558045428318420831586689)
          ·
            refine ⟨11668534071238815623690017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15558045428318420831586689 11668534071238815623690017)
            ·
              refine ⟨8751400553429111717767513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11668534071238815623690017 8751400553429111717767513)
              ·
                refine ⟨6563550415071833788325635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8751400553429111717767513 6563550415071833788325635)
                ·
                  refine ⟨9845325622607750682488453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6563550415071833788325635 9845325622607750682488453)
                  ·
                    refine ⟨1845998554238953252966585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9845325622607750682488453 1845998554238953252966585)
                    ·
                      refine ⟨1384498915679214939724939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1845998554238953252966585 1384498915679214939724939)
                      ·
                        rfl

theorem cell23_2696302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_2696302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696302 prefixEnd_2696302 := by exact prefixLift 2696302
  have htrace : WordTrace (prefixWord ++ tailWord_2696302) baseStart_2696302 baseEnd_2696302 := by
    simpa [prefixWord, tailWord_2696302, baseEnd_2696302] using wordTrace_append hprefix tailTrace_2696302
  have hstable : (prefixWord ++ tailWord_2696302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696302).length < 2 ^ (prefixWord ++ tailWord_2696302).sum := by decide
  have hdescent : baseEnd_2696302 < baseStart_2696302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696325 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 7]
def baseStart_2696325 : Nat := 118140960795 + 2696325 * 2 ^ 59
def prefixEnd_2696325 : Nat := 4983230072969 + 3 ^ 40 * 2696325 * 2
def baseEnd_2696325 : Nat := 153834525081585372193037

theorem tailTrace_2696325 : CollatzResearch.WordTrace tailWord_2696325 prefixEnd_2696325 153834525081585372193037 := by
  unfold tailWord_2696325
  simp only [CollatzResearch.WordTrace]
  refine ⟨98343051956682495493178429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65562034637788330328785619 98343051956682495493178429)
  ·
    refine ⟨36878644483755935809941911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98343051956682495493178429 36878644483755935809941911)
    ·
      refine ⟨55317966725633903714912867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36878644483755935809941911 55317966725633903714912867)
      ·
        refine ⟨82976950088450855572369301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55317966725633903714912867 82976950088450855572369301)
        ·
          refine ⟨3889544535396133854954811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82976950088450855572369301 3889544535396133854954811)
          ·
            refine ⟨5834316803094200782432217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3889544535396133854954811 5834316803094200782432217)
            ·
              refine ⟨4375737602320650586824163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834316803094200782432217 4375737602320650586824163)
              ·
                refine ⟨6563606403480975880236245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375737602320650586824163 6563606403480975880236245)
                ·
                  refine ⟨153834525081585372193037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6563606403480975880236245 153834525081585372193037)
                  ·
                    rfl

theorem cell23_2696325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_2696325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696325 prefixEnd_2696325 := by exact prefixLift 2696325
  have htrace : WordTrace (prefixWord ++ tailWord_2696325) baseStart_2696325 baseEnd_2696325 := by
    simpa [prefixWord, tailWord_2696325, baseEnd_2696325] using wordTrace_append hprefix tailTrace_2696325
  have hstable : (prefixWord ++ tailWord_2696325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696325).length < 2 ^ (prefixWord ++ tailWord_2696325).sum := by decide
  have hdescent : baseEnd_2696325 < baseStart_2696325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696359 : List Nat := [1, 1, 6, 2, 1, 3, 1, 3, 5]
def baseStart_2696359 : Nat := 118140960795 + 2696359 * 2 ^ 59
def prefixEnd_2696359 : Nat := 4983230072969 + 3 ^ 40 * 2696359 * 2
def baseEnd_2696359 : Nat := 153836464897391246301353

theorem tailTrace_2696359 : CollatzResearch.WordTrace tailWord_2696359 prefixEnd_2696359 153836464897391246301353 := by
  unfold tailWord_2696359
  simp only [CollatzResearch.WordTrace]
  refine ⟨98344292038559319299916131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65562861359039546199944087 98344292038559319299916131)
  ·
    refine ⟨147516438057838978949874197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98344292038559319299916131 147516438057838978949874197)
    ·
      refine ⟨6914833033961202138275353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147516438057838978949874197 6914833033961202138275353)
      ·
        refine ⟨5186124775470901603706515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6914833033961202138275353 5186124775470901603706515)
        ·
          refine ⟨7779187163206352405559773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186124775470901603706515 7779187163206352405559773)
          ·
            refine ⟨2917195186202382152084915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7779187163206352405559773 2917195186202382152084915)
            ·
              refine ⟨4375792779303573228127373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2917195186202382152084915 4375792779303573228127373)
              ·
                refine ⟨1640922292238839960547765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4375792779303573228127373 1640922292238839960547765)
                ·
                  refine ⟨153836464897391246301353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1640922292238839960547765 153836464897391246301353)
                  ·
                    rfl

theorem cell23_2696359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 5].length) (baseStart_2696359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696359 prefixEnd_2696359 := by exact prefixLift 2696359
  have htrace : WordTrace (prefixWord ++ tailWord_2696359) baseStart_2696359 baseEnd_2696359 := by
    simpa [prefixWord, tailWord_2696359, baseEnd_2696359] using wordTrace_append hprefix tailTrace_2696359
  have hstable : (prefixWord ++ tailWord_2696359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696359).length < 2 ^ (prefixWord ++ tailWord_2696359).sum := by decide
  have hdescent : baseEnd_2696359 < baseStart_2696359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696375 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_2696375 : Nat := 118140960795 + 2696375 * 2 ^ 59
def prefixEnd_2696375 : Nat := 4983230072969 + 3 ^ 40 * 2696375 * 2
def baseEnd_2696375 : Nat := 1384536399766993154112103

theorem tailTrace_2696375 : CollatzResearch.WordTrace tailWord_2696375 prefixEnd_2696375 1384536399766993154112103 := by
  unfold tailWord_2696375
  simp only [CollatzResearch.WordTrace]
  refine ⟨98344875606501354032498579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65563250404334236021665719 98344875606501354032498579)
  ·
    refine ⟨147517313409752031048747869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98344875606501354032498579 147517313409752031048747869)
    ·
      refine ⟨55318992528657011643280451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147517313409752031048747869 55318992528657011643280451)
      ·
        refine ⟨82978488792985517464920677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55318992528657011643280451 82978488792985517464920677)
        ·
          refine ⟨15558466648684784524672627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82978488792985517464920677 15558466648684784524672627)
          ·
            refine ⟨23337699973027176787008941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15558466648684784524672627 23337699973027176787008941)
            ·
              refine ⟨8751637489885191295128353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23337699973027176787008941 8751637489885191295128353)
              ·
                refine ⟨6563728117413893471346265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8751637489885191295128353 6563728117413893471346265)
                ·
                  refine ⟨4922796088060420103509699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6563728117413893471346265 4922796088060420103509699)
                  ·
                    refine ⟨7384194132090630155264549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4922796088060420103509699 7384194132090630155264549)
                    ·
                      refine ⟨1384536399766993154112103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7384194132090630155264549 1384536399766993154112103)
                      ·
                        rfl

theorem cell23_2696375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_2696375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696375 prefixEnd_2696375 := by exact prefixLift 2696375
  have htrace : WordTrace (prefixWord ++ tailWord_2696375) baseStart_2696375 baseEnd_2696375 := by
    simpa [prefixWord, tailWord_2696375, baseEnd_2696375] using wordTrace_append hprefix tailTrace_2696375
  have hstable : (prefixWord ++ tailWord_2696375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696375).length < 2 ^ (prefixWord ++ tailWord_2696375).sum := by decide
  have hdescent : baseEnd_2696375 < baseStart_2696375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696442 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3]
def baseStart_2696442 : Nat := 118140960795 + 2696442 * 2 ^ 59
def prefixEnd_2696442 : Nat := 4983230072969 + 3 ^ 40 * 2696442 * 2
def baseEnd_2696442 : Nat := 1384570802970844391974295

theorem tailTrace_2696442 : CollatzResearch.WordTrace tailWord_2696442 prefixEnd_2696442 1384570802970844391974295 := by
  unfold tailWord_2696442
  simp only [CollatzResearch.WordTrace]
  refine ⟨24586829824314656118796895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65564879531505749650125053 24586829824314656118796895)
  ·
    refine ⟨36880244736471984178195343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24586829824314656118796895 36880244736471984178195343)
    ·
      refine ⟨55320367104707976267293015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36880244736471984178195343 55320367104707976267293015)
      ·
        refine ⟨82980550657061964400939523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55320367104707976267293015 82980550657061964400939523)
        ·
          refine ⟨124470825985592946601409285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82980550657061964400939523 124470825985592946601409285)
          ·
            refine ⟨23338279872298677487764241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124470825985592946601409285 23338279872298677487764241)
            ·
              refine ⟨17503709904224008115823181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23338279872298677487764241 17503709904224008115823181)
              ·
                refine ⟨6563891214084003043433693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17503709904224008115823181 6563891214084003043433693)
                ·
                  refine ⟨2461459205281501141287635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6563891214084003043433693 2461459205281501141287635)
                  ·
                    refine ⟨3692188807922251711931453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2461459205281501141287635 3692188807922251711931453)
                    ·
                      refine ⟨1384570802970844391974295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3692188807922251711931453 1384570802970844391974295)
                      ·
                        rfl

theorem cell23_2696442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_2696442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696442 prefixEnd_2696442 := by exact prefixLift 2696442
  have htrace : WordTrace (prefixWord ++ tailWord_2696442) baseStart_2696442 baseEnd_2696442 := by
    simpa [prefixWord, tailWord_2696442, baseEnd_2696442] using wordTrace_append hprefix tailTrace_2696442
  have hstable : (prefixWord ++ tailWord_2696442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696442).length < 2 ^ (prefixWord ++ tailWord_2696442).sum := by decide
  have hdescent : baseEnd_2696442 < baseStart_2696442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696465 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_2696465 : Nat := 118140960795 + 2696465 * 2 ^ 59
def prefixEnd_2696465 : Nat := 4983230072969 + 3 ^ 40 * 2696465 * 2
def baseEnd_2696465 : Nat := 1384582613025897801986689

theorem tailTrace_2696465 : CollatzResearch.WordTrace tailWord_2696465 prefixEnd_2696465 1384582613025897801986689 := by
  unfold tailWord_2696465
  simp only [CollatzResearch.WordTrace]
  refine ⟨98348158176175299403274849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65565438784116866268849899 98348158176175299403274849)
  ·
    refine ⟨73761118632131474552456137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98348158176175299403274849 73761118632131474552456137)
    ·
      refine ⟨55320838974098605914342103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73761118632131474552456137 55320838974098605914342103)
      ·
        refine ⟨82981258461147908871513155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55320838974098605914342103 82981258461147908871513155)
        ·
          refine ⟨124471887691721863307269733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82981258461147908871513155 124471887691721863307269733)
          ·
            refine ⟨23338478942197849370113075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124471887691721863307269733 23338478942197849370113075)
            ·
              refine ⟨35007718413296774055169613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23338478942197849370113075 35007718413296774055169613)
              ·
                refine ⟨13127894404986290270688605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35007718413296774055169613 13127894404986290270688605)
                ·
                  refine ⟨4922960401869858851508227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13127894404986290270688605 4922960401869858851508227)
                  ·
                    refine ⟨7384440602804788277262341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4922960401869858851508227 7384440602804788277262341)
                    ·
                      refine ⟨1384582613025897801986689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7384440602804788277262341 1384582613025897801986689)
                      ·
                        rfl

theorem cell23_2696465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_2696465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696465 prefixEnd_2696465 := by exact prefixLift 2696465
  have htrace : WordTrace (prefixWord ++ tailWord_2696465) baseStart_2696465 baseEnd_2696465 := by
    simpa [prefixWord, tailWord_2696465, baseEnd_2696465] using wordTrace_append hprefix tailTrace_2696465
  have hstable : (prefixWord ++ tailWord_2696465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696465).length < 2 ^ (prefixWord ++ tailWord_2696465).sum := by decide
  have hdescent : baseEnd_2696465 < baseStart_2696465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696475 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 4, 4]
def baseStart_2696475 : Nat := 118140960795 + 2696475 * 2 ^ 59
def prefixEnd_2696475 : Nat := 4983230072969 + 3 ^ 40 * 2696475 * 2
def baseEnd_2696475 : Nat := 461529249277480920953881

theorem tailTrace_2696475 : CollatzResearch.WordTrace tailWord_2696475 prefixEnd_2696475 461529249277480920953881 := by
  unfold tailWord_2696475
  simp only [CollatzResearch.WordTrace]
  refine ⟨98348522906139071111138879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65565681937426047407425919 98348522906139071111138879)
  ·
    refine ⟨147522784359208606666708319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98348522906139071111138879 147522784359208606666708319)
    ·
      refine ⟨221284176538812910000062479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147522784359208606666708319 221284176538812910000062479)
      ·
        refine ⟨331926264808219365000093719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221284176538812910000062479 331926264808219365000093719)
        ·
          refine ⟨497889397212329047500140579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331926264808219365000093719 497889397212329047500140579)
          ·
            refine ⟨746834095818493571250210869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497889397212329047500140579 746834095818493571250210869)
            ·
              refine ⟨70015696482983772304707269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 746834095818493571250210869 70015696482983772304707269)
              ·
                refine ⟨13127943090559457307132613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70015696482983772304707269 13127943090559457307132613)
                ·
                  refine ⟨2461489329479898245087365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13127943090559457307132613 2461489329479898245087365)
                  ·
                    refine ⟨461529249277480920953881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2461489329479898245087365 461529249277480920953881)
                    ·
                      rfl

theorem cell23_2696475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 4].length) (baseStart_2696475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696475 prefixEnd_2696475 := by exact prefixLift 2696475
  have htrace : WordTrace (prefixWord ++ tailWord_2696475) baseStart_2696475 baseEnd_2696475 := by
    simpa [prefixWord, tailWord_2696475, baseEnd_2696475] using wordTrace_append hprefix tailTrace_2696475
  have hstable : (prefixWord ++ tailWord_2696475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696475).length < 2 ^ (prefixWord ++ tailWord_2696475).sum := by decide
  have hdescent : baseEnd_2696475 < baseStart_2696475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696493 : List Nat := [1, 5, 3, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_2696493 : Nat := 118140960795 + 2696493 * 2 ^ 59
def prefixEnd_2696493 : Nat := 4983230072969 + 3 ^ 40 * 2696493 * 2
def baseEnd_2696493 : Nat := 1384596990484223692436561

theorem tailTrace_2696493 : CollatzResearch.WordTrace tailWord_2696493 prefixEnd_2696493 1384596990484223692436561 := by
  unfold tailWord_2696493
  simp only [CollatzResearch.WordTrace]
  refine ⟨98349179420073860185294133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65566119613382573456862755 98349179420073860185294133)
  ·
    refine ⟨9220235570631924392371325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98349179420073860185294133 9220235570631924392371325)
    ·
      refine ⟨3457588338986971647139247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9220235570631924392371325 3457588338986971647139247)
      ·
        refine ⟨5186382508480457470708871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457588338986971647139247 5186382508480457470708871)
        ·
          refine ⟨7779573762720686206063307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186382508480457470708871 7779573762720686206063307)
          ·
            refine ⟨11669360644081029309094961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7779573762720686206063307 11669360644081029309094961)
            ·
              refine ⟨8752020483060771981821221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11669360644081029309094961 8752020483060771981821221)
              ·
                refine ⟨1641003840573894746591479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8752020483060771981821221 1641003840573894746591479)
                ·
                  refine ⟨2461505760860842119887219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641003840573894746591479 2461505760860842119887219)
                  ·
                    refine ⟨3692258641291263179830829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2461505760860842119887219 3692258641291263179830829)
                    ·
                      refine ⟨1384596990484223692436561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3692258641291263179830829 1384596990484223692436561)
                      ·
                        rfl

theorem cell23_2696493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_2696493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696493 prefixEnd_2696493 := by exact prefixLift 2696493
  have htrace : WordTrace (prefixWord ++ tailWord_2696493) baseStart_2696493 baseEnd_2696493 := by
    simpa [prefixWord, tailWord_2696493, baseEnd_2696493] using wordTrace_append hprefix tailTrace_2696493
  have hstable : (prefixWord ++ tailWord_2696493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696493).length < 2 ^ (prefixWord ++ tailWord_2696493).sum := by decide
  have hdescent : baseEnd_2696493 < baseStart_2696493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696499 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 3, 2, 2]
def baseStart_2696499 : Nat := 118140960795 + 2696499 * 2 ^ 59
def prefixEnd_2696499 : Nat := 4983230072969 + 3 ^ 40 * 2696499 * 2
def baseEnd_2696499 : Nat := 1384600071368150668961533

theorem tailTrace_2696499 : CollatzResearch.WordTrace tailWord_2696499 prefixEnd_2696499 1384600071368150668961533 := by
  unfold tailWord_2696499
  simp only [CollatzResearch.WordTrace]
  refine ⟨98349398258052123210012551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65566265505368082140008367 98349398258052123210012551)
  ·
    refine ⟨147524097387078184815018827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98349398258052123210012551 147524097387078184815018827)
    ·
      refine ⟨221286146080617277222528241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147524097387078184815018827 221286146080617277222528241)
      ·
        refine ⟨165964609560462957916896181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221286146080617277222528241 165964609560462957916896181)
        ·
          refine ⟨15559182146293402304709017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165964609560462957916896181 15559182146293402304709017)
          ·
            refine ⟨11669386609720051728531763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15559182146293402304709017 11669386609720051728531763)
            ·
              refine ⟨17504079914580077592797645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11669386609720051728531763 17504079914580077592797645)
              ·
                refine ⟨6564029967967529097299117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17504079914580077592797645 6564029967967529097299117)
                ·
                  refine ⟨2461511237987823411487169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6564029967967529097299117 2461511237987823411487169)
                  ·
                    refine ⟨1846133428490867558615377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2461511237987823411487169 1846133428490867558615377)
                    ·
                      refine ⟨1384600071368150668961533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846133428490867558615377 1384600071368150668961533)
                      ·
                        rfl

theorem cell23_2696499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 2, 2].length) (baseStart_2696499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696499 prefixEnd_2696499 := by exact prefixLift 2696499
  have htrace : WordTrace (prefixWord ++ tailWord_2696499) baseStart_2696499 baseEnd_2696499 := by
    simpa [prefixWord, tailWord_2696499, baseEnd_2696499] using wordTrace_append hprefix tailTrace_2696499
  have hstable : (prefixWord ++ tailWord_2696499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696499).length < 2 ^ (prefixWord ++ tailWord_2696499).sum := by decide
  have hdescent : baseEnd_2696499 < baseStart_2696499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696516 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2696516 : Nat := 118140960795 + 2696516 * 2 ^ 59
def prefixEnd_2696516 : Nat := 4983230072969 + 3 ^ 40 * 2696516 * 2
def baseEnd_2696516 : Nat := 1384608800539277102448955

theorem tailTrace_2696516 : CollatzResearch.WordTrace tailWord_2696516 prefixEnd_2696516 1384608800539277102448955 := by
  unfold tailWord_2696516
  simp only [CollatzResearch.WordTrace]
  refine ⟨49175009149495267556690701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65566678865993690075587601 49175009149495267556690701)
  ·
    refine ⟨18440628431060725333759013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49175009149495267556690701 18440628431060725333759013)
    ·
      refine ⟨3457617830823886000079815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18440628431060725333759013 3457617830823886000079815)
      ·
        refine ⟨5186426746235829000119723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457617830823886000079815 5186426746235829000119723)
        ·
          refine ⟨7779640119353743500179585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186426746235829000119723 7779640119353743500179585)
          ·
            refine ⟨5834730089515307625134689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7779640119353743500179585 5834730089515307625134689)
            ·
              refine ⟨4376047567136480718851017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834730089515307625134689 4376047567136480718851017)
              ·
                refine ⟨3282035675352360539138263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4376047567136480718851017 3282035675352360539138263)
                ·
                  refine ⟨4923053513028540808707395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282035675352360539138263 4923053513028540808707395)
                  ·
                    refine ⟨7384580269542811213061093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4923053513028540808707395 7384580269542811213061093)
                    ·
                      refine ⟨1384608800539277102448955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7384580269542811213061093 1384608800539277102448955)
                      ·
                        rfl

theorem cell23_2696516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2696516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696516 prefixEnd_2696516 := by exact prefixLift 2696516
  have htrace : WordTrace (prefixWord ++ tailWord_2696516) baseStart_2696516 baseEnd_2696516 := by
    simpa [prefixWord, tailWord_2696516, baseEnd_2696516] using wordTrace_append hprefix tailTrace_2696516
  have hstable : (prefixWord ++ tailWord_2696516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696516).length < 2 ^ (prefixWord ++ tailWord_2696516).sum := by decide
  have hdescent : baseEnd_2696516 < baseStart_2696516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696519 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_2696519 : Nat := 118140960795 + 2696519 * 2 ^ 59
def prefixEnd_2696519 : Nat := 4983230072969 + 3 ^ 40 * 2696519 * 2
def baseEnd_2696519 : Nat := 1384610340981240590711441

theorem tailTrace_2696519 : CollatzResearch.WordTrace tailWord_2696519 prefixEnd_2696519 1384610340981240590711441 := by
  unfold tailWord_2696519
  simp only [CollatzResearch.WordTrace]
  refine ⟨98350127717979666625740611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65566751811986444417160407 98350127717979666625740611)
  ·
    refine ⟨147525191576969499938610917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98350127717979666625740611 147525191576969499938610917)
    ·
      refine ⟨27660973420681781238489547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147525191576969499938610917 27660973420681781238489547)
      ·
        refine ⟨41491460131022671857734321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27660973420681781238489547 41491460131022671857734321)
        ·
          refine ⟨31118595098267003893300741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41491460131022671857734321 31118595098267003893300741)
          ·
            refine ⟨5834736580925063229993889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31118595098267003893300741 5834736580925063229993889)
            ·
              refine ⟨4376052435693797422495417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834736580925063229993889 4376052435693797422495417)
              ·
                refine ⟨3282039326770348066871563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4376052435693797422495417 3282039326770348066871563)
                ·
                  refine ⟨4923058990155522100307345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282039326770348066871563 4923058990155522100307345)
                  ·
                    refine ⟨3692294242616641575230509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4923058990155522100307345 3692294242616641575230509)
                    ·
                      refine ⟨1384610340981240590711441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3692294242616641575230509 1384610340981240590711441)
                      ·
                        rfl

theorem cell23_2696519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_2696519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696519 prefixEnd_2696519 := by exact prefixLift 2696519
  have htrace : WordTrace (prefixWord ++ tailWord_2696519) baseStart_2696519 baseEnd_2696519 := by
    simpa [prefixWord, tailWord_2696519, baseEnd_2696519] using wordTrace_append hprefix tailTrace_2696519
  have hstable : (prefixWord ++ tailWord_2696519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696519).length < 2 ^ (prefixWord ++ tailWord_2696519).sum := by decide
  have hdescent : baseEnd_2696519 < baseStart_2696519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696532 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_2696532 : Nat := 118140960795 + 2696532 * 2 ^ 59
def prefixEnd_2696532 : Nat := 4983230072969 + 3 ^ 40 * 2696532 * 2
def baseEnd_2696532 : Nat := 1384617016229749039848881

theorem tailTrace_2696532 : CollatzResearch.WordTrace tailWord_2696532 prefixEnd_2696532 1384617016229749039848881 := by
  unfold tailWord_2696532
  simp only [CollatzResearch.WordTrace]
  refine ⟨49175300933466284922981925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65567067911288379897309233 49175300933466284922981925)
  ·
    refine ⟨9220368925024928423059111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49175300933466284922981925 9220368925024928423059111)
    ·
      refine ⟨13830553387537392634588667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9220368925024928423059111 13830553387537392634588667)
      ·
        refine ⟨20745830081306088951883001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13830553387537392634588667 20745830081306088951883001)
        ·
          refine ⟨15559372560979566713912251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20745830081306088951883001 15559372560979566713912251)
          ·
            refine ⟨23339058841469350070868377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15559372560979566713912251 23339058841469350070868377)
            ·
              refine ⟨17504294131102012553151283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23339058841469350070868377 17504294131102012553151283)
              ·
                refine ⟨26256441196653018829726925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17504294131102012553151283 26256441196653018829726925)
                ·
                  refine ⟨9846165448744882061147597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26256441196653018829726925 9846165448744882061147597)
                  ·
                    refine ⟨3692312043279330772930349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9846165448744882061147597 3692312043279330772930349)
                    ·
                      refine ⟨1384617016229749039848881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3692312043279330772930349 1384617016229749039848881)
                      ·
                        rfl

theorem cell23_2696532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_2696532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696532 prefixEnd_2696532 := by exact prefixLift 2696532
  have htrace : WordTrace (prefixWord ++ tailWord_2696532) baseStart_2696532 baseEnd_2696532 := by
    simpa [prefixWord, tailWord_2696532, baseEnd_2696532] using wordTrace_append hprefix tailTrace_2696532
  have hstable : (prefixWord ++ tailWord_2696532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696532).length < 2 ^ (prefixWord ++ tailWord_2696532).sum := by decide
  have hdescent : baseEnd_2696532 < baseStart_2696532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696533 : List Nat := [1, 3, 2, 2, 3, 1, 3, 3, 1, 2, 2]
def baseStart_2696533 : Nat := 118140960795 + 2696533 * 2 ^ 59
def prefixEnd_2696533 : Nat := 4983230072969 + 3 ^ 40 * 2696533 * 2
def baseEnd_2696533 : Nat := 1384617529710403535936377

theorem tailTrace_2696533 : CollatzResearch.WordTrace tailWord_2696533 prefixEnd_2696533 1384617529710403535936377 := by
  unfold tailWord_2696533
  simp only [CollatzResearch.WordTrace]
  refine ⟨98350638339928947016750253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65567092226619298011166835 98350638339928947016750253)
  ·
    refine ⟨36881489377473355131281345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98350638339928947016750253 36881489377473355131281345)
    ·
      refine ⟨27661117033105016348461009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36881489377473355131281345 27661117033105016348461009)
      ·
        refine ⟨20745837774828762261345757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27661117033105016348461009 20745837774828762261345757)
        ·
          refine ⟨7779689165560785848004659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20745837774828762261345757 7779689165560785848004659)
          ·
            refine ⟨11669533748341178772006989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7779689165560785848004659 11669533748341178772006989)
            ·
              refine ⟨4376075155627942039502621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11669533748341178772006989 4376075155627942039502621)
              ·
                refine ⟨1641028183360478264813483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4376075155627942039502621 1641028183360478264813483)
                ·
                  refine ⟨2461542275040717397220225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641028183360478264813483 2461542275040717397220225)
                  ·
                    refine ⟨1846156706280538047915169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2461542275040717397220225 1846156706280538047915169)
                    ·
                      refine ⟨1384617529710403535936377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846156706280538047915169 1384617529710403535936377)
                      ·
                        rfl

theorem cell23_2696533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_2696533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696533 prefixEnd_2696533 := by exact prefixLift 2696533
  have htrace : WordTrace (prefixWord ++ tailWord_2696533) baseStart_2696533 baseEnd_2696533 := by
    simpa [prefixWord, tailWord_2696533, baseEnd_2696533] using wordTrace_append hprefix tailTrace_2696533
  have hstable : (prefixWord ++ tailWord_2696533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696533).length < 2 ^ (prefixWord ++ tailWord_2696533).sum := by decide
  have hdescent : baseEnd_2696533 < baseStart_2696533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696549 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 2, 1, 3]
def baseStart_2696549 : Nat := 118140960795 + 2696549 * 2 ^ 59
def prefixEnd_2696549 : Nat := 4983230072969 + 3 ^ 40 * 2696549 * 2
def baseEnd_2696549 : Nat := 1384625745400875473336303

theorem tailTrace_2696549 : CollatzResearch.WordTrace tailWord_2696549 prefixEnd_2696549 1384625745400875473336303 := by
  unfold tailWord_2696549
  simp only [CollatzResearch.WordTrace]
  refine ⟨98351221907870981749332701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65567481271913987832888467 98351221907870981749332701)
  ·
    refine ⟨36881708215451618155999763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98351221907870981749332701 36881708215451618155999763)
    ·
      refine ⟨55322562323177427233999645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36881708215451618155999763 55322562323177427233999645)
      ·
        refine ⟨20745960871191535212749867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55322562323177427233999645 20745960871191535212749867)
        ·
          refine ⟨31118941306787302819124801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20745960871191535212749867 31118941306787302819124801)
          ·
            refine ⟨23339205980090477114343601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31118941306787302819124801 23339205980090477114343601)
            ·
              refine ⟨17504404485067857835757701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23339205980090477114343601 17504404485067857835757701)
              ·
                refine ⟨3282075840950223344204569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17504404485067857835757701 3282075840950223344204569)
                ·
                  refine ⟨2461556880712667508153427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3282075840950223344204569 2461556880712667508153427)
                  ·
                    refine ⟨3692335321069001262230141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2461556880712667508153427 3692335321069001262230141)
                    ·
                      refine ⟨1384625745400875473336303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3692335321069001262230141 1384625745400875473336303)
                      ·
                        rfl

theorem cell23_2696549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_2696549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696549 prefixEnd_2696549 := by exact prefixLift 2696549
  have htrace : WordTrace (prefixWord ++ tailWord_2696549) baseStart_2696549 baseEnd_2696549 := by
    simpa [prefixWord, tailWord_2696549, baseEnd_2696549] using wordTrace_append hprefix tailTrace_2696549
  have hstable : (prefixWord ++ tailWord_2696549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696549).length < 2 ^ (prefixWord ++ tailWord_2696549).sum := by decide
  have hdescent : baseEnd_2696549 < baseStart_2696549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696602 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2696602 : Nat := 118140960795 + 2696602 * 2 ^ 59
def prefixEnd_2696602 : Nat := 4983230072969 + 3 ^ 40 * 2696602 * 2
def baseEnd_2696602 : Nat := 1384652959875563765973559

theorem tailTrace_2696602 : CollatzResearch.WordTrace tailWord_2696602 prefixEnd_2696602 1384652959875563765973559 := by
  unfold tailWord_2696602
  simp only [CollatzResearch.WordTrace]
  refine ⟨24588288744169742950253015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65568769984452647867341373 24588288744169742950253015)
  ·
    refine ⟨36882433116254614425379523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24588288744169742950253015 36882433116254614425379523)
    ·
      refine ⟨55323649674381921638069285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36882433116254614425379523 55323649674381921638069285)
      ·
        refine ⟨10373184313946610307137991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55323649674381921638069285 10373184313946610307137991)
        ·
          refine ⟨15559776470919915460706987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10373184313946610307137991 15559776470919915460706987)
          ·
            refine ⟨23339664706379873191060481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15559776470919915460706987 23339664706379873191060481)
            ·
              refine ⟨17504748529784904893295361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23339664706379873191060481 17504748529784904893295361)
              ·
                refine ⟨13128561397338678669971521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17504748529784904893295361 13128561397338678669971521)
                ·
                  refine ⟨9846421048004009002478641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13128561397338678669971521 9846421048004009002478641)
                  ·
                    refine ⟨7384815786003006751858981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9846421048004009002478641 7384815786003006751858981)
                    ·
                      refine ⟨1384652959875563765973559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7384815786003006751858981 1384652959875563765973559)
                      ·
                        rfl

theorem cell23_2696602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2696602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696602 prefixEnd_2696602 := by exact prefixLift 2696602
  have htrace : WordTrace (prefixWord ++ tailWord_2696602) baseStart_2696602 baseEnd_2696602 := by
    simpa [prefixWord, tailWord_2696602, baseEnd_2696602] using wordTrace_append hprefix tailTrace_2696602
  have hstable : (prefixWord ++ tailWord_2696602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696602).length < 2 ^ (prefixWord ++ tailWord_2696602).sum := by decide
  have hdescent : baseEnd_2696602 < baseStart_2696602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696689 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 3, 4]
def baseStart_2696689 : Nat := 118140960795 + 2696689 * 2 ^ 59
def prefixEnd_2696689 : Nat := 4983230072969 + 3 ^ 40 * 2696689 * 2
def baseEnd_2696689 : Nat := 461565877564168308528553

theorem tailTrace_2696689 : CollatzResearch.WordTrace tailWord_2696689 prefixEnd_2696689 461565877564168308528553 := by
  unfold tailWord_2696689
  simp only [CollatzResearch.WordTrace]
  refine ⟨98356328127363785659429121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65570885418242523772952747 98356328127363785659429121)
  ·
    refine ⟨73767246095522839244571841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98356328127363785659429121 73767246095522839244571841)
    ·
      refine ⟨55325434571642129433428881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73767246095522839244571841 55325434571642129433428881)
      ·
        refine ⟨41494075928731597075071661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55325434571642129433428881 41494075928731597075071661)
        ·
          refine ⟨15560278473274348903151873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41494075928731597075071661 15560278473274348903151873)
          ·
            refine ⟨11670208854955761677363905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15560278473274348903151873 11670208854955761677363905)
            ·
              refine ⟨8752656641216821258022929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11670208854955761677363905 8752656641216821258022929)
              ·
                refine ⟨6564492480912615943517197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8752656641216821258022929 6564492480912615943517197)
                ·
                  refine ⟨2461684680342230978818949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6564492480912615943517197 2461684680342230978818949)
                  ·
                    refine ⟨461565877564168308528553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2461684680342230978818949 461565877564168308528553)
                    ·
                      rfl

theorem cell23_2696689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_2696689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696689 prefixEnd_2696689 := by exact prefixLift 2696689
  have htrace : WordTrace (prefixWord ++ tailWord_2696689) baseStart_2696689 baseEnd_2696689 := by
    simpa [prefixWord, tailWord_2696689, baseEnd_2696689] using wordTrace_append hprefix tailTrace_2696689
  have hstable : (prefixWord ++ tailWord_2696689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696689).length < 2 ^ (prefixWord ++ tailWord_2696689).sum := by decide
  have hdescent : baseEnd_2696689 < baseStart_2696689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696710 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2696710 : Nat := 118140960795 + 2696710 * 2 ^ 59
def prefixEnd_2696710 : Nat := 4983230072969 + 3 ^ 40 * 2696710 * 2
def baseEnd_2696710 : Nat := 461569471928749781141021

theorem tailTrace_2696710 : CollatzResearch.WordTrace tailWord_2696710 prefixEnd_2696710 461569471928749781141021 := by
  unfold tailWord_2696710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073659189383990820185737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65571396040191804163962389 3073659189383990820185737)
  ·
    refine ⟨2305244392037993115139303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3073659189383990820185737 2305244392037993115139303)
    ·
      refine ⟨3457866588056989672708955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2305244392037993115139303 3457866588056989672708955)
      ·
        refine ⟨5186799882085484509063433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457866588056989672708955 5186799882085484509063433)
        ·
          refine ⟨3890099911564113381797575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5186799882085484509063433 3890099911564113381797575)
          ·
            refine ⟨5835149867346170072696363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890099911564113381797575 5835149867346170072696363)
            ·
              refine ⟨8752724801019255109044545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835149867346170072696363 8752724801019255109044545)
              ·
                refine ⟨6564543600764441331783409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8752724801019255109044545 6564543600764441331783409)
                ·
                  refine ⟨4923407700573330998837557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6564543600764441331783409 4923407700573330998837557)
                  ·
                    refine ⟨461569471928749781141021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4923407700573330998837557 461569471928749781141021)
                    ·
                      rfl

theorem cell23_2696710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2696710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696710 prefixEnd_2696710 := by exact prefixLift 2696710
  have htrace : WordTrace (prefixWord ++ tailWord_2696710) baseStart_2696710 baseEnd_2696710 := by
    simpa [prefixWord, tailWord_2696710, baseEnd_2696710] using wordTrace_append hprefix tailTrace_2696710
  have hstable : (prefixWord ++ tailWord_2696710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696710).length < 2 ^ (prefixWord ++ tailWord_2696710).sum := by decide
  have hdescent : baseEnd_2696710 < baseStart_2696710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696716 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 2, 2, 3]
def baseStart_2696716 : Nat := 118140960795 + 2696716 * 2 ^ 59
def prefixEnd_2696716 : Nat := 4983230072969 + 3 ^ 40 * 2696716 * 2
def baseEnd_2696716 : Nat := 1384711496670176319948035

theorem tailTrace_2696716 : CollatzResearch.WordTrace tailWord_2696716 prefixEnd_2696716 1384711496670176319948035 := by
  unfold tailWord_2696716
  simp only [CollatzResearch.WordTrace]
  refine ⟨49178656449132984635331001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65571541932177312847108001 49178656449132984635331001)
  ·
    refine ⟨36883992336849738476498251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49178656449132984635331001 36883992336849738476498251)
    ·
      refine ⟨55325988505274607714747377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36883992336849738476498251 55325988505274607714747377)
      ·
        refine ⟨41494491378955955786060533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55325988505274607714747377 41494491378955955786060533)
        ·
          refine ⟨3890108566777120854943175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41494491378955955786060533 3890108566777120854943175)
          ·
            refine ⟨5835162850165681282414763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890108566777120854943175 5835162850165681282414763)
            ·
              refine ⟨8752744275248521923622145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835162850165681282414763 8752744275248521923622145)
              ·
                refine ⟨6564558206436391442716609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8752744275248521923622145 6564558206436391442716609)
                ·
                  refine ⟨4923418654827293582037457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6564558206436391442716609 4923418654827293582037457)
                  ·
                    refine ⟨3692563991120470186528093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4923418654827293582037457 3692563991120470186528093)
                    ·
                      refine ⟨1384711496670176319948035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3692563991120470186528093 1384711496670176319948035)
                      ·
                        rfl

theorem cell23_2696716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_2696716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696716 prefixEnd_2696716 := by exact prefixLift 2696716
  have htrace : WordTrace (prefixWord ++ tailWord_2696716) baseStart_2696716 baseEnd_2696716 := by
    simpa [prefixWord, tailWord_2696716, baseEnd_2696716] using wordTrace_append hprefix tailTrace_2696716
  have hstable : (prefixWord ++ tailWord_2696716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696716).length < 2 ^ (prefixWord ++ tailWord_2696716).sum := by decide
  have hdescent : baseEnd_2696716 < baseStart_2696716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696723 : List Nat := [1, 1, 1, 2, 1, 7, 3, 2, 1, 4]
def baseStart_2696723 : Nat := 118140960795 + 2696723 * 2 ^ 59
def prefixEnd_2696723 : Nat := 4983230072969 + 3 ^ 40 * 2696723 * 2
def baseEnd_2696723 : Nat := 461571697011585930853501

theorem tailTrace_2696723 : CollatzResearch.WordTrace tailWord_2696723 prefixEnd_2696723 461571697011585930853501 := by
  unfold tailWord_2696723
  simp only [CollatzResearch.WordTrace]
  refine ⟨98357568209240609466166823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65571712139493739644111215 98357568209240609466166823)
  ·
    refine ⟨147536352313860914199250235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98357568209240609466166823 147536352313860914199250235)
    ·
      refine ⟨221304528470791371298875353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147536352313860914199250235 221304528470791371298875353)
      ·
        refine ⟨165978396353093528474156515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221304528470791371298875353 165978396353093528474156515)
        ·
          refine ⟨248967594529640292711234773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165978396353093528474156515 248967594529640292711234773)
          ·
            refine ⟨5835177996788444360419565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 248967594529640292711234773 5835177996788444360419565)
            ·
              refine ⟨2188191748795666635157337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5835177996788444360419565 2188191748795666635157337)
              ·
                refine ⟨1641143811596749976368003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2188191748795666635157337 1641143811596749976368003)
                ·
                  refine ⟨2461715717395124964552005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641143811596749976368003 2461715717395124964552005)
                  ·
                    refine ⟨461571697011585930853501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2461715717395124964552005 461571697011585930853501)
                    ·
                      rfl

theorem cell23_2696723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 1, 4].length) (baseStart_2696723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696723 prefixEnd_2696723 := by exact prefixLift 2696723
  have htrace : WordTrace (prefixWord ++ tailWord_2696723) baseStart_2696723 baseEnd_2696723 := by
    simpa [prefixWord, tailWord_2696723, baseEnd_2696723] using wordTrace_append hprefix tailTrace_2696723
  have hstable : (prefixWord ++ tailWord_2696723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696723).length < 2 ^ (prefixWord ++ tailWord_2696723).sum := by decide
  have hdescent : baseEnd_2696723 < baseStart_2696723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696736 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 6]
def baseStart_2696736 : Nat := 118140960795 + 2696736 * 2 ^ 59
def prefixEnd_2696736 : Nat := 4983230072969 + 3 ^ 40 * 2696736 * 2
def baseEnd_2696736 : Nat := 153857974031474026855327

theorem tailTrace_2696736 : CollatzResearch.WordTrace tailWord_2696736 prefixEnd_2696736 153857974031474026855327 := by
  unfold tailWord_2696736
  simp only [CollatzResearch.WordTrace]
  refine ⟨49179021179096756343195031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65572028238795675124260041 49179021179096756343195031)
  ·
    refine ⟨73768531768645134514792547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49179021179096756343195031 73768531768645134514792547)
    ·
      refine ⟨110652797652967701772188821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73768531768645134514792547 110652797652967701772188821)
      ·
        refine ⟨5186849889982861020571351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110652797652967701772188821 5186849889982861020571351)
        ·
          refine ⟨7780274834974291530857027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186849889982861020571351 7780274834974291530857027)
          ·
            refine ⟨11670412252461437296285541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7780274834974291530857027 11670412252461437296285541)
            ·
              refine ⟨2188202297336519493053539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11670412252461437296285541 2188202297336519493053539)
              ·
                refine ⟨3282303446004779239580309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2188202297336519493053539 3282303446004779239580309)
                ·
                  refine ⟨153857974031474026855327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3282303446004779239580309 153857974031474026855327)
                  ·
                    rfl

theorem cell23_2696736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 6].length) (baseStart_2696736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696736 prefixEnd_2696736 := by exact prefixLift 2696736
  have htrace : WordTrace (prefixWord ++ tailWord_2696736) baseStart_2696736 baseEnd_2696736 := by
    simpa [prefixWord, tailWord_2696736, baseEnd_2696736] using wordTrace_append hprefix tailTrace_2696736
  have hstable : (prefixWord ++ tailWord_2696736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696736).length < 2 ^ (prefixWord ++ tailWord_2696736).sum := by decide
  have hdescent : baseEnd_2696736 < baseStart_2696736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696746 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_2696746 : Nat := 118140960795 + 2696746 * 2 ^ 59
def prefixEnd_2696746 : Nat := 4983230072969 + 3 ^ 40 * 2696746 * 2
def baseEnd_2696746 : Nat := 1384726901089811202572897

theorem tailTrace_2696746 : CollatzResearch.WordTrace tailWord_2696746 prefixEnd_2696746 1384726901089811202572897 := by
  unfold tailWord_2696746
  simp only [CollatzResearch.WordTrace]
  refine ⟨24589601772039321098563523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65572271392104856262836061 24589601772039321098563523)
  ·
    refine ⟨36884402658058981647845285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24589601772039321098563523 36884402658058981647845285)
    ·
      refine ⟨6915825498386059058970991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36884402658058981647845285 6915825498386059058970991)
      ·
        refine ⟨10373738247579088588456487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915825498386059058970991 10373738247579088588456487)
        ·
          refine ⟨15560607371368632882684731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10373738247579088588456487 15560607371368632882684731)
          ·
            refine ⟨23340911057052949324027097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15560607371368632882684731 23340911057052949324027097)
            ·
              refine ⟨17505683292789711993020323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23340911057052949324027097 17505683292789711993020323)
              ·
                refine ⟨26258524939184567989530485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17505683292789711993020323 26258524939184567989530485)
                ·
                  refine ⟨2461736713048553249018483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26258524939184567989530485 2461736713048553249018483)
                  ·
                    refine ⟨3692605069572829873527725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2461736713048553249018483 3692605069572829873527725)
                    ·
                      refine ⟨1384726901089811202572897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3692605069572829873527725 1384726901089811202572897)
                      ·
                        rfl

theorem cell23_2696746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_2696746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696746 prefixEnd_2696746 := by exact prefixLift 2696746
  have htrace : WordTrace (prefixWord ++ tailWord_2696746) baseStart_2696746 baseEnd_2696746 := by
    simpa [prefixWord, tailWord_2696746, baseEnd_2696746] using wordTrace_append hprefix tailTrace_2696746
  have hstable : (prefixWord ++ tailWord_2696746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696746).length < 2 ^ (prefixWord ++ tailWord_2696746).sum := by decide
  have hdescent : baseEnd_2696746 < baseStart_2696746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696774 : List Nat := [6, 1, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_2696774 : Nat := 118140960795 + 2696774 * 2 ^ 59
def prefixEnd_2696774 : Nat := 4983230072969 + 3 ^ 40 * 2696774 * 2
def baseEnd_2696774 : Nat := 461580426182712364340923

theorem tailTrace_2696774 : CollatzResearch.WordTrace tailWord_2696774 prefixEnd_2696774 461580426182712364340923 := by
  unfold tailWord_2696774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073732135376745161758543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65572952221370563450848917 3073732135376745161758543)
  ·
    refine ⟨4610598203065117742637815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3073732135376745161758543 4610598203065117742637815)
    ·
      refine ⟨6915897304597676613956723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4610598203065117742637815 6915897304597676613956723)
      ·
        refine ⟨10373845956896514920935085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915897304597676613956723 10373845956896514920935085)
        ·
          refine ⟨3890192233836193095350657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10373845956896514920935085 3890192233836193095350657)
          ·
            refine ⟨2917644175377144821512993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3890192233836193095350657 2917644175377144821512993)
            ·
              refine ⟨2188233131532858616134745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2917644175377144821512993 2188233131532858616134745)
              ·
                refine ⟨1641174848649643962101059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2188233131532858616134745 1641174848649643962101059)
                ·
                  refine ⟨2461762272974465943151589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641174848649643962101059 2461762272974465943151589)
                  ·
                    refine ⟨461580426182712364340923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2461762272974465943151589 461580426182712364340923)
                    ·
                      rfl

theorem cell23_2696774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_2696774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696774 prefixEnd_2696774 := by exact prefixLift 2696774
  have htrace : WordTrace (prefixWord ++ tailWord_2696774) baseStart_2696774 baseEnd_2696774 := by
    simpa [prefixWord, tailWord_2696774, baseEnd_2696774] using wordTrace_append hprefix tailTrace_2696774
  have hstable : (prefixWord ++ tailWord_2696774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696774).length < 2 ^ (prefixWord ++ tailWord_2696774).sum := by decide
  have hdescent : baseEnd_2696774 < baseStart_2696774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696780 : List Nat := [2, 2, 1, 3, 1, 3, 4, 2, 1, 1, 3]
def baseStart_2696780 : Nat := 118140960795 + 2696780 * 2 ^ 59
def prefixEnd_2696780 : Nat := 4983230072969 + 3 ^ 40 * 2696780 * 2
def baseEnd_2696780 : Nat := 1384744359432064069547741

theorem tailTrace_2696780 : CollatzResearch.WordTrace tailWord_2696780 prefixEnd_2696780 1384744359432064069547741 := by
  unfold tailWord_2696780
  simp only [CollatzResearch.WordTrace]
  refine ⟨49179823585017054100495897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65573098113356072133994529 49179823585017054100495897)
  ·
    refine ⟨36884867688762790575371923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49179823585017054100495897 36884867688762790575371923)
    ·
      refine ⟨55327301533144185863057885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36884867688762790575371923 55327301533144185863057885)
      ·
        refine ⟨20747738074929069698646707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55327301533144185863057885 20747738074929069698646707)
        ·
          refine ⟨31121607112393604547970061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20747738074929069698646707 31121607112393604547970061)
          ·
            refine ⟨11670602667147601705488773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31121607112393604547970061 11670602667147601705488773)
            ·
              refine ⟨2188238000090175319779145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11670602667147601705488773 2188238000090175319779145)
              ·
                refine ⟨1641178500067631489834359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2188238000090175319779145 1641178500067631489834359)
                ·
                  refine ⟨2461767750101447234751539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641178500067631489834359 2461767750101447234751539)
                  ·
                    refine ⟨3692651625152170852127309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2461767750101447234751539 3692651625152170852127309)
                    ·
                      refine ⟨1384744359432064069547741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3692651625152170852127309 1384744359432064069547741)
                      ·
                        rfl

theorem cell23_2696780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_2696780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696780 prefixEnd_2696780 := by exact prefixLift 2696780
  have htrace : WordTrace (prefixWord ++ tailWord_2696780) baseStart_2696780 baseEnd_2696780 := by
    simpa [prefixWord, tailWord_2696780, baseEnd_2696780] using wordTrace_append hprefix tailTrace_2696780
  have hstable : (prefixWord ++ tailWord_2696780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696780).length < 2 ^ (prefixWord ++ tailWord_2696780).sum := by decide
  have hdescent : baseEnd_2696780 < baseStart_2696780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696796 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_2696796 : Nat := 118140960795 + 2696796 * 2 ^ 59
def prefixEnd_2696796 : Nat := 4983230072969 + 3 ^ 40 * 2696796 * 2
def baseEnd_2696796 : Nat := 461584191707512002315889

theorem tailTrace_2696796 : CollatzResearch.WordTrace tailWord_2696796 prefixEnd_2696796 461584191707512002315889 := by
  unfold tailWord_2696796
  simp only [CollatzResearch.WordTrace]
  refine ⟨49180115368988071466787121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65573487158650761955716161 49180115368988071466787121)
  ·
    refine ⟨36885086526741053600090341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49180115368988071466787121 36885086526741053600090341)
    ·
      refine ⟨6915953723763947550016939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36885086526741053600090341 6915953723763947550016939)
      ·
        refine ⟨10373930585645921325025409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915953723763947550016939 10373930585645921325025409)
        ·
          refine ⟨7780447939234440993769057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10373930585645921325025409 7780447939234440993769057)
          ·
            refine ⟨5835335954425830745326793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7780447939234440993769057 5835335954425830745326793)
            ·
              refine ⟨4376501965819373058995095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5835335954425830745326793 4376501965819373058995095)
              ·
                refine ⟨6564752948729059588492643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376501965819373058995095 6564752948729059588492643)
                ·
                  refine ⟨9847129423093589382738965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6564752948729059588492643 9847129423093589382738965)
                  ·
                    refine ⟨461584191707512002315889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9847129423093589382738965 461584191707512002315889)
                    ·
                      rfl

theorem cell23_2696796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_2696796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696796 prefixEnd_2696796 := by exact prefixLift 2696796
  have htrace : WordTrace (prefixWord ++ tailWord_2696796) baseStart_2696796 baseEnd_2696796 := by
    simpa [prefixWord, tailWord_2696796, baseEnd_2696796] using wordTrace_append hprefix tailTrace_2696796
  have hstable : (prefixWord ++ tailWord_2696796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696796).length < 2 ^ (prefixWord ++ tailWord_2696796).sum := by decide
  have hdescent : baseEnd_2696796 < baseStart_2696796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696803 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 3, 2, 2]
def baseStart_2696803 : Nat := 118140960795 + 2696803 * 2 ^ 59
def prefixEnd_2696803 : Nat := 4983230072969 + 3 ^ 40 * 2696803 * 2
def baseEnd_2696803 : Nat := 1384756169487117479560135

theorem tailTrace_2696803 : CollatzResearch.WordTrace tailWord_2696803 prefixEnd_2696803 1384756169487117479560135 := by
  unfold tailWord_2696803
  simp only [CollatzResearch.WordTrace]
  refine ⟨98360486048950783129079063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65573657365967188752719375 98360486048950783129079063)
  ·
    refine ⟨147540729073426174693618595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98360486048950783129079063 147540729073426174693618595)
    ·
      refine ⟨221311093610139262040427893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147540729073426174693618595 221311093610139262040427893)
      ·
        refine ⟨20747915025950555816290115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221311093610139262040427893 20747915025950555816290115)
        ·
          refine ⟨31121872538925833724435173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20747915025950555816290115 31121872538925833724435173)
          ·
            refine ⟨5835351101048593823331595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31121872538925833724435173 5835351101048593823331595)
            ·
              refine ⟨8753026651572890734997393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835351101048593823331595 8753026651572890734997393)
              ·
                refine ⟨6564769988679668051248045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8753026651572890734997393 6564769988679668051248045)
                ·
                  refine ⟨2461788745754875519218017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6564769988679668051248045 2461788745754875519218017)
                  ·
                    refine ⟨1846341559316156639413513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2461788745754875519218017 1846341559316156639413513)
                    ·
                      refine ⟨1384756169487117479560135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846341559316156639413513 1384756169487117479560135)
                      ·
                        rfl

theorem cell23_2696803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_2696803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696803 prefixEnd_2696803 := by exact prefixLift 2696803
  have htrace : WordTrace (prefixWord ++ tailWord_2696803) baseStart_2696803 baseEnd_2696803 := by
    simpa [prefixWord, tailWord_2696803, baseEnd_2696803] using wordTrace_append hprefix tailTrace_2696803
  have hstable : (prefixWord ++ tailWord_2696803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696803).length < 2 ^ (prefixWord ++ tailWord_2696803).sum := by decide
  have hdescent : baseEnd_2696803 < baseStart_2696803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696850 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_2696850 : Nat := 118140960795 + 2696850 * 2 ^ 59
def prefixEnd_2696850 : Nat := 4983230072969 + 3 ^ 40 * 2696850 * 2
def baseEnd_2696850 : Nat := 1384780303077878795672419

theorem tailTrace_2696850 : CollatzResearch.WordTrace tailWord_2696850 prefixEnd_2696850 1384780303077878795672419 := by
  unfold tailWord_2696850
  simp only [CollatzResearch.WordTrace]
  refine ⟨24590550069945127539010001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65574800186520340104026669 24590550069945127539010001)
  ·
    refine ⟨18442912552458845654257501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24590550069945127539010001 18442912552458845654257501)
    ·
      refine ⟨6916092207172067120346563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18442912552458845654257501 6916092207172067120346563)
      ·
        refine ⟨10374138310758100680519845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6916092207172067120346563 10374138310758100680519845)
        ·
          refine ⟨1945150933267143877597471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10374138310758100680519845 1945150933267143877597471)
          ·
            refine ⟨2917726399900715816396207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1945150933267143877597471 2917726399900715816396207)
            ·
              refine ⟨4376589599851073724594311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2917726399900715816396207 4376589599851073724594311)
              ·
                refine ⟨6564884399776610586891467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376589599851073724594311 6564884399776610586891467)
                ·
                  refine ⟨9847326599664915880337201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6564884399776610586891467 9847326599664915880337201)
                  ·
                    refine ⟨7385494949748686910252901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9847326599664915880337201 7385494949748686910252901)
                    ·
                      refine ⟨1384780303077878795672419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7385494949748686910252901 1384780303077878795672419)
                      ·
                        rfl

theorem cell23_2696850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_2696850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696850 prefixEnd_2696850 := by exact prefixLift 2696850
  have htrace : WordTrace (prefixWord ++ tailWord_2696850) baseStart_2696850 baseEnd_2696850 := by
    simpa [prefixWord, tailWord_2696850, baseEnd_2696850] using wordTrace_append hprefix tailTrace_2696850
  have hstable : (prefixWord ++ tailWord_2696850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696850).length < 2 ^ (prefixWord ++ tailWord_2696850).sum := by decide
  have hdescent : baseEnd_2696850 < baseStart_2696850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696879 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_2696879 : Nat := 118140960795 + 2696879 * 2 ^ 59
def prefixEnd_2696879 : Nat := 4983230072969 + 3 ^ 40 * 2696879 * 2
def baseEnd_2696879 : Nat := 1384795194016859182209785

theorem tailTrace_2696879 : CollatzResearch.WordTrace tailWord_2696879 prefixEnd_2696879 1384795194016859182209785 := by
  unfold tailWord_2696879
  simp only [CollatzResearch.WordTrace]
  refine ⟨98363257996675448108845691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65575505331116965405897127 98363257996675448108845691)
  ·
    refine ⟨147544886995013172163268537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98363257996675448108845691 147544886995013172163268537)
    ·
      refine ⟨110658665246259879122451403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147544886995013172163268537 110658665246259879122451403)
      ·
        refine ⟨165987997869389818683677105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110658665246259879122451403 165987997869389818683677105)
        ·
          refine ⟨124490998402042364012757829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165987997869389818683677105 124490998402042364012757829)
          ·
            refine ⟨23342062200382943252392093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124490998402042364012757829 23342062200382943252392093)
            ·
              refine ⟨8753273325143603719647035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23342062200382943252392093 8753273325143603719647035)
              ·
                refine ⟨13129909987715405579470553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8753273325143603719647035 13129909987715405579470553)
                ·
                  refine ⟨9847432490786554184602915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13129909987715405579470553 9847432490786554184602915)
                  ·
                    refine ⟨14771148736179831276904373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9847432490786554184602915 14771148736179831276904373)
                    ·
                      refine ⟨1384795194016859182209785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14771148736179831276904373 1384795194016859182209785)
                      ·
                        rfl

theorem cell23_2696879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_2696879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696879 prefixEnd_2696879 := by exact prefixLift 2696879
  have htrace : WordTrace (prefixWord ++ tailWord_2696879) baseStart_2696879 baseEnd_2696879 := by
    simpa [prefixWord, tailWord_2696879, baseEnd_2696879] using wordTrace_append hprefix tailTrace_2696879
  have hstable : (prefixWord ++ tailWord_2696879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696879).length < 2 ^ (prefixWord ++ tailWord_2696879).sum := by decide
  have hdescent : baseEnd_2696879 < baseStart_2696879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696889 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2696889 : Nat := 118140960795 + 2696889 * 2 ^ 59
def prefixEnd_2696889 : Nat := 4983230072969 + 3 ^ 40 * 2696889 * 2
def baseEnd_2696889 : Nat := 1384800328823404143084739

theorem tailTrace_2696889 : CollatzResearch.WordTrace tailWord_2696889 prefixEnd_2696889 1384800328823404143084739 := by
  unfold tailWord_2696889
  simp only [CollatzResearch.WordTrace]
  refine ⟨98363622726639219816709721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65575748484426146544473147 98363622726639219816709721)
  ·
    refine ⟨73772717044979414862532291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98363622726639219816709721 73772717044979414862532291)
    ·
      refine ⟨110659075567469122293798437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73772717044979414862532291 110659075567469122293798437)
      ·
        refine ⟨20748576668900460430087207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110659075567469122293798437 20748576668900460430087207)
        ·
          refine ⟨31122865003350690645130811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20748576668900460430087207 31122865003350690645130811)
          ·
            refine ⟨46684297505026035967696217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31122865003350690645130811 46684297505026035967696217)
            ·
              refine ⟨35013223128769526975772163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46684297505026035967696217 35013223128769526975772163)
              ·
                refine ⟨52519834693154290463658245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35013223128769526975772163 52519834693154290463658245)
                ·
                  refine ⟨9847469004966429461935921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52519834693154290463658245 9847469004966429461935921)
                  ·
                    refine ⟨7385601753724822096451941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9847469004966429461935921 7385601753724822096451941)
                    ·
                      refine ⟨1384800328823404143084739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7385601753724822096451941 1384800328823404143084739)
                      ·
                        rfl

theorem cell23_2696889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2696889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696889 prefixEnd_2696889 := by exact prefixLift 2696889
  have htrace : WordTrace (prefixWord ++ tailWord_2696889) baseStart_2696889 baseEnd_2696889 := by
    simpa [prefixWord, tailWord_2696889, baseEnd_2696889] using wordTrace_append hprefix tailTrace_2696889
  have hstable : (prefixWord ++ tailWord_2696889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696889).length < 2 ^ (prefixWord ++ tailWord_2696889).sum := by decide
  have hdescent : baseEnd_2696889 < baseStart_2696889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696893 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 4, 2, 2]
def baseStart_2696893 : Nat := 118140960795 + 2696893 * 2 ^ 59
def prefixEnd_2696893 : Nat := 4983230072969 + 3 ^ 40 * 2696893 * 2
def baseEnd_2696893 : Nat := 1384802382746022127434721

theorem tailTrace_2696893 : CollatzResearch.WordTrace tailWord_2696893 prefixEnd_2696893 1384802382746022127434721 := by
  unfold tailWord_2696893
  simp only [CollatzResearch.WordTrace]
  refine ⟨98363768618624728499855333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65575845745749818999903555 98363768618624728499855333)
  ·
    refine ⟨18443206615992136593722875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98363768618624728499855333 18443206615992136593722875)
    ·
      refine ⟨27664809923988204890584313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18443206615992136593722875 27664809923988204890584313)
      ·
        refine ⟨20748607442991153667938235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27664809923988204890584313 20748607442991153667938235)
        ·
          refine ⟨31122911164486730501907353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20748607442991153667938235 31122911164486730501907353)
          ·
            refine ⟨23342183373365047876430515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31122911164486730501907353 23342183373365047876430515)
            ·
              refine ⟨35013275060047571814645773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23342183373365047876430515 35013275060047571814645773)
              ·
                refine ⟨13129978147517839430492165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35013275060047571814645773 13129978147517839430492165)
                ·
                  refine ⟨2461870902659594893217281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13129978147517839430492165 2461870902659594893217281)
                  ·
                    refine ⟨1846403176994696169912961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2461870902659594893217281 1846403176994696169912961)
                    ·
                      refine ⟨1384802382746022127434721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846403176994696169912961 1384802382746022127434721)
                      ·
                        rfl

theorem cell23_2696893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_2696893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696893 prefixEnd_2696893 := by exact prefixLift 2696893
  have htrace : WordTrace (prefixWord ++ tailWord_2696893) baseStart_2696893 baseEnd_2696893 := by
    simpa [prefixWord, tailWord_2696893, baseEnd_2696893] using wordTrace_append hprefix tailTrace_2696893
  have hstable : (prefixWord ++ tailWord_2696893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696893).length < 2 ^ (prefixWord ++ tailWord_2696893).sum := by decide
  have hdescent : baseEnd_2696893 < baseStart_2696893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696910 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2]
def baseStart_2696910 : Nat := 118140960795 + 2696910 * 2 ^ 59
def prefixEnd_2696910 : Nat := 4983230072969 + 3 ^ 40 * 2696910 * 2
def baseEnd_2696910 : Nat := 1384811111917148560922143

theorem tailTrace_2696910 : CollatzResearch.WordTrace tailWord_2696910 prefixEnd_2696910 1384811111917148560922143 := by
  unfold tailWord_2696910
  simp only [CollatzResearch.WordTrace]
  refine ⟨12295548582445392550403023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65576259106375426935482789 12295548582445392550403023)
  ·
    refine ⟨18443322873668088825604535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12295548582445392550403023 18443322873668088825604535)
    ·
      refine ⟨27664984310502133238406803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18443322873668088825604535 27664984310502133238406803)
      ·
        refine ⟨41497476465753199857610205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27664984310502133238406803 41497476465753199857610205)
        ·
          refine ⟨15561553674657449946603827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41497476465753199857610205 15561553674657449946603827)
          ·
            refine ⟨23342330511986174919905741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15561553674657449946603827 23342330511986174919905741)
            ·
              refine ⟨8753373941994815594964653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23342330511986174919905741 8753373941994815594964653)
              ·
                refine ⟨3282515228248055848111745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8753373941994815594964653 3282515228248055848111745)
                ·
                  refine ⟨2461886421186041886083809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3282515228248055848111745 2461886421186041886083809)
                  ·
                    refine ⟨1846414815889531414562857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2461886421186041886083809 1846414815889531414562857)
                    ·
                      refine ⟨1384811111917148560922143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846414815889531414562857 1384811111917148560922143)
                      ·
                        rfl

theorem cell23_2696910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_2696910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696910 prefixEnd_2696910 := by exact prefixLift 2696910
  have htrace : WordTrace (prefixWord ++ tailWord_2696910) baseStart_2696910 baseEnd_2696910 := by
    simpa [prefixWord, tailWord_2696910, baseEnd_2696910] using wordTrace_append hprefix tailTrace_2696910
  have hstable : (prefixWord ++ tailWord_2696910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696910).length < 2 ^ (prefixWord ++ tailWord_2696910).sum := by decide
  have hdescent : baseEnd_2696910 < baseStart_2696910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696939 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 5]
def baseStart_2696939 : Nat := 118140960795 + 2696939 * 2 ^ 59
def prefixEnd_2696939 : Nat := 4983230072969 + 3 ^ 40 * 2696939 * 2
def baseEnd_2696939 : Nat := 1384826002856128947459509

theorem tailTrace_2696939 : CollatzResearch.WordTrace tailWord_2696939 prefixEnd_2696939 1384826002856128947459509 := by
  unfold tailWord_2696939
  simp only [CollatzResearch.WordTrace]
  refine ⟨98365446376458078356029871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65576964250972052237353247 98365446376458078356029871)
  ·
    refine ⟨147548169564687117534044807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98365446376458078356029871 147548169564687117534044807)
    ·
      refine ⟨221322254347030676301067211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147548169564687117534044807 221322254347030676301067211)
      ·
        refine ⟨331983381520546014451600817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221322254347030676301067211 331983381520546014451600817)
        ·
          refine ⟨248987536140409510838700613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331983381520546014451600817 248987536140409510838700613)
          ·
            refine ⟨46685163026326783282256365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248987536140409510838700613 46685163026326783282256365)
            ·
              refine ⟨17506936134872543730846137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46685163026326783282256365 17506936134872543730846137)
              ·
                refine ⟨13130202101154407798134603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17506936134872543730846137 13130202101154407798134603)
                ·
                  refine ⟨19695303151731611697201905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13130202101154407798134603 19695303151731611697201905)
                  ·
                    refine ⟨14771477363798708772901429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19695303151731611697201905 14771477363798708772901429)
                    ·
                      refine ⟨1384826002856128947459509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14771477363798708772901429 1384826002856128947459509)
                      ·
                        rfl

theorem cell23_2696939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 5].length) (baseStart_2696939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696939 prefixEnd_2696939 := by exact prefixLift 2696939
  have htrace : WordTrace (prefixWord ++ tailWord_2696939) baseStart_2696939 baseEnd_2696939 := by
    simpa [prefixWord, tailWord_2696939, baseEnd_2696939] using wordTrace_append hprefix tailTrace_2696939
  have hstable : (prefixWord ++ tailWord_2696939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696939).length < 2 ^ (prefixWord ++ tailWord_2696939).sum := by decide
  have hdescent : baseEnd_2696939 < baseStart_2696939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696946 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_2696946 : Nat := 118140960795 + 2696946 * 2 ^ 59
def prefixEnd_2696946 : Nat := 4983230072969 + 3 ^ 40 * 2696946 * 2
def baseEnd_2696946 : Nat := 461609865740236806690659

theorem tailTrace_2696946 : CollatzResearch.WordTrace tailWord_2696946 prefixEnd_2696946 461609865740236806690659 := by
  unfold tailWord_2696946
  simp only [CollatzResearch.WordTrace]
  refine ⟨24591425421858179637883673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65577134458288479034356461 24591425421858179637883673)
  ·
    refine ⟨18443569066393634728412755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24591425421858179637883673 18443569066393634728412755)
    ·
      refine ⟨27665353599590452092619133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18443569066393634728412755 27665353599590452092619133)
      ·
        refine ⟨10374507599846419534732175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27665353599590452092619133 10374507599846419534732175)
        ·
          refine ⟨15561761399769629302098263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10374507599846419534732175 15561761399769629302098263)
          ·
            refine ⟨23342642099654443953147395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15561761399769629302098263 23342642099654443953147395)
            ·
              refine ⟨35013963149481665929721093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23342642099654443953147395 35013963149481665929721093)
              ·
                refine ⟨6565118090527812361822705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35013963149481665929721093 6565118090527812361822705)
                ·
                  refine ⟨4923838567895859271367029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6565118090527812361822705 4923838567895859271367029)
                  ·
                    refine ⟨461609865740236806690659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4923838567895859271367029 461609865740236806690659)
                    ·
                      rfl

theorem cell23_2696946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_2696946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696946 prefixEnd_2696946 := by exact prefixLift 2696946
  have htrace : WordTrace (prefixWord ++ tailWord_2696946) baseStart_2696946 baseEnd_2696946 := by
    simpa [prefixWord, tailWord_2696946, baseEnd_2696946] using wordTrace_append hprefix tailTrace_2696946
  have hstable : (prefixWord ++ tailWord_2696946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696946).length < 2 ^ (prefixWord ++ tailWord_2696946).sum := by decide
  have hdescent : baseEnd_2696946 < baseStart_2696946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696950 : List Nat := [5, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_2696950 : Nat := 118140960795 + 2696950 * 2 ^ 59
def prefixEnd_2696950 : Nat := 4983230072969 + 3 ^ 40 * 2696950 * 2
def baseEnd_2696950 : Nat := 153870183460369822713551

theorem tailTrace_2696950 : CollatzResearch.WordTrace tailWord_2696950 prefixEnd_2696950 153870183460369822713551 := by
  unfold tailWord_2696950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6147865473713639202167519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65577231719612151489786869 6147865473713639202167519)
  ·
    refine ⟨9221798210570458803251279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6147865473713639202167519 9221798210570458803251279)
    ·
      refine ⟨13832697315855688204876919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9221798210570458803251279 13832697315855688204876919)
      ·
        refine ⟨20749045973783532307315379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13832697315855688204876919 20749045973783532307315379)
        ·
          refine ⟨31123568960675298460973069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20749045973783532307315379 31123568960675298460973069)
          ·
            refine ⟨11671338360253236922864901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31123568960675298460973069 11671338360253236922864901)
            ·
              refine ⟨2188375942547481923037169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11671338360253236922864901 2188375942547481923037169)
              ·
                refine ⟨1641281956910611442277877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2188375942547481923037169 1641281956910611442277877)
                ·
                  refine ⟨153870183460369822713551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1641281956910611442277877 153870183460369822713551)
                  ·
                    rfl

theorem cell23_2696950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_2696950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696950 prefixEnd_2696950 := by exact prefixLift 2696950
  have htrace : WordTrace (prefixWord ++ tailWord_2696950) baseStart_2696950 baseEnd_2696950 := by
    simpa [prefixWord, tailWord_2696950, baseEnd_2696950] using wordTrace_append hprefix tailTrace_2696950
  have hstable : (prefixWord ++ tailWord_2696950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696950).length < 2 ^ (prefixWord ++ tailWord_2696950).sum := by decide
  have hdescent : baseEnd_2696950 < baseStart_2696950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696979 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 4]
def baseStart_2696979 : Nat := 118140960795 + 2696979 * 2 ^ 59
def prefixEnd_2696979 : Nat := 4983230072969 + 3 ^ 40 * 2696979 * 2
def baseEnd_2696979 : Nat := 1384846542082308790959325

theorem tailTrace_2696979 : CollatzResearch.WordTrace tailWord_2696979 prefixEnd_2696979 1384846542082308790959325 := by
  unfold tailWord_2696979
  simp only [CollatzResearch.WordTrace]
  refine ⟨98366905296313165187485991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65577936864208776791657327 98366905296313165187485991)
  ·
    refine ⟨147550357944469747781228987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98366905296313165187485991 147550357944469747781228987)
    ·
      refine ⟨221325536916704621671843481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147550357944469747781228987 221325536916704621671843481)
      ·
        refine ⟨165994152687528466253882611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221325536916704621671843481 165994152687528466253882611)
        ·
          refine ⟨248991229031292699380823917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165994152687528466253882611 248991229031292699380823917)
          ·
            refine ⟨93371710886734762267808969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248991229031292699380823917 93371710886734762267808969)
            ·
              refine ⟨70028783165051071700856727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93371710886734762267808969 70028783165051071700856727)
              ·
                refine ⟨105043174747576607551285091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70028783165051071700856727 105043174747576607551285091)
                ·
                  refine ⟨157564762121364911326927637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105043174747576607551285091 157564762121364911326927637)
                  ·
                    refine ⟨7385848224438980218449733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 157564762121364911326927637 7385848224438980218449733)
                    ·
                      refine ⟨1384846542082308790959325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7385848224438980218449733 1384846542082308790959325)
                      ·
                        rfl

theorem cell23_2696979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_2696979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696979 prefixEnd_2696979 := by exact prefixLift 2696979
  have htrace : WordTrace (prefixWord ++ tailWord_2696979) baseStart_2696979 baseEnd_2696979 := by
    simpa [prefixWord, tailWord_2696979, baseEnd_2696979] using wordTrace_append hprefix tailTrace_2696979
  have hstable : (prefixWord ++ tailWord_2696979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696979).length < 2 ^ (prefixWord ++ tailWord_2696979).sum := by decide
  have hdescent : baseEnd_2696979 < baseStart_2696979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696983 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 4]
def baseStart_2696983 : Nat := 118140960795 + 2696983 * 2 ^ 59
def prefixEnd_2696983 : Nat := 4983230072969 + 3 ^ 40 * 2696983 * 2
def baseEnd_2696983 : Nat := 1384848596004926775309307

theorem tailTrace_2696983 : CollatzResearch.WordTrace tailWord_2696983 prefixEnd_2696983 1384848596004926775309307 := by
  unfold tailWord_2696983
  simp only [CollatzResearch.WordTrace]
  refine ⟨98367051188298673870631603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65578034125532449247087735 98367051188298673870631603)
  ·
    refine ⟨147550576782448010805947405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98367051188298673870631603 147550576782448010805947405)
    ·
      refine ⟨55331466293418004052230277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147550576782448010805947405 55331466293418004052230277)
      ·
        refine ⟨10374649930015875759793177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55331466293418004052230277 10374649930015875759793177)
        ·
          refine ⟨7780987447511906819844883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10374649930015875759793177 7780987447511906819844883)
          ·
            refine ⟨11671481171267860229767325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7780987447511906819844883 11671481171267860229767325)
            ·
              refine ⟨4376805439225447586162747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11671481171267860229767325 4376805439225447586162747)
              ·
                refine ⟨6565208158838171379244121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376805439225447586162747 6565208158838171379244121)
                ·
                  refine ⟨4923906119128628534433091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6565208158838171379244121 4923906119128628534433091)
                  ·
                    refine ⟨7385859178692942801649637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4923906119128628534433091 7385859178692942801649637)
                    ·
                      refine ⟨1384848596004926775309307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7385859178692942801649637 1384848596004926775309307)
                      ·
                        rfl

theorem cell23_2696983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_2696983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696983 prefixEnd_2696983 := by exact prefixLift 2696983
  have htrace : WordTrace (prefixWord ++ tailWord_2696983) baseStart_2696983 baseEnd_2696983 := by
    simpa [prefixWord, tailWord_2696983, baseEnd_2696983] using wordTrace_append hprefix tailTrace_2696983
  have hstable : (prefixWord ++ tailWord_2696983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696983).length < 2 ^ (prefixWord ++ tailWord_2696983).sum := by decide
  have hdescent : baseEnd_2696983 < baseStart_2696983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2696996 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2696996 : Nat := 118140960795 + 2696996 * 2 ^ 59
def prefixEnd_2696996 : Nat := 4983230072969 + 3 ^ 40 * 2696996 * 2
def baseEnd_2696996 : Nat := 1384855271253435224446747

theorem tailTrace_2696996 : CollatzResearch.WordTrace tailWord_2696996 prefixEnd_2696996 1384855271253435224446747 := by
  unfold tailWord_2696996
  simp only [CollatzResearch.WordTrace]
  refine ⟨49183762668625788545427421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65578350224834384727236561 49183762668625788545427421)
  ·
    refine ⟨18443911000734670704535283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49183762668625788545427421 18443911000734670704535283)
    ·
      refine ⟨27665866501102006056802925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18443911000734670704535283 27665866501102006056802925)
      ·
        refine ⟨10374699937913252271301097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27665866501102006056802925 10374699937913252271301097)
        ·
          refine ⟨7781024953434939203475823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10374699937913252271301097 7781024953434939203475823)
          ·
            refine ⟨11671537430152408805213735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7781024953434939203475823 11671537430152408805213735)
            ·
              refine ⟨17507306145228613207820603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11671537430152408805213735 17507306145228613207820603)
              ·
                refine ⟨26260959217842919811730905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17507306145228613207820603 26260959217842919811730905)
                ·
                  refine ⟨19695719413382189858798179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26260959217842919811730905 19695719413382189858798179)
                  ·
                    refine ⟨29543579120073284788197269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19695719413382189858798179 29543579120073284788197269)
                    ·
                      refine ⟨1384855271253435224446747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29543579120073284788197269 1384855271253435224446747)
                      ·
                        rfl

theorem cell23_2696996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2696996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2696996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2696996 prefixEnd_2696996 := by exact prefixLift 2696996
  have htrace : WordTrace (prefixWord ++ tailWord_2696996) baseStart_2696996 baseEnd_2696996 := by
    simpa [prefixWord, tailWord_2696996, baseEnd_2696996] using wordTrace_append hprefix tailTrace_2696996
  have hstable : (prefixWord ++ tailWord_2696996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2696996).length < 2 ^ (prefixWord ++ tailWord_2696996).sum := by decide
  have hdescent : baseEnd_2696996 < baseStart_2696996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2696996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697010 : List Nat := [3, 2, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_2697010 : Nat := 118140960795 + 2697010 * 2 ^ 59
def prefixEnd_2697010 : Nat := 4983230072969 + 3 ^ 40 * 2697010 * 2
def baseEnd_2697010 : Nat := 461620819994199389890561

theorem tailTrace_2697010 : CollatzResearch.WordTrace tailWord_2697010 prefixEnd_2697010 461620819994199389890561 := by
  unfold tailWord_2697010
  simp only [CollatzResearch.WordTrace]
  refine ⟨24592008989800214370466121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65578690639467238321242989 24592008989800214370466121)
  ·
    refine ⟨18444006742350160777849591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24592008989800214370466121 18444006742350160777849591)
    ·
      refine ⟨27666010113525241166774387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18444006742350160777849591 27666010113525241166774387)
      ·
        refine ⟨41499015170287861750161581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27666010113525241166774387 41499015170287861750161581)
        ·
          refine ⟨15562130688857948156310593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41499015170287861750161581 15562130688857948156310593)
          ·
            refine ⟨11671598016643461117232945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15562130688857948156310593 11671598016643461117232945)
            ·
              refine ⟨8753698512482595837924709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11671598016643461117232945 8753698512482595837924709)
              ·
                refine ⟨1641318471090486719610883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8753698512482595837924709 1641318471090486719610883)
                ·
                  refine ⟨2461977706635730079416325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641318471090486719610883 2461977706635730079416325)
                  ·
                    refine ⟨461620819994199389890561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2461977706635730079416325 461620819994199389890561)
                    ·
                      rfl

theorem cell23_2697010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_2697010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697010 prefixEnd_2697010 := by exact prefixLift 2697010
  have htrace : WordTrace (prefixWord ++ tailWord_2697010) baseStart_2697010 baseEnd_2697010 := by
    simpa [prefixWord, tailWord_2697010, baseEnd_2697010] using wordTrace_append hprefix tailTrace_2697010
  have hstable : (prefixWord ++ tailWord_2697010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697010).length < 2 ^ (prefixWord ++ tailWord_2697010).sum := by decide
  have hdescent : baseEnd_2697010 < baseStart_2697010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697033 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 3, 1, 3]
def baseStart_2697033 : Nat := 118140960795 + 2697033 * 2 ^ 59
def prefixEnd_2697033 : Nat := 4983230072969 + 3 ^ 40 * 2697033 * 2
def baseEnd_2697033 : Nat := 1384874270037651579684077

theorem tailTrace_2697033 : CollatzResearch.WordTrace tailWord_2697033 prefixEnd_2697033 1384874270037651579684077 := by
  unfold tailWord_2697033
  simp only [CollatzResearch.WordTrace]
  refine ⟨98368874838117532409951753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65579249892078354939967835 98368874838117532409951753)
  ·
    refine ⟨73776656128588149307463815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98368874838117532409951753 73776656128588149307463815)
    ·
      refine ⟨110664984192882223961195723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73776656128588149307463815 110664984192882223961195723)
      ·
        refine ⟨165997476289323335941793585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110664984192882223961195723 165997476289323335941793585)
        ·
          refine ⟨124498107216992501956345189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165997476289323335941793585 124498107216992501956345189)
          ·
            refine ⟨23343395103186094116814723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124498107216992501956345189 23343395103186094116814723)
            ·
              refine ⟨35015092654779141175222085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23343395103186094116814723 35015092654779141175222085)
              ·
                refine ⟨6565329872771088970354141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35015092654779141175222085 6565329872771088970354141)
                ·
                  refine ⟨2461998702289158363882803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6565329872771088970354141 2461998702289158363882803)
                  ·
                    refine ⟨3692998053433737545824205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2461998702289158363882803 3692998053433737545824205)
                    ·
                      refine ⟨1384874270037651579684077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3692998053433737545824205 1384874270037651579684077)
                      ·
                        rfl

theorem cell23_2697033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 1, 3].length) (baseStart_2697033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697033 prefixEnd_2697033 := by exact prefixLift 2697033
  have htrace : WordTrace (prefixWord ++ tailWord_2697033) baseStart_2697033 baseEnd_2697033 := by
    simpa [prefixWord, tailWord_2697033, baseEnd_2697033] using wordTrace_append hprefix tailTrace_2697033
  have hstable : (prefixWord ++ tailWord_2697033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697033).length < 2 ^ (prefixWord ++ tailWord_2697033).sum := by decide
  have hdescent : baseEnd_2697033 < baseStart_2697033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697093 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 3, 2, 3]
def baseStart_2697093 : Nat := 118140960795 + 2697093 * 2 ^ 59
def prefixEnd_2697093 : Nat := 4983230072969 + 3 ^ 40 * 2697093 * 2
def baseEnd_2697093 : Nat := 1384905078876921344933801

theorem tailTrace_2697093 : CollatzResearch.WordTrace tailWord_2697093 prefixEnd_2697093 1384905078876921344933801 := by
  unfold tailWord_2697093
  simp only [CollatzResearch.WordTrace]
  refine ⟨98371063217900162657135933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65580708811933441771423955 98371063217900162657135933)
  ·
    refine ⟨36889148706712560996425975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98371063217900162657135933 36889148706712560996425975)
    ·
      refine ⟨55333723060068841494638963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36889148706712560996425975 55333723060068841494638963)
      ·
        refine ⟨83000584590103262241958445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55333723060068841494638963 83000584590103262241958445)
        ·
          refine ⟨31125219221288723340734417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83000584590103262241958445 31125219221288723340734417)
          ·
            refine ⟨23343914415966542505550813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31125219221288723340734417 23343914415966542505550813)
            ·
              refine ⟨8753967905987453439581555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23343914415966542505550813 8753967905987453439581555)
              ·
                refine ⟨13130951858981180159372333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8753967905987453439581555 13130951858981180159372333)
                ·
                  refine ⟨4924106947117942559764625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13130951858981180159372333 4924106947117942559764625)
                  ·
                    refine ⟨3693080210338456919823469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4924106947117942559764625 3693080210338456919823469)
                    ·
                      refine ⟨1384905078876921344933801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3693080210338456919823469 1384905078876921344933801)
                      ·
                        rfl

theorem cell23_2697093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_2697093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697093 prefixEnd_2697093 := by exact prefixLift 2697093
  have htrace : WordTrace (prefixWord ++ tailWord_2697093) baseStart_2697093 baseEnd_2697093 := by
    simpa [prefixWord, tailWord_2697093, baseEnd_2697093] using wordTrace_append hprefix tailTrace_2697093
  have hstable : (prefixWord ++ tailWord_2697093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697093).length < 2 ^ (prefixWord ++ tailWord_2697093).sum := by decide
  have hdescent : baseEnd_2697093 < baseStart_2697093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697124 : List Nat := [2, 3, 1, 2, 1, 4, 1, 4, 1, 2, 2]
def baseStart_2697124 : Nat := 118140960795 + 2697124 * 2 ^ 59
def prefixEnd_2697124 : Nat := 4983230072969 + 3 ^ 40 * 2697124 * 2
def baseEnd_2697124 : Nat := 1384920996777210723646159

theorem tailTrace_2697124 : CollatzResearch.WordTrace tailWord_2697124 prefixEnd_2697124 1384920996777210723646159 := by
  unfold tailWord_2697124
  simp only [CollatzResearch.WordTrace]
  refine ⟨49186096940393927475757213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65581462587191903301009617 49186096940393927475757213)
  ·
    refine ⟨18444786352647722803408955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49186096940393927475757213 18444786352647722803408955)
    ·
      refine ⟨27667179528971584205113433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18444786352647722803408955 27667179528971584205113433)
      ·
        refine ⟨20750384646728688153835075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27667179528971584205113433 20750384646728688153835075)
        ·
          refine ⟨31125576970093032230752613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20750384646728688153835075 31125576970093032230752613)
          ·
            refine ⟨5836045681892443543266115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31125576970093032230752613 5836045681892443543266115)
            ·
              refine ⟨8754068522838665314899173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5836045681892443543266115 8754068522838665314899173)
              ·
                refine ⟨1641387848032249746543595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8754068522838665314899173 1641387848032249746543595)
                ·
                  refine ⟨2462081772048374619815393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641387848032249746543595 2462081772048374619815393)
                  ·
                    refine ⟨1846561329036280964861545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2462081772048374619815393 1846561329036280964861545)
                    ·
                      refine ⟨1384920996777210723646159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846561329036280964861545 1384920996777210723646159)
                      ·
                        rfl

theorem cell23_2697124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_2697124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697124 prefixEnd_2697124 := by exact prefixLift 2697124
  have htrace : WordTrace (prefixWord ++ tailWord_2697124) baseStart_2697124 baseEnd_2697124 := by
    simpa [prefixWord, tailWord_2697124, baseEnd_2697124] using wordTrace_append hprefix tailTrace_2697124
  have hstable : (prefixWord ++ tailWord_2697124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697124).length < 2 ^ (prefixWord ++ tailWord_2697124).sum := by decide
  have hdescent : baseEnd_2697124 < baseStart_2697124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697134 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2697134 : Nat := 118140960795 + 2697134 * 2 ^ 59
def prefixEnd_2697134 : Nat := 4983230072969 + 3 ^ 40 * 2697134 * 2
def baseEnd_2697134 : Nat := 461642043861251894840371

theorem tailTrace_2697134 : CollatzResearch.WordTrace tailWord_2697134 prefixEnd_2697134 461642043861251894840371 := by
  unfold tailWord_2697134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12296569826343953332422307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65581705740501084439585637 12296569826343953332422307)
  ·
    refine ⟨18444854739515929998633461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12296569826343953332422307 18444854739515929998633461)
    ·
      refine ⟨1729205131829618437371887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18444854739515929998633461 1729205131829618437371887)
      ·
        refine ⟨2593807697744427656057831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1729205131829618437371887 2593807697744427656057831)
        ·
          refine ⟨3890711546616641484086747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2593807697744427656057831 3890711546616641484086747)
          ·
            refine ⟨5836067319924962226130121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890711546616641484086747 5836067319924962226130121)
            ·
              refine ⟨4377050489943721669597591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5836067319924962226130121 4377050489943721669597591)
              ·
                refine ⟨6565575734915582504396387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377050489943721669597591 6565575734915582504396387)
                ·
                  refine ⟨9848363602373373756594581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6565575734915582504396387 9848363602373373756594581)
                  ·
                    refine ⟨461642043861251894840371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9848363602373373756594581 461642043861251894840371)
                    ·
                      rfl

theorem cell23_2697134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2697134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697134 prefixEnd_2697134 := by exact prefixLift 2697134
  have htrace : WordTrace (prefixWord ++ tailWord_2697134) baseStart_2697134 baseEnd_2697134 := by
    simpa [prefixWord, tailWord_2697134, baseEnd_2697134] using wordTrace_append hprefix tailTrace_2697134
  have hstable : (prefixWord ++ tailWord_2697134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697134).length < 2 ^ (prefixWord ++ tailWord_2697134).sum := by decide
  have hdescent : baseEnd_2697134 < baseStart_2697134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697173 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_2697173 : Nat := 118140960795 + 2697173 * 2 ^ 59
def prefixEnd_2697173 : Nat := 4983230072969 + 3 ^ 40 * 2697173 * 2
def baseEnd_2697173 : Nat := 461648719109760343977811

theorem tailTrace_2697173 : CollatzResearch.WordTrace tailWord_2697173 prefixEnd_2697173 461648719109760343977811 := by
  unfold tailWord_2697173
  simp only [CollatzResearch.WordTrace]
  refine ⟨98373981057610336320048173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65582654038406890880032115 98373981057610336320048173)
  ·
    refine ⟨36890242896603876120018065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98373981057610336320048173 36890242896603876120018065)
    ·
      refine ⟨27667682172452907090013549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36890242896603876120018065 27667682172452907090013549)
      ·
        refine ⟨10375380814669840158755081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27667682172452907090013549 10375380814669840158755081)
        ·
          refine ⟨7781535611002380119066311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10375380814669840158755081 7781535611002380119066311)
          ·
            refine ⟨11672303416503570178599467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7781535611002380119066311 11672303416503570178599467)
            ·
              refine ⟨17508455124755355267899201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11672303416503570178599467 17508455124755355267899201)
              ·
                refine ⟨13131341343566516450924401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17508455124755355267899201 13131341343566516450924401)
                ·
                  refine ⟨9848506007674887338193301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13131341343566516450924401 9848506007674887338193301)
                  ·
                    refine ⟨461648719109760343977811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9848506007674887338193301 461648719109760343977811)
                    ·
                      rfl

theorem cell23_2697173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_2697173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697173 prefixEnd_2697173 := by exact prefixLift 2697173
  have htrace : WordTrace (prefixWord ++ tailWord_2697173) baseStart_2697173 baseEnd_2697173 := by
    simpa [prefixWord, tailWord_2697173, baseEnd_2697173] using wordTrace_append hprefix tailTrace_2697173
  have hstable : (prefixWord ++ tailWord_2697173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697173).length < 2 ^ (prefixWord ++ tailWord_2697173).sum := by decide
  have hdescent : baseEnd_2697173 < baseStart_2697173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697174 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2697174 : Nat := 118140960795 + 2697174 * 2 ^ 59
def prefixEnd_2697174 : Nat := 4983230072969 + 3 ^ 40 * 2697174 * 2
def baseEnd_2697174 : Nat := 1384946670809935528020929

theorem tailTrace_2697174 : CollatzResearch.WordTrace tailWord_2697174 prefixEnd_2697174 1384946670809935528020929 := by
  unfold tailWord_2697174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6148376095662919593177161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65582678353737808993889717 6148376095662919593177161)
  ·
    refine ⟨4611282071747189694882871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6148376095662919593177161 4611282071747189694882871)
    ·
      refine ⟨6916923107620784542324307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4611282071747189694882871 6916923107620784542324307)
      ·
        refine ⟨10375384661431176813486461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6916923107620784542324307 10375384661431176813486461)
        ·
          refine ⟨3890769248036691305057423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10375384661431176813486461 3890769248036691305057423)
          ·
            refine ⟨5836153872055036957586135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890769248036691305057423 5836153872055036957586135)
            ·
              refine ⟨8754230808082555436379203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5836153872055036957586135 8754230808082555436379203)
              ·
                refine ⟨13131346212123833154568805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8754230808082555436379203 13131346212123833154568805)
                ·
                  refine ⟨2462127414773218716481651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13131346212123833154568805 2462127414773218716481651)
                  ·
                    refine ⟨3693191122159828074722477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2462127414773218716481651 3693191122159828074722477)
                    ·
                      refine ⟨1384946670809935528020929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3693191122159828074722477 1384946670809935528020929)
                      ·
                        rfl

theorem cell23_2697174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2697174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697174 prefixEnd_2697174 := by exact prefixLift 2697174
  have htrace : WordTrace (prefixWord ++ tailWord_2697174) baseStart_2697174 baseEnd_2697174 := by
    simpa [prefixWord, tailWord_2697174, baseEnd_2697174] using wordTrace_append hprefix tailTrace_2697174
  have hstable : (prefixWord ++ tailWord_2697174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697174).length < 2 ^ (prefixWord ++ tailWord_2697174).sum := by decide
  have hdescent : baseEnd_2697174 < baseStart_2697174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697196 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_2697196 : Nat := 118140960795 + 2697196 * 2 ^ 59
def prefixEnd_2697196 : Nat := 4983230072969 + 3 ^ 40 * 2697196 * 2
def baseEnd_2697196 : Nat := 1384957967384334441945827

theorem tailTrace_2697196 : CollatzResearch.WordTrace tailWord_2697196 prefixEnd_2697196 1384957967384334441945827 := by
  unfold tailWord_2697196
  simp only [CollatzResearch.WordTrace]
  refine ⟨49187409968263505624067721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65583213291018007498756961 49187409968263505624067721)
  ·
    refine ⟨36890557476197629218050791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49187409968263505624067721 36890557476197629218050791)
    ·
      refine ⟨55335836214296443827076187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36890557476197629218050791 55335836214296443827076187)
      ·
        refine ⟨83003754321444665740614281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55335836214296443827076187 83003754321444665740614281)
        ·
          refine ⟨62252815741083499305460711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83003754321444665740614281 62252815741083499305460711)
          ·
            refine ⟨93379223611625248958191067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62252815741083499305460711 93379223611625248958191067)
            ·
              refine ⟨140068835417437873437286601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93379223611625248958191067 140068835417437873437286601)
              ·
                refine ⟨105051626563078405077964951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140068835417437873437286601 105051626563078405077964951)
                ·
                  refine ⟨157577439844617607616947427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105051626563078405077964951 157577439844617607616947427)
                  ·
                    refine ⟨236366159766926411425421141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 157577439844617607616947427 236366159766926411425421141)
                    ·
                      refine ⟨1384957967384334441945827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 236366159766926411425421141 1384957967384334441945827)
                      ·
                        rfl

theorem cell23_2697196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2697196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697196 prefixEnd_2697196 := by exact prefixLift 2697196
  have htrace : WordTrace (prefixWord ++ tailWord_2697196) baseStart_2697196 baseEnd_2697196 := by
    simpa [prefixWord, tailWord_2697196, baseEnd_2697196] using wordTrace_append hprefix tailTrace_2697196
  have hstable : (prefixWord ++ tailWord_2697196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697196).length < 2 ^ (prefixWord ++ tailWord_2697196).sum := by decide
  have hdescent : baseEnd_2697196 < baseStart_2697196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697213 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_2697213 : Nat := 118140960795 + 2697213 * 2 ^ 59
def prefixEnd_2697213 : Nat := 4983230072969 + 3 ^ 40 * 2697213 * 2
def baseEnd_2697213 : Nat := 1384966696555460875433249

theorem tailTrace_2697213 : CollatzResearch.WordTrace tailWord_2697213 prefixEnd_2697213 1384966696555460875433249 := by
  unfold tailWord_2697213
  simp only [CollatzResearch.WordTrace]
  refine ⟨98375439977465423151504293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65583626651643615434336195 98375439977465423151504293)
  ·
    refine ⟨18445394995774766840907055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98375439977465423151504293 18445394995774766840907055)
    ·
      refine ⟨27668092493662150261360583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18445394995774766840907055 27668092493662150261360583)
      ·
        refine ⟨41502138740493225392040875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27668092493662150261360583 41502138740493225392040875)
        ·
          refine ⟨62253208110739838088061313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41502138740493225392040875 62253208110739838088061313)
          ·
            refine ⟨46689906083054878566045985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62253208110739838088061313 46689906083054878566045985)
            ·
              refine ⟨35017429562291158924534489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46689906083054878566045985 35017429562291158924534489)
              ·
                refine ⟨26263072171718369193400867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35017429562291158924534489 26263072171718369193400867)
                ·
                  refine ⟨39394608257577553790101301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26263072171718369193400867 39394608257577553790101301)
                  ·
                    refine ⟨3693244524147895667821997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39394608257577553790101301 3693244524147895667821997)
                    ·
                      refine ⟨1384966696555460875433249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3693244524147895667821997 1384966696555460875433249)
                      ·
                        rfl

theorem cell23_2697213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_2697213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697213 prefixEnd_2697213 := by exact prefixLift 2697213
  have htrace : WordTrace (prefixWord ++ tailWord_2697213) baseStart_2697213 baseEnd_2697213 := by
    simpa [prefixWord, tailWord_2697213, baseEnd_2697213] using wordTrace_append hprefix tailTrace_2697213
  have hstable : (prefixWord ++ tailWord_2697213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697213).length < 2 ^ (prefixWord ++ tailWord_2697213).sum := by decide
  have hdescent : baseEnd_2697213 < baseStart_2697213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697214 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2697214 : Nat := 118140960795 + 2697214 * 2 ^ 59
def prefixEnd_2697214 : Nat := 4983230072969 + 3 ^ 40 * 2697214 * 2
def baseEnd_2697214 : Nat := 1384967210036115371520745

theorem tailTrace_2697214 : CollatzResearch.WordTrace tailWord_2697214 prefixEnd_2697214 1384967210036115371520745 := by
  unfold tailWord_2697214
  simp only [CollatzResearch.WordTrace]
  refine ⟨12296934556307725040286337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65583650966974533548193797 12296934556307725040286337)
  ·
    refine ⟨9222700917230793780214753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12296934556307725040286337 9222700917230793780214753)
    ·
      refine ⟨6917025687923095335161065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9222700917230793780214753 6917025687923095335161065)
      ·
        refine ⟨5187769265942321501370799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6917025687923095335161065 5187769265942321501370799)
        ·
          refine ⟨7781653898913482252056199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5187769265942321501370799 7781653898913482252056199)
          ·
            refine ⟨11672480848370223378084299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7781653898913482252056199 11672480848370223378084299)
            ·
              refine ⟨17508721272555335067126449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11672480848370223378084299 17508721272555335067126449)
              ·
                refine ⟨13131540954416501300344837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17508721272555335067126449 13131540954416501300344837)
                ·
                  refine ⟨2462163928953093993814657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13131540954416501300344837 2462163928953093993814657)
                  ·
                    refine ⟨1846622946714820495360993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2462163928953093993814657 1846622946714820495360993)
                    ·
                      refine ⟨1384967210036115371520745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846622946714820495360993 1384967210036115371520745)
                      ·
                        rfl

theorem cell23_2697214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2697214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697214 prefixEnd_2697214 := by exact prefixLift 2697214
  have htrace : WordTrace (prefixWord ++ tailWord_2697214) baseStart_2697214 baseEnd_2697214 := by
    simpa [prefixWord, tailWord_2697214, baseEnd_2697214] using wordTrace_append hprefix tailTrace_2697214
  have hstable : (prefixWord ++ tailWord_2697214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697214).length < 2 ^ (prefixWord ++ tailWord_2697214).sum := by decide
  have hdescent : baseEnd_2697214 < baseStart_2697214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697237 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 7]
def baseStart_2697237 : Nat := 118140960795 + 2697237 * 2 ^ 59
def prefixEnd_2697237 : Nat := 4983230072969 + 3 ^ 40 * 2697237 * 2
def baseEnd_2697237 : Nat := 153886557787907642392571

theorem tailTrace_2697237 : CollatzResearch.WordTrace tailWord_2697237 prefixEnd_2697237 153886557787907642392571 := by
  unfold tailWord_2697237
  simp only [CollatzResearch.WordTrace]
  refine ⟨98376315329378475250377965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65584210219585650166918643 98376315329378475250377965)
  ·
    refine ⟨36891118248516928218891737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98376315329378475250377965 36891118248516928218891737)
    ·
      refine ⟨27668338686387696164168803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36891118248516928218891737 27668338686387696164168803)
      ·
        refine ⟨41502508029581544246253205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27668338686387696164168803 41502508029581544246253205)
        ·
          refine ⟨1945430063886634886543119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41502508029581544246253205 1945430063886634886543119)
          ·
            refine ⟨2918145095829952329814679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1945430063886634886543119 2918145095829952329814679)
            ·
              refine ⟨4377217643744928494722019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2918145095829952329814679 4377217643744928494722019)
              ·
                refine ⟨6565826465617392742083029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377217643744928494722019 6565826465617392742083029)
                ·
                  refine ⟨153886557787907642392571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6565826465617392742083029 153886557787907642392571)
                  ·
                    rfl

theorem cell23_2697237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_2697237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697237 prefixEnd_2697237 := by exact prefixLift 2697237
  have htrace : WordTrace (prefixWord ++ tailWord_2697237) baseStart_2697237 baseEnd_2697237 := by
    simpa [prefixWord, tailWord_2697237, baseEnd_2697237] using wordTrace_append hprefix tailTrace_2697237
  have hstable : (prefixWord ++ tailWord_2697237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697237).length < 2 ^ (prefixWord ++ tailWord_2697237).sum := by decide
  have hdescent : baseEnd_2697237 < baseStart_2697237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697240 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 2, 5, 2]
def baseStart_2697240 : Nat := 118140960795 + 2697240 * 2 ^ 59
def prefixEnd_2697240 : Nat := 4983230072969 + 3 ^ 40 * 2697240 * 2
def baseEnd_2697240 : Nat := 1384980560533132269795625

theorem tailTrace_2697240 : CollatzResearch.WordTrace tailWord_2697240 prefixEnd_2697240 1384980560533132269795625 := by
  unfold tailWord_2697240
  simp only [CollatzResearch.WordTrace]
  refine ⟨49188212374183803381368587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65584283165578404508491449 49188212374183803381368587)
  ·
    refine ⟨73782318561275705072052881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49188212374183803381368587 73782318561275705072052881)
    ·
      refine ⟨55336738920956778804039661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73782318561275705072052881 55336738920956778804039661)
      ·
        refine ⟨20751277095358792051514873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55336738920956778804039661 20751277095358792051514873)
        ·
          refine ⟨15563457821519094038636155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20751277095358792051514873 15563457821519094038636155)
          ·
            refine ⟨23345186732278641057954233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15563457821519094038636155 23345186732278641057954233)
            ·
              refine ⟨17508890049208980793465675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23345186732278641057954233 17508890049208980793465675)
              ·
                refine ⟨26263335073813471190198513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17508890049208980793465675 26263335073813471190198513)
                ·
                  refine ⟨19697501305360103392648885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26263335073813471190198513 19697501305360103392648885)
                  ·
                    refine ⟨1846640747377509693060833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19697501305360103392648885 1846640747377509693060833)
                    ·
                      refine ⟨1384980560533132269795625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846640747377509693060833 1384980560533132269795625)
                      ·
                        rfl

theorem cell23_2697240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_2697240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697240 prefixEnd_2697240 := by exact prefixLift 2697240
  have htrace : WordTrace (prefixWord ++ tailWord_2697240) baseStart_2697240 baseEnd_2697240 := by
    simpa [prefixWord, tailWord_2697240, baseEnd_2697240] using wordTrace_append hprefix tailTrace_2697240
  have hstable : (prefixWord ++ tailWord_2697240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697240).length < 2 ^ (prefixWord ++ tailWord_2697240).sum := by decide
  have hdescent : baseEnd_2697240 < baseStart_2697240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697314 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_2697314 : Nat := 118140960795 + 2697314 * 2 ^ 59
def prefixEnd_2697314 : Nat := 4983230072969 + 3 ^ 40 * 2697314 * 2
def baseEnd_2697314 : Nat := 461672852700521660090095

theorem tailTrace_2697314 : CollatzResearch.WordTrace tailWord_2697314 prefixEnd_2697314 461672852700521660090095 := by
  unfold tailWord_2697314
  simp only [CollatzResearch.WordTrace]
  refine ⟨24594780937524879350232749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65586082500066344933953997 24594780937524879350232749)
  ·
    refine ⟨9223042851571829756337281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24594780937524879350232749 9223042851571829756337281)
    ·
      refine ⟨6917282138678872317252961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9223042851571829756337281 6917282138678872317252961)
      ·
        refine ⟨5187961604009154237939721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6917282138678872317252961 5187961604009154237939721)
        ·
          refine ⟨3890971203006865678454791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5187961604009154237939721 3890971203006865678454791)
          ·
            refine ⟨5836456804510298517682187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890971203006865678454791 5836456804510298517682187)
            ·
              refine ⟨8754685206765447776523281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5836456804510298517682187 8754685206765447776523281)
              ·
                refine ⟨6566013905074085832392461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8754685206765447776523281 6566013905074085832392461)
                ·
                  refine ⟨2462255214402782187147173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6566013905074085832392461 2462255214402782187147173)
                  ·
                    refine ⟨461672852700521660090095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2462255214402782187147173 461672852700521660090095)
                    ·
                      rfl

theorem cell23_2697314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_2697314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697314 prefixEnd_2697314 := by exact prefixLift 2697314
  have htrace : WordTrace (prefixWord ++ tailWord_2697314) baseStart_2697314 baseEnd_2697314 := by
    simpa [prefixWord, tailWord_2697314, baseEnd_2697314] using wordTrace_append hprefix tailTrace_2697314
  have hstable : (prefixWord ++ tailWord_2697314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697314).length < 2 ^ (prefixWord ++ tailWord_2697314).sum := by decide
  have hdescent : baseEnd_2697314 < baseStart_2697314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697354 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_2697354 : Nat := 118140960795 + 2697354 * 2 ^ 59
def prefixEnd_2697354 : Nat := 4983230072969 + 3 ^ 40 * 2697354 * 2
def baseEnd_2697354 : Nat := 1385039097327744823770101

theorem tailTrace_2697354 : CollatzResearch.WordTrace tailWord_2697354 prefixEnd_2697354 1385039097327744823770101 := by
  unfold tailWord_2697354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24595145667488651058096779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65587055113303069488258077 24595145667488651058096779)
  ·
    refine ⟨36892718501232976587145169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24595145667488651058096779 36892718501232976587145169)
    ·
      refine ⟨27669538875924732440358877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36892718501232976587145169 27669538875924732440358877)
      ·
        refine ⟨10376077078471774665134579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27669538875924732440358877 10376077078471774665134579)
        ·
          refine ⟨15564115617707661997701869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10376077078471774665134579 15564115617707661997701869)
          ·
            refine ⟨5836543356640373249138201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15564115617707661997701869 5836543356640373249138201)
            ·
              refine ⟨4377407517480279936853651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5836543356640373249138201 4377407517480279936853651)
              ·
                refine ⟨6566111276220419905280477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377407517480279936853651 6566111276220419905280477)
                ·
                  refine ⟨2462291728582657464480179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6566111276220419905280477 2462291728582657464480179)
                  ·
                    refine ⟨3693437592873986196720269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2462291728582657464480179 3693437592873986196720269)
                    ·
                      refine ⟨1385039097327744823770101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3693437592873986196720269 1385039097327744823770101)
                      ·
                        rfl

theorem cell23_2697354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_2697354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697354 prefixEnd_2697354 := by exact prefixLift 2697354
  have htrace : WordTrace (prefixWord ++ tailWord_2697354) baseStart_2697354 baseEnd_2697354 := by
    simpa [prefixWord, tailWord_2697354, baseEnd_2697354] using wordTrace_append hprefix tailTrace_2697354
  have hstable : (prefixWord ++ tailWord_2697354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697354).length < 2 ^ (prefixWord ++ tailWord_2697354).sum := by decide
  have hdescent : baseEnd_2697354 < baseStart_2697354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697377 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2697377 : Nat := 118140960795 + 2697377 * 2 ^ 59
def prefixEnd_2697377 : Nat := 4983230072969 + 3 ^ 40 * 2697377 * 2
def baseEnd_2697377 : Nat := 1385050907382798233782495

theorem tailTrace_2697377 : CollatzResearch.WordTrace tailWord_2697377 prefixEnd_2697377 1385050907382798233782495 := by
  unfold tailWord_2697377
  simp only [CollatzResearch.WordTrace]
  refine ⟨98381421548871279160474385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65587614365914186106982923 98381421548871279160474385)
  ·
    refine ⟨73786066161653459370355789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98381421548871279160474385 73786066161653459370355789)
    ·
      refine ⟨27669774810620047263883421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73786066161653459370355789 27669774810620047263883421)
      ·
        refine ⟨10376165553982517723956283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27669774810620047263883421 10376165553982517723956283)
        ·
          refine ⟨15564248330973776585934425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10376165553982517723956283 15564248330973776585934425)
          ·
            refine ⟨11673186248230332439450819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15564248330973776585934425 11673186248230332439450819)
            ·
              refine ⟨17509779372345498659176229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11673186248230332439450819 17509779372345498659176229)
              ·
                refine ⟨3283083632314780998595543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17509779372345498659176229 3283083632314780998595543)
                ·
                  refine ⟨4924625448472171497893315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283083632314780998595543 4924625448472171497893315)
                  ·
                    refine ⟨7386938172708257246839973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4924625448472171497893315 7386938172708257246839973)
                    ·
                      refine ⟨1385050907382798233782495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7386938172708257246839973 1385050907382798233782495)
                      ·
                        rfl

theorem cell23_2697377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2697377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697377 prefixEnd_2697377 := by exact prefixLift 2697377
  have htrace : WordTrace (prefixWord ++ tailWord_2697377) baseStart_2697377 baseEnd_2697377 := by
    simpa [prefixWord, tailWord_2697377, baseEnd_2697377] using wordTrace_append hprefix tailTrace_2697377
  have hstable : (prefixWord ++ tailWord_2697377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697377).length < 2 ^ (prefixWord ++ tailWord_2697377).sum := by decide
  have hdescent : baseEnd_2697377 < baseStart_2697377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697484 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 1, 4, 2]
def baseStart_2697484 : Nat := 118140960795 + 2697484 * 2 ^ 59
def prefixEnd_2697484 : Nat := 4983230072969 + 3 ^ 40 * 2697484 * 2
def baseEnd_2697484 : Nat := 1385105849812829315144503

theorem tailTrace_2697484 : CollatzResearch.WordTrace tailWord_2697484 prefixEnd_2697484 1385105849812829315144503 := by
  unfold tailWord_2697484
  simp only [CollatzResearch.WordTrace]
  refine ⟨49192662079741818217309753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65590216106322424289746337 49192662079741818217309753)
  ·
    refine ⟨36894496559806363662982315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49192662079741818217309753 36894496559806363662982315)
    ·
      refine ⟨55341744839709545494473473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36894496559806363662982315 55341744839709545494473473)
      ·
        refine ⟨41506308629782159120855105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55341744839709545494473473 41506308629782159120855105)
        ·
          refine ⟨31129731472336619340641329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41506308629782159120855105 31129731472336619340641329)
          ·
            refine ⟨23347298604252464505480997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31129731472336619340641329 23347298604252464505480997)
            ·
              refine ⟨4377618488297337094777687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23347298604252464505480997 4377618488297337094777687)
              ·
                refine ⟨6566427732446005642166531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377618488297337094777687 6566427732446005642166531)
                ·
                  refine ⟨9849641598669008463249797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566427732446005642166531 9849641598669008463249797)
                  ·
                    refine ⟨1846807799750439086859337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9849641598669008463249797 1846807799750439086859337)
                    ·
                      refine ⟨1385105849812829315144503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846807799750439086859337 1385105849812829315144503)
                      ·
                        rfl

theorem cell23_2697484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_2697484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697484 prefixEnd_2697484 := by exact prefixLift 2697484
  have htrace : WordTrace (prefixWord ++ tailWord_2697484) baseStart_2697484 baseEnd_2697484 := by
    simpa [prefixWord, tailWord_2697484, baseEnd_2697484] using wordTrace_append hprefix tailTrace_2697484
  have hstable : (prefixWord ++ tailWord_2697484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697484).length < 2 ^ (prefixWord ++ tailWord_2697484).sum := by decide
  have hdescent : baseEnd_2697484 < baseStart_2697484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697500 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2697500 : Nat := 118140960795 + 2697500 * 2 ^ 59
def prefixEnd_2697500 : Nat := 4983230072969 + 3 ^ 40 * 2697500 * 2
def baseEnd_2697500 : Nat := 1385114065503301252544429

theorem tailTrace_2697500 : CollatzResearch.WordTrace tailWord_2697500 prefixEnd_2697500 1385114065503301252544429 := by
  unfold tailWord_2697500
  simp only [CollatzResearch.WordTrace]
  refine ⟨49192953863712835583600977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65590605151617114111467969 49192953863712835583600977)
  ·
    refine ⟨36894715397784626687700733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49192953863712835583600977 36894715397784626687700733)
    ·
      refine ⟨13835518274169235007887775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36894715397784626687700733 13835518274169235007887775)
      ·
        refine ⟨20753277411253852511831663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13835518274169235007887775 20753277411253852511831663)
        ·
          refine ⟨31129916116880778767747495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20753277411253852511831663 31129916116880778767747495)
          ·
            refine ⟨46694874175321168151621243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31129916116880778767747495 46694874175321168151621243)
            ·
              refine ⟨70042311262981752227431865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46694874175321168151621243 70042311262981752227431865)
              ·
                refine ⟨52531733447236314170573899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70042311262981752227431865 52531733447236314170573899)
                ·
                  refine ⟨78797600170854471255860849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52531733447236314170573899 78797600170854471255860849)
                  ·
                    refine ⟨59098200128140853441895637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78797600170854471255860849 59098200128140853441895637)
                    ·
                      refine ⟨1385114065503301252544429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59098200128140853441895637 1385114065503301252544429)
                      ·
                        rfl

theorem cell23_2697500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2697500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697500 prefixEnd_2697500 := by exact prefixLift 2697500
  have htrace : WordTrace (prefixWord ++ tailWord_2697500) baseStart_2697500 baseEnd_2697500 := by
    simpa [prefixWord, tailWord_2697500, baseEnd_2697500] using wordTrace_append hprefix tailTrace_2697500
  have hstable : (prefixWord ++ tailWord_2697500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697500).length < 2 ^ (prefixWord ++ tailWord_2697500).sum := by decide
  have hdescent : baseEnd_2697500 < baseStart_2697500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697524 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2697524 : Nat := 118140960795 + 2697524 * 2 ^ 59
def prefixEnd_2697524 : Nat := 4983230072969 + 3 ^ 40 * 2697524 * 2
def baseEnd_2697524 : Nat := 153902932115445462071591

theorem tailTrace_2697524 : CollatzResearch.WordTrace tailWord_2697524 prefixEnd_2697524 153902932115445462071591 := by
  unfold tailWord_2697524
  simp only [CollatzResearch.WordTrace]
  refine ⟨49193391539669361633037813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65591188719559148844050417 49193391539669361633037813)
  ·
    refine ⟨4611880456844002653097295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49193391539669361633037813 4611880456844002653097295)
    ·
      refine ⟨6917820685266003979645943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4611880456844002653097295 6917820685266003979645943)
      ·
        refine ⟨10376731027899005969468915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6917820685266003979645943 10376731027899005969468915)
        ·
          refine ⟨15565096541848508954203373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10376731027899005969468915 15565096541848508954203373)
          ·
            refine ⟨5836911203193190857826265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15565096541848508954203373 5836911203193190857826265)
            ·
              refine ⟨4377683402394893143369699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5836911203193190857826265 4377683402394893143369699)
              ·
                refine ⟨6566525103592339715054549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377683402394893143369699 6566525103592339715054549)
                ·
                  refine ⟨153902932115445462071591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6566525103592339715054549 153902932115445462071591)
                  ·
                    rfl

theorem cell23_2697524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2697524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697524 prefixEnd_2697524 := by exact prefixLift 2697524
  have htrace : WordTrace (prefixWord ++ tailWord_2697524) baseStart_2697524 baseEnd_2697524 := by
    simpa [prefixWord, tailWord_2697524, baseEnd_2697524] using wordTrace_append hprefix tailTrace_2697524
  have hstable : (prefixWord ++ tailWord_2697524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697524).length < 2 ^ (prefixWord ++ tailWord_2697524).sum := by decide
  have hdescent : baseEnd_2697524 < baseStart_2697524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697527 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 1, 7, 2]
def baseStart_2697527 : Nat := 118140960795 + 2697527 * 2 ^ 59
def prefixEnd_2697527 : Nat := 4983230072969 + 3 ^ 40 * 2697527 * 2
def baseEnd_2697527 : Nat := 1385127929480972646906805

theorem tailTrace_2697527 : CollatzResearch.WordTrace tailWord_2697527 prefixEnd_2697527 1385127929480972646906805 := by
  unfold tailWord_2697527
  simp only [CollatzResearch.WordTrace]
  refine ⟨98386892498327854778434835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65591261665551903185623223 98386892498327854778434835)
  ·
    refine ⟨147580338747491782167652253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98386892498327854778434835 147580338747491782167652253)
    ·
      refine ⟨55342627030309418312869595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147580338747491782167652253 55342627030309418312869595)
      ·
        refine ⟨83013940545464127469304393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55342627030309418312869595 83013940545464127469304393)
        ·
          refine ⟨62260455409098095601978295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83013940545464127469304393 62260455409098095601978295)
          ·
            refine ⟨93390683113647143402967443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62260455409098095601978295 93390683113647143402967443)
            ·
              refine ⟨140086024670470715104451165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93390683113647143402967443 140086024670470715104451165)
              ·
                refine ⟨52532259251426518164169187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140086024670470715104451165 52532259251426518164169187)
                ·
                  refine ⟨78798388877139777246253781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52532259251426518164169187 78798388877139777246253781)
                  ·
                    refine ⟨1846837239307963529209073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 78798388877139777246253781 1846837239307963529209073)
                    ·
                      refine ⟨1385127929480972646906805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846837239307963529209073 1385127929480972646906805)
                      ·
                        rfl

theorem cell23_2697527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_2697527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697527 prefixEnd_2697527 := by exact prefixLift 2697527
  have htrace : WordTrace (prefixWord ++ tailWord_2697527) baseStart_2697527 baseEnd_2697527 := by
    simpa [prefixWord, tailWord_2697527, baseEnd_2697527] using wordTrace_append hprefix tailTrace_2697527
  have hstable : (prefixWord ++ tailWord_2697527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697527).length < 2 ^ (prefixWord ++ tailWord_2697527).sum := by decide
  have hdescent : baseEnd_2697527 < baseStart_2697527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697534 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2697534 : Nat := 118140960795 + 2697534 * 2 ^ 59
def prefixEnd_2697534 : Nat := 4983230072969 + 3 ^ 40 * 2697534 * 2
def baseEnd_2697534 : Nat := 1385131523845554119519273

theorem tailTrace_2697534 : CollatzResearch.WordTrace tailWord_2697534 prefixEnd_2697534 1385131523845554119519273 := by
  unfold tailWord_2697534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12298393476162811871742457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65591431872868329982626437 12298393476162811871742457)
  ·
    refine ⟨9223795107122108903806843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12298393476162811871742457 9223795107122108903806843)
    ·
      refine ⟨13835692660683163355710265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9223795107122108903806843 13835692660683163355710265)
      ·
        refine ⟨10376769495512372516782699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13835692660683163355710265 10376769495512372516782699)
        ·
          refine ⟨15565154243268558775174049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10376769495512372516782699 15565154243268558775174049)
          ·
            refine ⟨11673865682451419081380537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15565154243268558775174049 11673865682451419081380537)
            ·
              refine ⟨8755399261838564311035403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11673865682451419081380537 8755399261838564311035403)
              ·
                refine ⟨13133098892757846466553105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8755399261838564311035403 13133098892757846466553105)
                ·
                  refine ⟨9849824169568384849914829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13133098892757846466553105 9849824169568384849914829)
                  ·
                    refine ⟨3693684063588144318718061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9849824169568384849914829 3693684063588144318718061)
                    ·
                      refine ⟨1385131523845554119519273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3693684063588144318718061 1385131523845554119519273)
                      ·
                        rfl

theorem cell23_2697534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2697534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697534 prefixEnd_2697534 := by exact prefixLift 2697534
  have htrace : WordTrace (prefixWord ++ tailWord_2697534) baseStart_2697534 baseEnd_2697534 := by
    simpa [prefixWord, tailWord_2697534, baseEnd_2697534] using wordTrace_append hprefix tailTrace_2697534
  have hstable : (prefixWord ++ tailWord_2697534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697534).length < 2 ^ (prefixWord ++ tailWord_2697534).sum := by decide
  have hdescent : baseEnd_2697534 < baseStart_2697534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697567 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 5, 4]
def baseStart_2697567 : Nat := 118140960795 + 2697567 * 2 ^ 59
def prefixEnd_2697567 : Nat := 4983230072969 + 3 ^ 40 * 2697567 * 2
def baseEnd_2697567 : Nat := 461716156235717496802207

theorem tailTrace_2697567 : CollatzResearch.WordTrace tailWord_2697567 prefixEnd_2697567 461716156235717496802207 := by
  unfold tailWord_2697567
  simp only [CollatzResearch.WordTrace]
  refine ⟨98388351418182941609890955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65592234278788627739927303 98388351418182941609890955)
  ·
    refine ⟨147582527127274412414836433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98388351418182941609890955 147582527127274412414836433)
    ·
      refine ⟨110686895345455809311127325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147582527127274412414836433 110686895345455809311127325)
      ·
        refine ⟨41507585754545928491672747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110686895345455809311127325 41507585754545928491672747)
        ·
          refine ⟨62261378631818892737509121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41507585754545928491672747 62261378631818892737509121)
          ·
            refine ⟨46696033973864169553131841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62261378631818892737509121 46696033973864169553131841)
            ·
              refine ⟨35022025480398127164848881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46696033973864169553131841 35022025480398127164848881)
              ·
                refine ⟨26266519110298595373636661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35022025480398127164848881 26266519110298595373636661)
                ·
                  refine ⟨2462486166590493316278437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26266519110298595373636661 2462486166590493316278437)
                  ·
                    refine ⟨461716156235717496802207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2462486166590493316278437 461716156235717496802207)
                    ·
                      rfl

theorem cell23_2697567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 4].length) (baseStart_2697567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697567 prefixEnd_2697567 := by exact prefixLift 2697567
  have htrace : WordTrace (prefixWord ++ tailWord_2697567) baseStart_2697567 baseEnd_2697567 := by
    simpa [prefixWord, tailWord_2697567, baseEnd_2697567] using wordTrace_append hprefix tailTrace_2697567
  have hstable : (prefixWord ++ tailWord_2697567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697567).length < 2 ^ (prefixWord ++ tailWord_2697567).sum := by decide
  have hdescent : baseEnd_2697567 < baseStart_2697567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697584 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 3, 4]
def baseStart_2697584 : Nat := 118140960795 + 2697584 * 2 ^ 59
def prefixEnd_2697584 : Nat := 4983230072969 + 3 ^ 40 * 2697584 * 2
def baseEnd_2697584 : Nat := 461719065959426307964681

theorem tailTrace_2697584 : CollatzResearch.WordTrace tailWord_2697584 prefixEnd_2697584 461719065959426307964681 := by
  unfold tailWord_2697584
  simp only [CollatzResearch.WordTrace]
  refine ⟨49194485729560676756629903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65592647639414235675506537 49194485729560676756629903)
  ·
    refine ⟨73791728594341015134944855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49194485729560676756629903 73791728594341015134944855)
    ·
      refine ⟨110687592891511522702417283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73791728594341015134944855 110687592891511522702417283)
      ·
        refine ⟨166031389337267284053625925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110687592891511522702417283 166031389337267284053625925)
        ·
          refine ⟨31130885500737615760054861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166031389337267284053625925 31130885500737615760054861)
          ·
            refine ⟨11674082062776605910020573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31130885500737615760054861 11674082062776605910020573)
            ·
              refine ⟨4377780773541227216257715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11674082062776605910020573 4377780773541227216257715)
              ·
                refine ⟨6566671160311840824386573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377780773541227216257715 6566671160311840824386573)
                ·
                  refine ⟨2462501685116940309144965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6566671160311840824386573 2462501685116940309144965)
                  ·
                    refine ⟨461719065959426307964681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2462501685116940309144965 461719065959426307964681)
                    ·
                      rfl

theorem cell23_2697584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3, 4].length) (baseStart_2697584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697584 prefixEnd_2697584 := by exact prefixLift 2697584
  have htrace : WordTrace (prefixWord ++ tailWord_2697584) baseStart_2697584 baseEnd_2697584 := by
    simpa [prefixWord, tailWord_2697584, baseEnd_2697584] using wordTrace_append hprefix tailTrace_2697584
  have hstable : (prefixWord ++ tailWord_2697584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697584).length < 2 ^ (prefixWord ++ tailWord_2697584).sum := by decide
  have hdescent : baseEnd_2697584 < baseStart_2697584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697664 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 4]
def baseStart_2697664 : Nat := 118140960795 + 2697664 * 2 ^ 59
def prefixEnd_2697664 : Nat := 4983230072969 + 3 ^ 40 * 2697664 * 2
def baseEnd_2697664 : Nat := 1385198276330638610893675

theorem tailTrace_2697664 : CollatzResearch.WordTrace tailWord_2697664 prefixEnd_2697664 1385198276330638610893675 := by
  unfold tailWord_2697664
  simp only [CollatzResearch.WordTrace]
  refine ⟨49195944649415763588086023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65594592865887684784114697 49195944649415763588086023)
  ·
    refine ⟨73793916974123645382129035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49195944649415763588086023 73793916974123645382129035)
    ·
      refine ⟨110690875461185468073193553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73793916974123645382129035 110690875461185468073193553)
      ·
        refine ⟨83018156595889101054895165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110690875461185468073193553 83018156595889101054895165)
        ·
          refine ⟨31131808723458412895585687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83018156595889101054895165 31131808723458412895585687)
          ·
            refine ⟨46697713085187619343378531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31131808723458412895585687 46697713085187619343378531)
            ·
              refine ⟨70046569627781429015067797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46697713085187619343378531 70046569627781429015067797)
              ·
                refine ⟨3283432951302254485081303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70046569627781429015067797 3283432951302254485081303)
                ·
                  refine ⟨4925149426953381727621955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283432951302254485081303 4925149426953381727621955)
                  ·
                    refine ⟨7387724140430072591432933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4925149426953381727621955 7387724140430072591432933)
                    ·
                      refine ⟨1385198276330638610893675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7387724140430072591432933 1385198276330638610893675)
                      ·
                        rfl

theorem cell23_2697664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_2697664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697664 prefixEnd_2697664 := by exact prefixLift 2697664
  have htrace : WordTrace (prefixWord ++ tailWord_2697664) baseStart_2697664 baseEnd_2697664 := by
    simpa [prefixWord, tailWord_2697664, baseEnd_2697664] using wordTrace_append hprefix tailTrace_2697664
  have hstable : (prefixWord ++ tailWord_2697664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697664).length < 2 ^ (prefixWord ++ tailWord_2697664).sum := by decide
  have hdescent : baseEnd_2697664 < baseStart_2697664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697668 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_2697668 : Nat := 118140960795 + 2697668 * 2 ^ 59
def prefixEnd_2697668 : Nat := 4983230072969 + 3 ^ 40 * 2697668 * 2
def baseEnd_2697668 : Nat := 1385200330253256595243657

theorem tailTrace_2697668 : CollatzResearch.WordTrace tailWord_2697668 prefixEnd_2697668 1385200330253256595243657 := by
  unfold tailWord_2697668
  simp only [CollatzResearch.WordTrace]
  refine ⟨49196017595408517929658829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65594690127211357239545105 49196017595408517929658829)
  ·
    refine ⟨18448506598278194223622061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49196017595408517929658829 18448506598278194223622061)
    ·
      refine ⟨6918189974354322833858273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18448506598278194223622061 6918189974354322833858273)
      ·
        refine ⟨5188642480765742125393705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6918189974354322833858273 5188642480765742125393705)
        ·
          refine ⟨3891481860574306594045279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5188642480765742125393705 3891481860574306594045279)
          ·
            refine ⟨5837222790861459891067919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891481860574306594045279 5837222790861459891067919)
            ·
              refine ⟨8755834186292189836601879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837222790861459891067919 8755834186292189836601879)
              ·
                refine ⟨13133751279438284754902819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8755834186292189836601879 13133751279438284754902819)
                ·
                  refine ⟨19700626919157427132354229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13133751279438284754902819 19700626919157427132354229)
                  ·
                    refine ⟨1846933773671008793658209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19700626919157427132354229 1846933773671008793658209)
                    ·
                      refine ⟨1385200330253256595243657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846933773671008793658209 1385200330253256595243657)
                      ·
                        rfl

theorem cell23_2697668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_2697668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697668 prefixEnd_2697668 := by exact prefixLift 2697668
  have htrace : WordTrace (prefixWord ++ tailWord_2697668) baseStart_2697668 baseEnd_2697668 := by
    simpa [prefixWord, tailWord_2697668, baseEnd_2697668] using wordTrace_append hprefix tailTrace_2697668
  have hstable : (prefixWord ++ tailWord_2697668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697668).length < 2 ^ (prefixWord ++ tailWord_2697668).sum := by decide
  have hdescent : baseEnd_2697668 < baseStart_2697668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697674 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_2697674 : Nat := 118140960795 + 2697674 * 2 ^ 59
def prefixEnd_2697674 : Nat := 4983230072969 + 3 ^ 40 * 2697674 * 2
def baseEnd_2697674 : Nat := 461734470379061190589543

theorem tailTrace_2697674 : CollatzResearch.WordTrace tailWord_2697674 prefixEnd_2697674 461734470379061190589543 := by
  unfold tailWord_2697674
  simp only [CollatzResearch.WordTrace]
  refine ⟨24598063507198824721009019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65594836019196865922690717 24598063507198824721009019)
  ·
    refine ⟨36897095260798237081513529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24598063507198824721009019 36897095260798237081513529)
    ·
      refine ⟨27672821445598677811135147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36897095260798237081513529 27672821445598677811135147)
      ·
        refine ⟨41509232168398016716702721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27672821445598677811135147 41509232168398016716702721)
        ·
          refine ⟨31131924126298512537527041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41509232168398016716702721 31131924126298512537527041)
          ·
            refine ⟨23348943094723884403145281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31131924126298512537527041 23348943094723884403145281)
            ·
              refine ⟨17511707321042913302358961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23348943094723884403145281 17511707321042913302358961)
              ·
                refine ⟨13133780490782184976769221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17511707321042913302358961 13133780490782184976769221)
                ·
                  refine ⟨2462583842021659683144229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13133780490782184976769221 2462583842021659683144229)
                  ·
                    refine ⟨461734470379061190589543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2462583842021659683144229 461734470379061190589543)
                    ·
                      rfl

theorem cell23_2697674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_2697674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697674 prefixEnd_2697674 := by exact prefixLift 2697674
  have htrace : WordTrace (prefixWord ++ tailWord_2697674) baseStart_2697674 baseEnd_2697674 := by
    simpa [prefixWord, tailWord_2697674, baseEnd_2697674] using wordTrace_append hprefix tailTrace_2697674
  have hstable : (prefixWord ++ tailWord_2697674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697674).length < 2 ^ (prefixWord ++ tailWord_2697674).sum := by decide
  have hdescent : baseEnd_2697674 < baseStart_2697674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697701 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2697701 : Nat := 118140960795 + 2697701 * 2 ^ 59
def prefixEnd_2697701 : Nat := 4983230072969 + 3 ^ 40 * 2697701 * 2
def baseEnd_2697701 : Nat := 1385217275114854966131005

theorem tailTrace_2697701 : CollatzResearch.WordTrace tailWord_2697701 prefixEnd_2697701 1385217275114854966131005 := by
  unfold tailWord_2697701
  simp only [CollatzResearch.WordTrace]
  refine ⟨98393238799697482495268957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65595492533131654996845971 98393238799697482495268957)
  ·
    refine ⟨36897464549886555935725859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98393238799697482495268957 36897464549886555935725859)
    ·
      refine ⟨55346196824829833903588789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36897464549886555935725859 55346196824829833903588789)
      ·
        refine ⟨5188705952327796928461449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55346196824829833903588789 5188705952327796928461449)
        ·
          refine ⟨3891529464245847696346087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5188705952327796928461449 3891529464245847696346087)
          ·
            refine ⟨5837294196368771544519131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891529464245847696346087 5837294196368771544519131)
            ·
              refine ⟨8755941294553157316778697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837294196368771544519131 8755941294553157316778697)
              ·
                refine ⟨6566955970914867987584023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8755941294553157316778697 6566955970914867987584023)
                ·
                  refine ⟨9850433956372301981376035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566955970914867987584023 9850433956372301981376035)
                  ·
                    refine ⟨14775650934558452972064053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9850433956372301981376035 14775650934558452972064053)
                    ·
                      refine ⟨1385217275114854966131005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14775650934558452972064053 1385217275114854966131005)
                      ·
                        rfl

theorem cell23_2697701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2697701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697701 prefixEnd_2697701 := by exact prefixLift 2697701
  have htrace : WordTrace (prefixWord ++ tailWord_2697701) baseStart_2697701 baseEnd_2697701 := by
    simpa [prefixWord, tailWord_2697701, baseEnd_2697701] using wordTrace_append hprefix tailTrace_2697701
  have hstable : (prefixWord ++ tailWord_2697701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697701).length < 2 ^ (prefixWord ++ tailWord_2697701).sum := by decide
  have hdescent : baseEnd_2697701 < baseStart_2697701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697718 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2697718 : Nat := 118140960795 + 2697718 * 2 ^ 59
def prefixEnd_2697718 : Nat := 4983230072969 + 3 ^ 40 * 2697718 * 2
def baseEnd_2697718 : Nat := 1385226004285981399618427

theorem tailTrace_2697718 : CollatzResearch.WordTrace tailWord_2697718 prefixEnd_2697718 1385226004285981399618427 := by
  unfold tailWord_2697718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6149616177539743399914863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65595905893757262932425205 6149616177539743399914863)
  ·
    refine ⟨9224424266309615099872295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6149616177539743399914863 9224424266309615099872295)
    ·
      refine ⟨13836636399464422649808443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9224424266309615099872295 13836636399464422649808443)
      ·
        refine ⟨20754954599196633974712665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13836636399464422649808443 20754954599196633974712665)
        ·
          refine ⟨15566215949397475481034499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20754954599196633974712665 15566215949397475481034499)
          ·
            refine ⟨23349323924096213221551749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15566215949397475481034499 23349323924096213221551749)
            ·
              refine ⟨4377998235768039979040953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23349323924096213221551749 4377998235768039979040953)
              ·
                refine ⟨3283498676826029984280715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4377998235768039979040953 3283498676826029984280715)
                ·
                  refine ⟨4925248015239044976421073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283498676826029984280715 4925248015239044976421073)
                  ·
                    refine ⟨3693936011429283732315805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4925248015239044976421073 3693936011429283732315805)
                    ·
                      refine ⟨1385226004285981399618427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3693936011429283732315805 1385226004285981399618427)
                      ·
                        rfl

theorem cell23_2697718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2697718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697718 prefixEnd_2697718 := by exact prefixLift 2697718
  have htrace : WordTrace (prefixWord ++ tailWord_2697718) baseStart_2697718 baseEnd_2697718 := by
    simpa [prefixWord, tailWord_2697718, baseEnd_2697718] using wordTrace_append hprefix tailTrace_2697718
  have hstable : (prefixWord ++ tailWord_2697718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697718).length < 2 ^ (prefixWord ++ tailWord_2697718).sum := by decide
  have hdescent : baseEnd_2697718 < baseStart_2697718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697727 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_2697727 : Nat := 118140960795 + 2697727 * 2 ^ 59
def prefixEnd_2697727 : Nat := 4983230072969 + 3 ^ 40 * 2697727 * 2
def baseEnd_2697727 : Nat := 1385230625611871864405885

theorem tailTrace_2697727 : CollatzResearch.WordTrace tailWord_2697727 prefixEnd_2697727 1385230625611871864405885 := by
  unfold tailWord_2697727
  simp only [CollatzResearch.WordTrace]
  refine ⟨98394187097603288935715435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65596124731735525957143623 98394187097603288935715435)
  ·
    refine ⟨147591280646404933403573153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98394187097603288935715435 147591280646404933403573153)
    ·
      refine ⟨110693460484803700052679865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147591280646404933403573153 110693460484803700052679865)
      ·
        refine ⟨83020095363602775039509899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110693460484803700052679865 83020095363602775039509899)
        ·
          refine ⟨124530143045404162559264849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83020095363602775039509899 124530143045404162559264849)
          ·
            refine ⟨93397607284053121919448637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124530143045404162559264849 93397607284053121919448637)
            ·
              refine ⟨35024102731519920719793239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93397607284053121919448637 35024102731519920719793239)
              ·
                refine ⟨52536154097279881079689859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35024102731519920719793239 52536154097279881079689859)
                ·
                  refine ⟨78804231145919821619534789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52536154097279881079689859 78804231145919821619534789)
                  ·
                    refine ⟨14775793339859966553662773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78804231145919821619534789 14775793339859966553662773)
                    ·
                      refine ⟨1385230625611871864405885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14775793339859966553662773 1385230625611871864405885)
                      ·
                        rfl

theorem cell23_2697727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_2697727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697727 prefixEnd_2697727 := by exact prefixLift 2697727
  have htrace : WordTrace (prefixWord ++ tailWord_2697727) baseStart_2697727 baseEnd_2697727 := by
    simpa [prefixWord, tailWord_2697727, baseEnd_2697727] using wordTrace_append hprefix tailTrace_2697727
  have hstable : (prefixWord ++ tailWord_2697727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697727).length < 2 ^ (prefixWord ++ tailWord_2697727).sum := by decide
  have hdescent : baseEnd_2697727 < baseStart_2697727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697732 : List Nat := [2, 3, 2, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2697732 : Nat := 118140960795 + 2697732 * 2 ^ 59
def prefixEnd_2697732 : Nat := 4983230072969 + 3 ^ 40 * 2697732 * 2
def baseEnd_2697732 : Nat := 1385233193015144344843363

theorem tailTrace_2697732 : CollatzResearch.WordTrace tailWord_2697732 prefixEnd_2697732 1385233193015144344843363 := by
  unfold tailWord_2697732
  simp only [CollatzResearch.WordTrace]
  refine ⟨49197184731292587394823725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65596246308390116526431633 49197184731292587394823725)
  ·
    refine ⟨18448944274234720273058897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49197184731292587394823725 18448944274234720273058897)
    ·
      refine ⟨13836708205676040204794173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18448944274234720273058897 13836708205676040204794173)
      ·
        refine ⟨5188765577128515076797815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13836708205676040204794173 5188765577128515076797815)
        ·
          refine ⟨7783148365692772615196723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5188765577128515076797815 7783148365692772615196723)
          ·
            refine ⟨11674722548539158922795085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7783148365692772615196723 11674722548539158922795085)
            ·
              refine ⟨4378020955702184596048157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11674722548539158922795085 4378020955702184596048157)
              ·
                refine ⟨1641757858388319223518059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4378020955702184596048157 1641757858388319223518059)
                ·
                  refine ⟨2462636787582478835277089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641757858388319223518059 2462636787582478835277089)
                  ·
                    refine ⟨1846977590686859126457817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2462636787582478835277089 1846977590686859126457817)
                    ·
                      refine ⟨1385233193015144344843363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1846977590686859126457817 1385233193015144344843363)
                      ·
                        rfl

theorem cell23_2697732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2697732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697732 prefixEnd_2697732 := by exact prefixLift 2697732
  have htrace : WordTrace (prefixWord ++ tailWord_2697732) baseStart_2697732 baseEnd_2697732 := by
    simpa [prefixWord, tailWord_2697732, baseEnd_2697732] using wordTrace_append hprefix tailTrace_2697732
  have hstable : (prefixWord ++ tailWord_2697732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697732).length < 2 ^ (prefixWord ++ tailWord_2697732).sum := by decide
  have hdescent : baseEnd_2697732 < baseStart_2697732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697787 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 9]
def baseStart_2697787 : Nat := 118140960795 + 2697787 * 2 ^ 59
def prefixEnd_2697787 : Nat := 4983230072969 + 3 ^ 40 * 2697787 * 2
def baseEnd_2697787 : Nat := 1385261434451141629655609

theorem tailTrace_2697787 : CollatzResearch.WordTrace tailWord_2697787 prefixEnd_2697787 1385261434451141629655609 := by
  unfold tailWord_2697787
  simp only [CollatzResearch.WordTrace]
  refine ⟨98396375477385919182899615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65597583651590612788599743 98396375477385919182899615)
  ·
    refine ⟨147594563216078878774349423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98396375477385919182899615 147594563216078878774349423)
    ·
      refine ⟨221391844824118318161524135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147594563216078878774349423 221391844824118318161524135)
      ·
        refine ⟨332087767236177477242286203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221391844824118318161524135 332087767236177477242286203)
        ·
          refine ⟨498131650854266215863429305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332087767236177477242286203 498131650854266215863429305)
          ·
            refine ⟨373598738140699661897571979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498131650854266215863429305 373598738140699661897571979)
            ·
              refine ⟨560398107211049492846357969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373598738140699661897571979 560398107211049492846357969)
              ·
                refine ⟨420298580408287119634768477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560398107211049492846357969 420298580408287119634768477)
                ·
                  refine ⟨157611967653107669863038179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420298580408287119634768477 157611967653107669863038179)
                  ·
                    refine ⟨236417951479661504794557269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 157611967653107669863038179 236417951479661504794557269)
                    ·
                      refine ⟨1385261434451141629655609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 236417951479661504794557269 1385261434451141629655609)
                      ·
                        rfl

theorem cell23_2697787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_2697787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697787 prefixEnd_2697787 := by exact prefixLift 2697787
  have htrace : WordTrace (prefixWord ++ tailWord_2697787) baseStart_2697787 baseEnd_2697787 := by
    simpa [prefixWord, tailWord_2697787, baseEnd_2697787] using wordTrace_append hprefix tailTrace_2697787
  have hstable : (prefixWord ++ tailWord_2697787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697787).length < 2 ^ (prefixWord ++ tailWord_2697787).sum := by decide
  have hdescent : baseEnd_2697787 < baseStart_2697787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697788 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 1, 4, 2]
def baseStart_2697788 : Nat := 118140960795 + 2697788 * 2 ^ 59
def prefixEnd_2697788 : Nat := 4983230072969 + 3 ^ 40 * 2697788 * 2
def baseEnd_2697788 : Nat := 1385261947931796125743105

theorem tailTrace_2697788 : CollatzResearch.WordTrace tailWord_2697788 prefixEnd_2697788 1385261947931796125743105 := by
  unfold tailWord_2697788
  simp only [CollatzResearch.WordTrace]
  refine ⟨49198205975191148176843009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65597607966921530902457345 49198205975191148176843009)
  ·
    refine ⟨36898654481393361132632257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49198205975191148176843009 36898654481393361132632257)
    ·
      refine ⟨27673990861045020849474193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36898654481393361132632257 27673990861045020849474193)
      ·
        refine ⟨20755493145783765637105645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27673990861045020849474193 20755493145783765637105645)
        ·
          refine ⟨7783309929668912113914617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20755493145783765637105645 7783309929668912113914617)
          ·
            refine ⟨5837482447251684085435963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7783309929668912113914617 5837482447251684085435963)
            ·
              refine ⟨8756223670877526128153945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837482447251684085435963 8756223670877526128153945)
              ·
                refine ⟨6567167753158144596115459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8756223670877526128153945 6567167753158144596115459)
                ·
                  refine ⟨9850751629737216894173189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6567167753158144596115459 9850751629737216894173189)
                  ·
                    refine ⟨1847015930575728167657473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9850751629737216894173189 1847015930575728167657473)
                    ·
                      refine ⟨1385261947931796125743105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847015930575728167657473 1385261947931796125743105)
                      ·
                        rfl

theorem cell23_2697788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_2697788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697788 prefixEnd_2697788 := by exact prefixLift 2697788
  have htrace : WordTrace (prefixWord ++ tailWord_2697788) baseStart_2697788 baseEnd_2697788 := by
    simpa [prefixWord, tailWord_2697788, baseEnd_2697788] using wordTrace_append hprefix tailTrace_2697788
  have hstable : (prefixWord ++ tailWord_2697788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697788).length < 2 ^ (prefixWord ++ tailWord_2697788).sum := by decide
  have hdescent : baseEnd_2697788 < baseStart_2697788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697824 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 4, 5]
def baseStart_2697824 : Nat := 118140960795 + 2697824 * 2 ^ 59
def prefixEnd_2697824 : Nat := 4983230072969 + 3 ^ 40 * 2697824 * 2
def baseEnd_2697824 : Nat := 461760144411785994964313

theorem tailTrace_2697824 : CollatzResearch.WordTrace tailWord_2697824 prefixEnd_2697824 461760144411785994964313 := by
  unfold tailWord_2697824
  simp only [CollatzResearch.WordTrace]
  refine ⟨49198862489125937250998263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65598483318834583001331017 49198862489125937250998263)
  ·
    refine ⟨73798293733688905876497395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49198862489125937250998263 73798293733688905876497395)
    ·
      refine ⟨110697440600533358814746093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73798293733688905876497395 110697440600533358814746093)
      ·
        refine ⟨41511540225200009555529785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110697440600533358814746093 41511540225200009555529785)
        ·
          refine ⟨31133655168900007166647339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41511540225200009555529785 31133655168900007166647339)
          ·
            refine ⟨46700482753350010749971009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31133655168900007166647339 46700482753350010749971009)
            ·
              refine ⟨35025362065012508062478257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46700482753350010749971009 35025362065012508062478257)
              ·
                refine ⟨26269021548759381046858693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35025362065012508062478257 26269021548759381046858693)
                ·
                  refine ⟨4925441540392383946286005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26269021548759381046858693 4925441540392383946286005)
                  ·
                    refine ⟨461760144411785994964313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4925441540392383946286005 461760144411785994964313)
                    ·
                      rfl

theorem cell23_2697824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_2697824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697824 prefixEnd_2697824 := by exact prefixLift 2697824
  have htrace : WordTrace (prefixWord ++ tailWord_2697824) baseStart_2697824 baseEnd_2697824 := by
    simpa [prefixWord, tailWord_2697824, baseEnd_2697824] using wordTrace_append hprefix tailTrace_2697824
  have hstable : (prefixWord ++ tailWord_2697824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697824).length < 2 ^ (prefixWord ++ tailWord_2697824).sum := by decide
  have hdescent : baseEnd_2697824 < baseStart_2697824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697831 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_2697831 : Nat := 118140960795 + 2697831 * 2 ^ 59
def prefixEnd_2697831 : Nat := 4983230072969 + 3 ^ 40 * 2697831 * 2
def baseEnd_2697831 : Nat := 1385284027599939457505407

theorem tailTrace_2697831 : CollatzResearch.WordTrace tailWord_2697831 prefixEnd_2697831 1385284027599939457505407 := by
  unfold tailWord_2697831
  simp only [CollatzResearch.WordTrace]
  refine ⟨98397980289226514697501347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65598653526151009798334231 98397980289226514697501347)
  ·
    refine ⟨147596970433839772046252021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98397980289226514697501347 147596970433839772046252021)
    ·
      refine ⟨13837215978172478629336127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147596970433839772046252021 13837215978172478629336127)
      ·
        refine ⟨20755823967258717944004191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13837215978172478629336127 20755823967258717944004191)
        ·
          refine ⟨31133735950888076916006287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20755823967258717944004191 31133735950888076916006287)
          ·
            refine ⟨46700603926332115374009431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31133735950888076916006287 46700603926332115374009431)
            ·
              refine ⟨70050905889498173061014147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46700603926332115374009431 70050905889498173061014147)
              ·
                refine ⟨105076358834247259591521221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70050905889498173061014147 105076358834247259591521221)
                ·
                  refine ⟨19701817281421361173410229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105076358834247259591521221 19701817281421361173410229)
                  ·
                    refine ⟨1847045370133252610007209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19701817281421361173410229 1847045370133252610007209)
                    ·
                      refine ⟨1385284027599939457505407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847045370133252610007209 1385284027599939457505407)
                      ·
                        rfl

theorem cell23_2697831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_2697831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697831 prefixEnd_2697831 := by exact prefixLift 2697831
  have htrace : WordTrace (prefixWord ++ tailWord_2697831) baseStart_2697831 baseEnd_2697831 := by
    simpa [prefixWord, tailWord_2697831, baseEnd_2697831] using wordTrace_append hprefix tailTrace_2697831
  have hstable : (prefixWord ++ tailWord_2697831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697831).length < 2 ^ (prefixWord ++ tailWord_2697831).sum := by decide
  have hdescent : baseEnd_2697831 < baseStart_2697831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697845 : List Nat := [1, 3, 4, 2, 2, 1, 2, 3, 5]
def baseStart_2697845 : Nat := 118140960795 + 2697845 * 2 ^ 59
def prefixEnd_2697845 : Nat := 4983230072969 + 3 ^ 40 * 2697845 * 2
def baseEnd_2697845 : Nat := 153921246258789155858927

theorem tailTrace_2697845 : CollatzResearch.WordTrace tailWord_2697845 prefixEnd_2697845 153921246258789155858927 := by
  unfold tailWord_2697845
  simp only [CollatzResearch.WordTrace]
  refine ⟨98398490911175795088510989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65598993940783863392340659 98398490911175795088510989)
  ·
    refine ⟨36899434091690923158191621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98398490911175795088510989 36899434091690923158191621)
    ·
      refine ⟨6918643892192048092160929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36899434091690923158191621 6918643892192048092160929)
      ·
        refine ⟨5188982919144036069120697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6918643892192048092160929 5188982919144036069120697)
        ·
          refine ⟨3891737189358027051840523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5188982919144036069120697 3891737189358027051840523)
          ·
            refine ⟨5837605784037040577760785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891737189358027051840523 5837605784037040577760785)
            ·
              refine ⟨4378204338027780433320589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5837605784037040577760785 4378204338027780433320589)
              ·
                refine ⟨1641826626760417662495221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4378204338027780433320589 1641826626760417662495221)
                ·
                  refine ⟨153921246258789155858927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1641826626760417662495221 153921246258789155858927)
                  ·
                    rfl

theorem cell23_2697845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_2697845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697845 prefixEnd_2697845 := by exact prefixLift 2697845
  have htrace : WordTrace (prefixWord ++ tailWord_2697845) baseStart_2697845 baseEnd_2697845 := by
    simpa [prefixWord, tailWord_2697845, baseEnd_2697845] using wordTrace_append hprefix tailTrace_2697845
  have hstable : (prefixWord ++ tailWord_2697845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697845).length < 2 ^ (prefixWord ++ tailWord_2697845).sum := by decide
  have hdescent : baseEnd_2697845 < baseStart_2697845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697901 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 8]
def baseStart_2697901 : Nat := 118140960795 + 2697901 * 2 ^ 59
def prefixEnd_2697901 : Nat := 4983230072969 + 3 ^ 40 * 2697901 * 2
def baseEnd_2697901 : Nat := 153924441249528242625565

theorem tailTrace_2697901 : CollatzResearch.WordTrace tailWord_2697901 prefixEnd_2697901 153924441249528242625565 := by
  unfold tailWord_2697901
  simp only [CollatzResearch.WordTrace]
  refine ⟨98400533398972916652549557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65600355599315277768366371 98400533398972916652549557)
  ·
    refine ⟨9225050006153710936176521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98400533398972916652549557 9225050006153710936176521)
    ·
      refine ⟨6918787504615283202132391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9225050006153710936176521 6918787504615283202132391)
      ·
        refine ⟨10378181256922924803198587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6918787504615283202132391 10378181256922924803198587)
        ·
          refine ⟨15567271885384387204797881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10378181256922924803198587 15567271885384387204797881)
          ·
            refine ⟨11675453914038290403598411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15567271885384387204797881 11675453914038290403598411)
            ·
              refine ⟨17513180871057435605397617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11675453914038290403598411 17513180871057435605397617)
              ·
                refine ⟨13134885653293076704048213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17513180871057435605397617 13134885653293076704048213)
                ·
                  refine ⟨153924441249528242625565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13134885653293076704048213 153924441249528242625565)
                  ·
                    rfl

theorem cell23_2697901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_2697901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697901 prefixEnd_2697901 := by exact prefixLift 2697901
  have htrace : WordTrace (prefixWord ++ tailWord_2697901) baseStart_2697901 baseEnd_2697901 := by
    simpa [prefixWord, tailWord_2697901, baseEnd_2697901] using wordTrace_append hprefix tailTrace_2697901
  have hstable : (prefixWord ++ tailWord_2697901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697901).length < 2 ^ (prefixWord ++ tailWord_2697901).sum := by decide
  have hdescent : baseEnd_2697901 < baseStart_2697901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697955 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 2, 3, 2]
def baseStart_2697955 : Nat := 118140960795 + 2697955 * 2 ^ 59
def prefixEnd_2697955 : Nat := 4983230072969 + 3 ^ 40 * 2697955 * 2
def baseEnd_2697955 : Nat := 1385347699201096972354837

theorem tailTrace_2697955 : CollatzResearch.WordTrace tailWord_2697955 prefixEnd_2697955 1385347699201096972354837 := by
  unfold tailWord_2697955
  simp only [CollatzResearch.WordTrace]
  refine ⟨98402502940777283875015319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65601668627184855916676879 98402502940777283875015319)
  ·
    refine ⟨147603754411165925812522979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98402502940777283875015319 147603754411165925812522979)
    ·
      refine ⟨221405631616748888718784469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147603754411165925812522979 221405631616748888718784469)
      ·
        refine ⟨5189194491017552079346511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 221405631616748888718784469 5189194491017552079346511)
        ·
          refine ⟨7783791736526328119019767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5189194491017552079346511 7783791736526328119019767)
          ·
            refine ⟨11675687604789492178529651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7783791736526328119019767 11675687604789492178529651)
            ·
              refine ⟨17513531407184238267794477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11675687604789492178529651 17513531407184238267794477)
              ·
                refine ⟨6567574277694089350422929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17513531407184238267794477 6567574277694089350422929)
                ·
                  refine ⟨4925680708270567012817197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6567574277694089350422929 4925680708270567012817197)
                  ·
                    refine ⟨1847130265601462629806449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4925680708270567012817197 1847130265601462629806449)
                    ·
                      refine ⟨1385347699201096972354837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847130265601462629806449 1385347699201096972354837)
                      ·
                        rfl

theorem cell23_2697955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_2697955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697955 prefixEnd_2697955 := by exact prefixLift 2697955
  have htrace : WordTrace (prefixWord ++ tailWord_2697955) baseStart_2697955 baseEnd_2697955 := by
    simpa [prefixWord, tailWord_2697955, baseEnd_2697955] using wordTrace_append hprefix tailTrace_2697955
  have hstable : (prefixWord ++ tailWord_2697955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697955).length < 2 ^ (prefixWord ++ tailWord_2697955).sum := by decide
  have hdescent : baseEnd_2697955 < baseStart_2697955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697961 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 6, 4]
def baseStart_2697961 : Nat := 118140960795 + 2697961 * 2 ^ 59
def prefixEnd_2697961 : Nat := 4983230072969 + 3 ^ 40 * 2697961 * 2
def baseEnd_2697961 : Nat := 461783593361674649626603

theorem tailTrace_2697961 : CollatzResearch.WordTrace tailWord_2697961 prefixEnd_2697961 461783593361674649626603 := by
  unfold tailWord_2697961
  simp only [CollatzResearch.WordTrace]
  refine ⟨98402721778755546899733737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65601814519170364599822491 98402721778755546899733737)
  ·
    refine ⟨73802041334066660174800303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98402721778755546899733737 73802041334066660174800303)
    ·
      refine ⟨110703062001099990262200455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73802041334066660174800303 110703062001099990262200455)
      ·
        refine ⟨166054593001649985393300683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110703062001099990262200455 166054593001649985393300683)
        ·
          refine ⟨249081889502474978089951025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166054593001649985393300683 249081889502474978089951025)
          ·
            refine ⟨186811417126856233567463269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249081889502474978089951025 186811417126856233567463269)
            ·
              refine ⟨35027140711285543793899363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186811417126856233567463269 35027140711285543793899363)
              ·
                refine ⟨52540711066928315690849045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35027140711285543793899363 52540711066928315690849045)
                ·
                  refine ⟨2462845831262264798008549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52540711066928315690849045 2462845831262264798008549)
                  ·
                    refine ⟨461783593361674649626603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2462845831262264798008549 461783593361674649626603)
                    ·
                      rfl

theorem cell23_2697961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 4].length) (baseStart_2697961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697961 prefixEnd_2697961 := by exact prefixLift 2697961
  have htrace : WordTrace (prefixWord ++ tailWord_2697961) baseStart_2697961 baseEnd_2697961 := by
    simpa [prefixWord, tailWord_2697961, baseEnd_2697961] using wordTrace_append hprefix tailTrace_2697961
  have hstable : (prefixWord ++ tailWord_2697961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697961).length < 2 ^ (prefixWord ++ tailWord_2697961).sum := by decide
  have hdescent : baseEnd_2697961 < baseStart_2697961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697965 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_2697965 : Nat := 118140960795 + 2697965 * 2 ^ 59
def prefixEnd_2697965 : Nat := 4983230072969 + 3 ^ 40 * 2697965 * 2
def baseEnd_2697965 : Nat := 461784278002547311076597

theorem tailTrace_2697965 : CollatzResearch.WordTrace tailWord_2697965 prefixEnd_2697965 461784278002547311076597 := by
  unfold tailWord_2697965
  simp only [CollatzResearch.WordTrace]
  refine ⟨98402867670741055582879349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65601911780494037055252899 98402867670741055582879349)
  ·
    refine ⟨9225268844131973960894939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98402867670741055582879349 9225268844131973960894939)
    ·
      refine ⟨13837903266197960941342409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9225268844131973960894939 13837903266197960941342409)
      ·
        refine ⟨10378427449648470706006807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13837903266197960941342409 10378427449648470706006807)
        ·
          refine ⟨15567641174472706059010211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10378427449648470706006807 15567641174472706059010211)
          ·
            refine ⟨23351461761709059088515317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15567641174472706059010211 23351461761709059088515317)
            ·
              refine ⟨2189199540160224289548311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23351461761709059088515317 2189199540160224289548311)
              ·
                refine ⟨3283799310240336434322467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189199540160224289548311 3283799310240336434322467)
                ·
                  refine ⟨4925698965360504651483701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283799310240336434322467 4925698965360504651483701)
                  ·
                    refine ⟨461784278002547311076597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4925698965360504651483701 461784278002547311076597)
                    ·
                      rfl

theorem cell23_2697965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_2697965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697965 prefixEnd_2697965 := by exact prefixLift 2697965
  have htrace : WordTrace (prefixWord ++ tailWord_2697965) baseStart_2697965 baseEnd_2697965 := by
    simpa [prefixWord, tailWord_2697965, baseEnd_2697965] using wordTrace_append hprefix tailTrace_2697965
  have hstable : (prefixWord ++ tailWord_2697965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697965).length < 2 ^ (prefixWord ++ tailWord_2697965).sum := by decide
  have hdescent : baseEnd_2697965 < baseStart_2697965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697973 : List Nat := [1, 3, 6, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2697973 : Nat := 118140960795 + 2697973 * 2 ^ 59
def prefixEnd_2697973 : Nat := 4983230072969 + 3 ^ 40 * 2697973 * 2
def baseEnd_2697973 : Nat := 461785647284292633976585

theorem tailTrace_2697973 : CollatzResearch.WordTrace tailWord_2697973 prefixEnd_2697973 461785647284292633976585 := by
  unfold tailWord_2697973
  simp only [CollatzResearch.WordTrace]
  refine ⟨98403159454712072949170573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65602106303141381966113715 98403159454712072949170573)
  ·
    refine ⟨36901184795517027355938965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98403159454712072949170573 36901184795517027355938965)
    ·
      refine ⟨1729743037289860657309639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36901184795517027355938965 1729743037289860657309639)
      ·
        refine ⟨2594614555934790985964459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1729743037289860657309639 2594614555934790985964459)
        ·
          refine ⟨3891921833902186478946689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594614555934790985964459 3891921833902186478946689)
          ·
            refine ⟨2918941375426639859210017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3891921833902186478946689 2918941375426639859210017)
            ·
              refine ⟨2189206031569979894407513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2918941375426639859210017 2189206031569979894407513)
              ·
                refine ⟨1641904523677484920805635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189206031569979894407513 1641904523677484920805635)
                ·
                  refine ⟨2462856785516227381208453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641904523677484920805635 2462856785516227381208453)
                  ·
                    refine ⟨461785647284292633976585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2462856785516227381208453 461785647284292633976585)
                    ·
                      rfl

theorem cell23_2697973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2697973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697973 prefixEnd_2697973 := by exact prefixLift 2697973
  have htrace : WordTrace (prefixWord ++ tailWord_2697973) baseStart_2697973 baseEnd_2697973 := by
    simpa [prefixWord, tailWord_2697973, baseEnd_2697973] using wordTrace_append hprefix tailTrace_2697973
  have hstable : (prefixWord ++ tailWord_2697973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697973).length < 2 ^ (prefixWord ++ tailWord_2697973).sum := by decide
  have hdescent : baseEnd_2697973 < baseStart_2697973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697978 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_2697978 : Nat := 118140960795 + 2697978 * 2 ^ 59
def prefixEnd_2697978 : Nat := 4983230072969 + 3 ^ 40 * 2697978 * 2
def baseEnd_2697978 : Nat := 461786503085383460789077

theorem tailTrace_2697978 : CollatzResearch.WordTrace tailWord_2697978 prefixEnd_2697978 461786503085383460789077 := by
  unfold tailWord_2697978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24600835454923489700775647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65602227879795972535401725 24600835454923489700775647)
  ·
    refine ⟨36901253182385234551163471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24600835454923489700775647 36901253182385234551163471)
    ·
      refine ⟨55351879773577851826745207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36901253182385234551163471 55351879773577851826745207)
      ·
        refine ⟨83027819660366777740117811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55351879773577851826745207 83027819660366777740117811)
        ·
          refine ⟨124541729490550166610176717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83027819660366777740117811 124541729490550166610176717)
          ·
            refine ⟨46703148558956312478816269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124541729490550166610176717 46703148558956312478816269)
            ·
              refine ⟨17513680709608617179556101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46703148558956312478816269 17513680709608617179556101)
              ·
                refine ⟨3283815133051615721166769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17513680709608617179556101 3283815133051615721166769)
                ·
                  refine ⟨2462861349788711790875077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3283815133051615721166769 2462861349788711790875077)
                  ·
                    refine ⟨461786503085383460789077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2462861349788711790875077 461786503085383460789077)
                    ·
                      rfl

theorem cell23_2697978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_2697978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697978 prefixEnd_2697978 := by exact prefixLift 2697978
  have htrace : WordTrace (prefixWord ++ tailWord_2697978) baseStart_2697978 baseEnd_2697978 := by
    simpa [prefixWord, tailWord_2697978, baseEnd_2697978] using wordTrace_append hprefix tailTrace_2697978
  have hstable : (prefixWord ++ tailWord_2697978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697978).length < 2 ^ (prefixWord ++ tailWord_2697978).sum := by decide
  have hdescent : baseEnd_2697978 < baseStart_2697978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697981 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_2697981 : Nat := 118140960795 + 2697981 * 2 ^ 59
def prefixEnd_2697981 : Nat := 4983230072969 + 3 ^ 40 * 2697981 * 2
def baseEnd_2697981 : Nat := 1385361049698113870629717

theorem tailTrace_2697981 : CollatzResearch.WordTrace tailWord_2697981 prefixEnd_2697981 1385361049698113870629717 := by
  unfold tailWord_2697981
  simp only [CollatzResearch.WordTrace]
  refine ⟨98403451238683090315461797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65602300825788726876974531 98403451238683090315461797)
  ·
    refine ⟨18450647107253079434149087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98403451238683090315461797 18450647107253079434149087)
    ·
      refine ⟨27675970660879619151223631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18450647107253079434149087 27675970660879619151223631)
      ·
        refine ⟨41513955991319428726835447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27675970660879619151223631 41513955991319428726835447)
        ·
          refine ⟨62270933986979143090253171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41513955991319428726835447 62270933986979143090253171)
          ·
            refine ⟨93406400980468714635379757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62270933986979143090253171 93406400980468714635379757)
            ·
              refine ⟨35027400367675767988267409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93406400980468714635379757 35027400367675767988267409)
              ·
                refine ⟨26270550275756825991200557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35027400367675767988267409 26270550275756825991200557)
                ·
                  refine ⟨9851456353408809746700209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26270550275756825991200557 9851456353408809746700209)
                  ·
                    refine ⟨7388592265056607310025157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9851456353408809746700209 7388592265056607310025157)
                    ·
                      refine ⟨1385361049698113870629717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7388592265056607310025157 1385361049698113870629717)
                      ·
                        rfl

theorem cell23_2697981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_2697981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697981 prefixEnd_2697981 := by exact prefixLift 2697981
  have htrace : WordTrace (prefixWord ++ tailWord_2697981) baseStart_2697981 baseEnd_2697981 := by
    simpa [prefixWord, tailWord_2697981, baseEnd_2697981] using wordTrace_append hprefix tailTrace_2697981
  have hstable : (prefixWord ++ tailWord_2697981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697981).length < 2 ^ (prefixWord ++ tailWord_2697981).sum := by decide
  have hdescent : baseEnd_2697981 < baseStart_2697981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697985 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_2697985 : Nat := 118140960795 + 2697985 * 2 ^ 59
def prefixEnd_2697985 : Nat := 4983230072969 + 3 ^ 40 * 2697985 * 2
def baseEnd_2697985 : Nat := 1385363103620731854979699

theorem tailTrace_2697985 : CollatzResearch.WordTrace tailWord_2697985 prefixEnd_2697985 1385363103620731854979699 := by
  unfold tailWord_2697985
  simp only [CollatzResearch.WordTrace]
  refine ⟨98403597130668598998607409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65602398087112399332404939 98403597130668598998607409)
  ·
    refine ⟨73802697848001449248955557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98403597130668598998607409 73802697848001449248955557)
    ·
      refine ⟨13838005846500271734179167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73802697848001449248955557 13838005846500271734179167)
      ·
        refine ⟨20757008769750407601268751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13838005846500271734179167 20757008769750407601268751)
        ·
          refine ⟨31135513154625611401903127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20757008769750407601268751 31135513154625611401903127)
          ·
            refine ⟨46703269731938417102854691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31135513154625611401903127 46703269731938417102854691)
            ·
              refine ⟨70054904597907625654282037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46703269731938417102854691 70054904597907625654282037)
              ·
                refine ⟨6567647306053839905088941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70054904597907625654282037 6567647306053839905088941)
                ·
                  refine ⟨2462867739770189964408353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6567647306053839905088941 2462867739770189964408353)
                  ·
                    refine ⟨1847150804827642473306265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2462867739770189964408353 1847150804827642473306265)
                    ·
                      refine ⟨1385363103620731854979699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847150804827642473306265 1385363103620731854979699)
                      ·
                        rfl

theorem cell23_2697985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_2697985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697985 prefixEnd_2697985 := by exact prefixLift 2697985
  have htrace : WordTrace (prefixWord ++ tailWord_2697985) baseStart_2697985 baseEnd_2697985 := by
    simpa [prefixWord, tailWord_2697985, baseEnd_2697985] using wordTrace_append hprefix tailTrace_2697985
  have hstable : (prefixWord ++ tailWord_2697985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697985).length < 2 ^ (prefixWord ++ tailWord_2697985).sum := by decide
  have hdescent : baseEnd_2697985 < baseStart_2697985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2697988 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2697988 : Nat := 118140960795 + 2697988 * 2 ^ 59
def prefixEnd_2697988 : Nat := 4983230072969 + 3 ^ 40 * 2697988 * 2
def baseEnd_2697988 : Nat := 1385364644062695343242185

theorem tailTrace_2697988 : CollatzResearch.WordTrace tailWord_2697988 prefixEnd_2697988 1385364644062695343242185 := by
  unfold tailWord_2697988
  simp only [CollatzResearch.WordTrace]
  refine ⟨49201853274828865255483309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65602471033105153673977745 49201853274828865255483309)
  ·
    refine ⟨18450694978060824470806241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49201853274828865255483309 18450694978060824470806241)
    ·
      refine ⟨13838021233545618353104681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18450694978060824470806241 13838021233545618353104681)
      ·
        refine ⟨10378515925159213764828511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13838021233545618353104681 10378515925159213764828511)
        ·
          refine ⟨15567773887738820647242767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10378515925159213764828511 15567773887738820647242767)
          ·
            refine ⟨23351660831608230970864151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15567773887738820647242767 23351660831608230970864151)
            ·
              refine ⟨35027491247412346456296227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23351660831608230970864151 35027491247412346456296227)
              ·
                refine ⟨52541236871118519684444341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35027491247412346456296227 52541236871118519684444341)
                ·
                  refine ⟨4925740956667361220416657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52541236871118519684444341 4925740956667361220416657)
                  ·
                    refine ⟨3694305717500520915312493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4925740956667361220416657 3694305717500520915312493)
                    ·
                      refine ⟨1385364644062695343242185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3694305717500520915312493 1385364644062695343242185)
                      ·
                        rfl

theorem cell23_2697988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2697988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2697988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2697988 prefixEnd_2697988 := by exact prefixLift 2697988
  have htrace : WordTrace (prefixWord ++ tailWord_2697988) baseStart_2697988 baseEnd_2697988 := by
    simpa [prefixWord, tailWord_2697988, baseEnd_2697988] using wordTrace_append hprefix tailTrace_2697988
  have hstable : (prefixWord ++ tailWord_2697988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2697988).length < 2 ^ (prefixWord ++ tailWord_2697988).sum := by decide
  have hdescent : baseEnd_2697988 < baseStart_2697988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2697988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698035 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 4, 1, 3]
def baseStart_2698035 : Nat := 118140960795 + 2698035 * 2 ^ 59
def prefixEnd_2698035 : Nat := 4983230072969 + 3 ^ 40 * 2698035 * 2
def baseEnd_2698035 : Nat := 1385388777653456659354469

theorem tailTrace_2698035 : CollatzResearch.WordTrace tailWord_2698035 prefixEnd_2698035 1385388777653456659354469 := by
  unfold tailWord_2698035
  simp only [CollatzResearch.WordTrace]
  refine ⟨98405420780487457537927559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65603613853658305025285039 98405420780487457537927559)
  ·
    refine ⟨147608131170731186306891339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98405420780487457537927559 147608131170731186306891339)
    ·
      refine ⟨221412196756096779460337009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147608131170731186306891339 221412196756096779460337009)
      ·
        refine ⟨166059147567072584595252757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221412196756096779460337009 166059147567072584595252757)
        ·
          refine ⟨7784022542206527402902473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 166059147567072584595252757 7784022542206527402902473)
          ·
            refine ⟨5838016906654895552176855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7784022542206527402902473 5838016906654895552176855)
            ·
              refine ⟨8757025359982343328265283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5838016906654895552176855 8757025359982343328265283)
              ·
                refine ⟨13135538039973514992397925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8757025359982343328265283 13135538039973514992397925)
                ·
                  refine ⟨2462913382495034061074611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13135538039973514992397925 2462913382495034061074611)
                  ·
                    refine ⟨3694370073742551091611917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2462913382495034061074611 3694370073742551091611917)
                    ·
                      refine ⟨1385388777653456659354469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3694370073742551091611917 1385388777653456659354469)
                      ·
                        rfl

theorem cell23_2698035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 1, 3].length) (baseStart_2698035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698035 prefixEnd_2698035 := by exact prefixLift 2698035
  have htrace : WordTrace (prefixWord ++ tailWord_2698035) baseStart_2698035 baseEnd_2698035 := by
    simpa [prefixWord, tailWord_2698035, baseEnd_2698035] using wordTrace_append hprefix tailTrace_2698035
  have hstable : (prefixWord ++ tailWord_2698035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698035).length < 2 ^ (prefixWord ++ tailWord_2698035).sum := by decide
  have hdescent : baseEnd_2698035 < baseStart_2698035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698049 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2698049 : Nat := 118140960795 + 2698049 * 2 ^ 59
def prefixEnd_2698049 : Nat := 4983230072969 + 3 ^ 40 * 2698049 * 2
def baseEnd_2698049 : Nat := 1385395966382619604579405

theorem tailTrace_2698049 : CollatzResearch.WordTrace tailWord_2698049 prefixEnd_2698049 1385395966382619604579405 := by
  unfold tailWord_2698049
  simp only [CollatzResearch.WordTrace]
  refine ⟨98405931402436737928937201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65603954268291158619291467 98405931402436737928937201)
  ·
    refine ⟨73804448551827553446702901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98405931402436737928937201 73804448551827553446702901)
    ·
      refine ⟨6919167051733833135628397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73804448551827553446702901 6919167051733833135628397)
      ·
        refine ⟨2594687644400187425860649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6919167051733833135628397 2594687644400187425860649)
        ·
          refine ⟨1946015733300140569395487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2594687644400187425860649 1946015733300140569395487)
          ·
            refine ⟨2919023599950210854093231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946015733300140569395487 2919023599950210854093231)
            ·
              refine ⟨4378535399925316281139847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919023599950210854093231 4378535399925316281139847)
              ·
                refine ⟨6567803099887974421709771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4378535399925316281139847 6567803099887974421709771)
                ·
                  refine ⟨9851704649831961632564657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6567803099887974421709771 9851704649831961632564657)
                  ·
                    refine ⟨7388778487373971224423493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9851704649831961632564657 7388778487373971224423493)
                    ·
                      refine ⟨1385395966382619604579405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7388778487373971224423493 1385395966382619604579405)
                      ·
                        rfl

theorem cell23_2698049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2698049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698049 prefixEnd_2698049 := by exact prefixLift 2698049
  have htrace : WordTrace (prefixWord ++ tailWord_2698049) baseStart_2698049 baseEnd_2698049 := by
    simpa [prefixWord, tailWord_2698049, baseEnd_2698049] using wordTrace_append hprefix tailTrace_2698049
  have hstable : (prefixWord ++ tailWord_2698049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698049).length < 2 ^ (prefixWord ++ tailWord_2698049).sum := by decide
  have hdescent : baseEnd_2698049 < baseStart_2698049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698051 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 2, 6]
def baseStart_2698051 : Nat := 118140960795 + 2698051 * 2 ^ 59
def prefixEnd_2698051 : Nat := 4983230072969 + 3 ^ 40 * 2698051 * 2
def baseEnd_2698051 : Nat := 461798997781309532251465

theorem tailTrace_2698051 : CollatzResearch.WordTrace tailWord_2698051 prefixEnd_2698051 461798997781309532251465 := by
  unfold tailWord_2698051
  simp only [CollatzResearch.WordTrace]
  refine ⟨98406004348429492270510007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65604002898952994847006671 98406004348429492270510007)
  ·
    refine ⟨147609006522644238405765011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98406004348429492270510007 147609006522644238405765011)
    ·
      refine ⟨221413509783966357608647517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147609006522644238405765011 221413509783966357608647517)
      ·
        refine ⟨83030066168987384103242819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221413509783966357608647517 83030066168987384103242819)
        ·
          refine ⟨124545099253481076154864229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83030066168987384103242819 124545099253481076154864229)
          ·
            refine ⟨23352206110027701779037043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124545099253481076154864229 23352206110027701779037043)
            ·
              refine ⟨35028309165041552668555565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23352206110027701779037043 35028309165041552668555565)
              ·
                refine ⟨13135615936890582250708337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35028309165041552668555565 13135615936890582250708337)
                ·
                  refine ⟨9851711952667936688031253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13135615936890582250708337 9851711952667936688031253)
                  ·
                    refine ⟨461798997781309532251465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9851711952667936688031253 461798997781309532251465)
                    ·
                      rfl

theorem cell23_2698051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 6].length) (baseStart_2698051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698051 prefixEnd_2698051 := by exact prefixLift 2698051
  have htrace : WordTrace (prefixWord ++ tailWord_2698051) baseStart_2698051 baseEnd_2698051 := by
    simpa [prefixWord, tailWord_2698051, baseEnd_2698051] using wordTrace_append hprefix tailTrace_2698051
  have hstable : (prefixWord ++ tailWord_2698051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698051).length < 2 ^ (prefixWord ++ tailWord_2698051).sum := by decide
  have hdescent : baseEnd_2698051 < baseStart_2698051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698092 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 2, 2, 2]
def baseStart_2698092 : Nat := 118140960795 + 2698092 * 2 ^ 59
def prefixEnd_2698092 : Nat := 4983230072969 + 3 ^ 40 * 2698092 * 2
def baseEnd_2698092 : Nat := 1385418046050762936341707

theorem tailTrace_2698092 : CollatzResearch.WordTrace tailWord_2698092 prefixEnd_2698092 1385418046050762936341707 := by
  unfold tailWord_2698092
  simp only [CollatzResearch.WordTrace]
  refine ⟨49203749870640478136376265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65604999827520637515168353 49203749870640478136376265)
  ·
    refine ⟨36902812402980358602282199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49203749870640478136376265 36902812402980358602282199)
    ·
      refine ⟨55354218604470537903423299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36902812402980358602282199 55354218604470537903423299)
      ·
        refine ⟨83031327906705806855134949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55354218604470537903423299 83031327906705806855134949)
        ·
          refine ⟨15568373982507338785337803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83031327906705806855134949 15568373982507338785337803)
          ·
            refine ⟨23352560973761008178006705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15568373982507338785337803 23352560973761008178006705)
            ·
              refine ⟨17514420730320756133505029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23352560973761008178006705 17514420730320756133505029)
              ·
                refine ⟨3283953886935141775032193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17514420730320756133505029 3283953886935141775032193)
                ·
                  refine ⟨2462965415201356331274145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3283953886935141775032193 2462965415201356331274145)
                  ·
                    refine ⟨1847224061401017248455609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2462965415201356331274145 1847224061401017248455609)
                    ·
                      refine ⟨1385418046050762936341707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847224061401017248455609 1385418046050762936341707)
                      ·
                        rfl

theorem cell23_2698092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_2698092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698092 prefixEnd_2698092 := by exact prefixLift 2698092
  have htrace : WordTrace (prefixWord ++ tailWord_2698092) baseStart_2698092 baseEnd_2698092 := by
    simpa [prefixWord, tailWord_2698092, baseEnd_2698092] using wordTrace_append hprefix tailTrace_2698092
  have hstable : (prefixWord ++ tailWord_2698092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698092).length < 2 ^ (prefixWord ++ tailWord_2698092).sum := by decide
  have hdescent : baseEnd_2698092 < baseStart_2698092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698098 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 7]
def baseStart_2698098 : Nat := 118140960795 + 2698098 * 2 ^ 59
def prefixEnd_2698098 : Nat := 4983230072969 + 3 ^ 40 * 2698098 * 2
def baseEnd_2698098 : Nat := 153935680770521101429631

theorem tailTrace_2698098 : CollatzResearch.WordTrace tailWord_2698098 prefixEnd_2698098 153935680770521101429631 := by
  unfold tailWord_2698098
  simp only [CollatzResearch.WordTrace]
  refine ⟨24601929644814804824367737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65605145719506146198313965 24601929644814804824367737)
  ·
    refine ⟨18451447233611103618275803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24601929644814804824367737 18451447233611103618275803)
    ·
      refine ⟨27677170850416655427413705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18451447233611103618275803 27677170850416655427413705)
      ·
        refine ⟨20757878137812491570560279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27677170850416655427413705 20757878137812491570560279)
        ·
          refine ⟨31136817206718737355840419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20757878137812491570560279 31136817206718737355840419)
          ·
            refine ⟨46705225810078106033760629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31136817206718737355840419 46705225810078106033760629)
            ·
              refine ⟨4378614919694822440665059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46705225810078106033760629 4378614919694822440665059)
              ·
                refine ⟨6567922379542233660997589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4378614919694822440665059 6567922379542233660997589)
                ·
                  refine ⟨153935680770521101429631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6567922379542233660997589 153935680770521101429631)
                  ·
                    rfl

theorem cell23_2698098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_2698098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698098 prefixEnd_2698098 := by exact prefixLift 2698098
  have htrace : WordTrace (prefixWord ++ tailWord_2698098) baseStart_2698098 baseEnd_2698098 := by
    simpa [prefixWord, tailWord_2698098, baseEnd_2698098] using wordTrace_append hprefix tailTrace_2698098
  have hstable : (prefixWord ++ tailWord_2698098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698098).length < 2 ^ (prefixWord ++ tailWord_2698098).sum := by decide
  have hdescent : baseEnd_2698098 < baseStart_2698098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698108 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_2698108 : Nat := 118140960795 + 2698108 * 2 ^ 59
def prefixEnd_2698108 : Nat := 4983230072969 + 3 ^ 40 * 2698108 * 2
def baseEnd_2698108 : Nat := 1385426261741234873741633

theorem tailTrace_2698108 : CollatzResearch.WordTrace tailWord_2698108 prefixEnd_2698108 1385426261741234873741633 := by
  unfold tailWord_2698108
  simp only [CollatzResearch.WordTrace]
  refine ⟨49204041654611495502667489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65605388872815327336889985 49204041654611495502667489)
  ·
    refine ⟨36903031240958621627000617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49204041654611495502667489 36903031240958621627000617)
    ·
      refine ⟨27677273430718966220250463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36903031240958621627000617 27677273430718966220250463)
      ·
        refine ⟨41515910146078449330375695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27677273430718966220250463 41515910146078449330375695)
        ·
          refine ⟨62273865219117673995563543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41515910146078449330375695 62273865219117673995563543)
          ·
            refine ⟨93410797828676510993345315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62273865219117673995563543 93410797828676510993345315)
            ·
              refine ⟨140116196743014766490017973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93410797828676510993345315 140116196743014766490017973)
              ·
                refine ⟨13135893444657634358439185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140116196743014766490017973 13135893444657634358439185)
                ·
                  refine ⟨9851920083493225768829389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13135893444657634358439185 9851920083493225768829389)
                  ·
                    refine ⟨3694470031309959663311021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9851920083493225768829389 3694470031309959663311021)
                    ·
                      refine ⟨1385426261741234873741633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3694470031309959663311021 1385426261741234873741633)
                      ·
                        rfl

theorem cell23_2698108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_2698108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698108 prefixEnd_2698108 := by exact prefixLift 2698108
  have htrace : WordTrace (prefixWord ++ tailWord_2698108) baseStart_2698108 baseEnd_2698108 := by
    simpa [prefixWord, tailWord_2698108, baseEnd_2698108] using wordTrace_append hprefix tailTrace_2698108
  have hstable : (prefixWord ++ tailWord_2698108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698108).length < 2 ^ (prefixWord ++ tailWord_2698108).sum := by decide
  have hdescent : baseEnd_2698108 < baseStart_2698108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2698109 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 2, 2, 2]
def baseStart_2698109 : Nat := 118140960795 + 2698109 * 2 ^ 59
def prefixEnd_2698109 : Nat := 4983230072969 + 3 ^ 40 * 2698109 * 2
def baseEnd_2698109 : Nat := 1385426775221889369829129

theorem tailTrace_2698109 : CollatzResearch.WordTrace tailWord_2698109 prefixEnd_2698109 1385426775221889369829129 := by
  unfold tailWord_2698109
  simp only [CollatzResearch.WordTrace]
  refine ⟨98408119782219368176121381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65605413188146245450747587 98408119782219368176121381)
  ·
    refine ⟨18451522459166131533022759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98408119782219368176121381 18451522459166131533022759)
    ·
      refine ⟨27677283688749197299534139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18451522459166131533022759 27677283688749197299534139)
      ·
        refine ⟨41515925533123795949301209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27677283688749197299534139 41515925533123795949301209)
        ·
          refine ⟨31136944149842846961975907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41515925533123795949301209 31136944149842846961975907)
          ·
            refine ⟨46705416224764270442963861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31136944149842846961975907 46705416224764270442963861)
            ·
              refine ⟨2189316385535825177013931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46705416224764270442963861 2189316385535825177013931)
              ·
                refine ⟨3283974578303737765520897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189316385535825177013931 3283974578303737765520897)
                ·
                  refine ⟨2462980933727803324140673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3283974578303737765520897 2462980933727803324140673)
                  ·
                    refine ⟨1847235700295852493105505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2462980933727803324140673 1847235700295852493105505)
                    ·
                      refine ⟨1385426775221889369829129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1847235700295852493105505 1385426775221889369829129)
                      ·
                        rfl

theorem cell23_2698109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_2698109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2698109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2698109 prefixEnd_2698109 := by exact prefixLift 2698109
  have htrace : WordTrace (prefixWord ++ tailWord_2698109) baseStart_2698109 baseEnd_2698109 := by
    simpa [prefixWord, tailWord_2698109, baseEnd_2698109] using wordTrace_append hprefix tailTrace_2698109
  have hstable : (prefixWord ++ tailWord_2698109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2698109).length < 2 ^ (prefixWord ++ tailWord_2698109).sum := by decide
  have hdescent : baseEnd_2698109 < baseStart_2698109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2698109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
