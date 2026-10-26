import V185TrunkScan23Chunk0449

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2661316 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_2661316 : Nat := 118140960795 + 2661316 * 2 ^ 59
def prefixEnd_2661316 : Nat := 4983230072969 + 3 ^ 40 * 2661316 * 2
def baseEnd_2661316 : Nat := 455511427167004940870279

theorem tailTrace_2661316 : CollatzResearch.WordTrace tailWord_2661316 prefixEnd_2661316 455511427167004940870279 := by
  unfold tailWord_2661316
  simp only [CollatzResearch.WordTrace]
  refine ⟨48533084413257061715997901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64710779217676082287997201 48533084413257061715997901)
  ·
    refine ⟨18199906654971398143499213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48533084413257061715997901 18199906654971398143499213)
    ·
      refine ⟨6824964995614274303812205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18199906654971398143499213 6824964995614274303812205)
      ·
        refine ⟨2559361873355352863929577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6824964995614274303812205 2559361873355352863929577)
        ·
          refine ⟨1919521405016514647947183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2559361873355352863929577 1919521405016514647947183)
          ·
            refine ⟨2879282107524771971920775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919521405016514647947183 2879282107524771971920775)
            ·
              refine ⟨4318923161287157957881163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879282107524771971920775 4318923161287157957881163)
              ·
                refine ⟨6478384741930736936821745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4318923161287157957881163 6478384741930736936821745)
                ·
                  refine ⟨4858788556448052702616309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6478384741930736936821745 4858788556448052702616309)
                  ·
                    refine ⟨455511427167004940870279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4858788556448052702616309 455511427167004940870279)
                    ·
                      rfl

theorem cell23_2661316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_2661316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661316 prefixEnd_2661316 := by exact prefixLift 2661316
  have htrace : WordTrace (prefixWord ++ tailWord_2661316) baseStart_2661316 baseEnd_2661316 := by
    simpa [prefixWord, tailWord_2661316, baseEnd_2661316] using wordTrace_append hprefix tailTrace_2661316
  have hstable : (prefixWord ++ tailWord_2661316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661316).length < 2 ^ (prefixWord ++ tailWord_2661316).sum := by decide
  have hdescent : baseEnd_2661316 < baseStart_2661316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661346 : List Nat := [3, 3, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2661346 : Nat := 118140960795 + 2661346 * 2 ^ 59
def prefixEnd_2661346 : Nat := 4983230072969 + 3 ^ 40 * 2661346 * 2
def baseEnd_2661346 : Nat := 455516561973549901745233

theorem tailTrace_2661346 : CollatzResearch.WordTrace tailWord_2661346 prefixEnd_2661346 455516561973549901745233 := by
  unfold tailWord_2661346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24266815754101359638896973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64711508677603625703725261 24266815754101359638896973)
  ·
    refine ⟨9100055907788009864586365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24266815754101359638896973 9100055907788009864586365)
    ·
      refine ⟨3412520965420503699219887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9100055907788009864586365 3412520965420503699219887)
      ·
        refine ⟨5118781448130755548829831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3412520965420503699219887 5118781448130755548829831)
        ·
          refine ⟨7678172172196133323244747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5118781448130755548829831 7678172172196133323244747)
          ·
            refine ⟨11517258258294199984867121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7678172172196133323244747 11517258258294199984867121)
            ·
              refine ⟨8637943693720649988650341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11517258258294199984867121 8637943693720649988650341)
              ·
                refine ⟨1619614442572621872871939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8637943693720649988650341 1619614442572621872871939)
                ·
                  refine ⟨2429421663858932809307909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619614442572621872871939 2429421663858932809307909)
                  ·
                    refine ⟨455516561973549901745233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2429421663858932809307909 455516561973549901745233)
                    ·
                      rfl

theorem cell23_2661346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2661346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661346 prefixEnd_2661346 := by exact prefixLift 2661346
  have htrace : WordTrace (prefixWord ++ tailWord_2661346) baseStart_2661346 baseEnd_2661346 := by
    simpa [prefixWord, tailWord_2661346, baseEnd_2661346] using wordTrace_append hprefix tailTrace_2661346
  have hstable : (prefixWord ++ tailWord_2661346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661346).length < 2 ^ (prefixWord ++ tailWord_2661346).sum := by decide
  have hdescent : baseEnd_2661346 < baseStart_2661346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661348 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_2661348 : Nat := 118140960795 + 2661348 * 2 ^ 59
def prefixEnd_2661348 : Nat := 4983230072969 + 3 ^ 40 * 2661348 * 2
def baseEnd_2661348 : Nat := 1366550712881958697410689

theorem tailTrace_2661348 : CollatzResearch.WordTrace tailWord_2661348 prefixEnd_2661348 1366550712881958697410689 := by
  unfold tailWord_2661348
  simp only [CollatzResearch.WordTrace]
  refine ⟨48533667981199096448580349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64711557308265461931440465 48533667981199096448580349)
  ·
    refine ⟨18200125492949661168217631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48533667981199096448580349 18200125492949661168217631)
    ·
      refine ⟨27300188239424491752326447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18200125492949661168217631 27300188239424491752326447)
      ·
        refine ⟨40950282359136737628489671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27300188239424491752326447 40950282359136737628489671)
        ·
          refine ⟨61425423538705106442734507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40950282359136737628489671 61425423538705106442734507)
          ·
            refine ⟨92138135308057659664101761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61425423538705106442734507 92138135308057659664101761)
            ·
              refine ⟨69103601481043244748076321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92138135308057659664101761 69103601481043244748076321)
              ·
                refine ⟨51827701110782433561057241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69103601481043244748076321 51827701110782433561057241)
                ·
                  refine ⟨38870775833086825170792931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51827701110782433561057241 38870775833086825170792931)
                  ·
                    refine ⟨58306163749630237756189397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38870775833086825170792931 58306163749630237756189397)
                    ·
                      refine ⟨1366550712881958697410689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58306163749630237756189397 1366550712881958697410689)
                      ·
                        rfl

theorem cell23_2661348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_2661348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661348 prefixEnd_2661348 := by exact prefixLift 2661348
  have htrace : WordTrace (prefixWord ++ tailWord_2661348) baseStart_2661348 baseEnd_2661348 := by
    simpa [prefixWord, tailWord_2661348, baseEnd_2661348] using wordTrace_append hprefix tailTrace_2661348
  have hstable : (prefixWord ++ tailWord_2661348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661348).length < 2 ^ (prefixWord ++ tailWord_2661348).sum := by decide
  have hdescent : baseEnd_2661348 < baseStart_2661348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661352 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_2661352 : Nat := 118140960795 + 2661352 * 2 ^ 59
def prefixEnd_2661352 : Nat := 4983230072969 + 3 ^ 40 * 2661352 * 2
def baseEnd_2661352 : Nat := 1366552766804576681760671

theorem tailTrace_2661352 : CollatzResearch.WordTrace tailWord_2661352 prefixEnd_2661352 1366552766804576681760671 := by
  unfold tailWord_2661352
  simp only [CollatzResearch.WordTrace]
  refine ⟨48533740927191850790153155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64711654569589134386870873 48533740927191850790153155)
  ·
    refine ⟨72800611390787776185229733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48533740927191850790153155 72800611390787776185229733)
    ·
      refine ⟨13650114635772708034730575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72800611390787776185229733 13650114635772708034730575)
      ·
        refine ⟨20475171953659062052095863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13650114635772708034730575 20475171953659062052095863)
        ·
          refine ⟨30712757930488593078143795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20475171953659062052095863 30712757930488593078143795)
          ·
            refine ⟨46069136895732889617215693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30712757930488593078143795 46069136895732889617215693)
            ·
              refine ⟨17275926335899833606455885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46069136895732889617215693 17275926335899833606455885)
              ·
                refine ⟨6478472375962437602420957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17275926335899833606455885 6478472375962437602420957)
                ·
                  refine ⟨2429427140985914100907859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6478472375962437602420957 2429427140985914100907859)
                  ·
                    refine ⟨3644140711478871151361789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2429427140985914100907859 3644140711478871151361789)
                    ·
                      refine ⟨1366552766804576681760671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3644140711478871151361789 1366552766804576681760671)
                      ·
                        rfl

theorem cell23_2661352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_2661352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661352 prefixEnd_2661352 := by exact prefixLift 2661352
  have htrace : WordTrace (prefixWord ++ tailWord_2661352) baseStart_2661352 baseEnd_2661352 := by
    simpa [prefixWord, tailWord_2661352, baseEnd_2661352] using wordTrace_append hprefix tailTrace_2661352
  have hstable : (prefixWord ++ tailWord_2661352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661352).length < 2 ^ (prefixWord ++ tailWord_2661352).sum := by decide
  have hdescent : baseEnd_2661352 < baseStart_2661352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661372 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_2661372 : Nat := 118140960795 + 2661372 * 2 ^ 59
def prefixEnd_2661372 : Nat := 4983230072969 + 3 ^ 40 * 2661372 * 2
def baseEnd_2661372 : Nat := 455521012139222201170193

theorem tailTrace_2661372 : CollatzResearch.WordTrace tailWord_2661372 prefixEnd_2661372 455521012139222201170193 := by
  unfold tailWord_2661372
  simp only [CollatzResearch.WordTrace]
  refine ⟨48534105657155622498017185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64712140876207496664022913 48534105657155622498017185)
  ·
    refine ⟨36400579242866716873512889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48534105657155622498017185 36400579242866716873512889)
    ·
      refine ⟨27300434432150037655134667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36400579242866716873512889 27300434432150037655134667)
      ·
        refine ⟨40950651648225056482702001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27300434432150037655134667 40950651648225056482702001)
        ·
          refine ⟨30712988736168792362026501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40950651648225056482702001 30712988736168792362026501)
          ·
            refine ⟨5758685388031648567879969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30712988736168792362026501 5758685388031648567879969)
            ·
              refine ⟨4319014041023736425909977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5758685388031648567879969 4319014041023736425909977)
              ·
                refine ⟨3239260530767802319432483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4319014041023736425909977 3239260530767802319432483)
                ·
                  refine ⟨4858890796151703479148725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239260530767802319432483 4858890796151703479148725)
                  ·
                    refine ⟨455521012139222201170193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4858890796151703479148725 455521012139222201170193)
                    ·
                      rfl

theorem cell23_2661372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_2661372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661372 prefixEnd_2661372 := by exact prefixLift 2661372
  have htrace : WordTrace (prefixWord ++ tailWord_2661372) baseStart_2661372 baseEnd_2661372 := by
    simpa [prefixWord, tailWord_2661372, baseEnd_2661372] using wordTrace_append hprefix tailTrace_2661372
  have hstable : (prefixWord ++ tailWord_2661372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661372).length < 2 ^ (prefixWord ++ tailWord_2661372).sum := by decide
  have hdescent : baseEnd_2661372 < baseStart_2661372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661386 : List Nat := [3, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3]
def baseStart_2661386 : Nat := 118140960795 + 2661386 * 2 ^ 59
def prefixEnd_2661386 : Nat := 4983230072969 + 3 ^ 40 * 2661386 * 2
def baseEnd_2661386 : Nat := 1366570225146829548735515

theorem tailTrace_2661386 : CollatzResearch.WordTrace tailWord_2661386 prefixEnd_2661386 1366570225146829548735515 := by
  unfold tailWord_2661386
  simp only [CollatzResearch.WordTrace]
  refine ⟨24267180484065131346761003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64712481290840350258029341 24267180484065131346761003)
  ·
    refine ⟨36400770726097697020141505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24267180484065131346761003 36400770726097697020141505)
    ·
      refine ⟨27300578044573272765106129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36400770726097697020141505 27300578044573272765106129)
      ·
        refine ⟨20475433533429954573829597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27300578044573272765106129 20475433533429954573829597)
        ·
          refine ⟨7678287575036232965186099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20475433533429954573829597 7678287575036232965186099)
          ·
            refine ⟨11517431362554349447779149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7678287575036232965186099 11517431362554349447779149)
            ·
              refine ⟨4319036760957881042917181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11517431362554349447779149 4319036760957881042917181)
              ·
                refine ⟨1619638785359205391093943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4319036760957881042917181 1619638785359205391093943)
                ·
                  refine ⟨2429458178038808086640915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619638785359205391093943 2429458178038808086640915)
                  ·
                    refine ⟨3644187267058212129961373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2429458178038808086640915 3644187267058212129961373)
                    ·
                      refine ⟨1366570225146829548735515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3644187267058212129961373 1366570225146829548735515)
                      ·
                        rfl

theorem cell23_2661386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_2661386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661386 prefixEnd_2661386 := by exact prefixLift 2661386
  have htrace : WordTrace (prefixWord ++ tailWord_2661386) baseStart_2661386 baseEnd_2661386 := by
    simpa [prefixWord, tailWord_2661386, baseEnd_2661386] using wordTrace_append hprefix tailTrace_2661386
  have hstable : (prefixWord ++ tailWord_2661386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661386).length < 2 ^ (prefixWord ++ tailWord_2661386).sum := by decide
  have hdescent : baseEnd_2661386 < baseStart_2661386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661395 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 3]
def baseStart_2661395 : Nat := 118140960795 + 2661395 * 2 ^ 59
def prefixEnd_2661395 : Nat := 4983230072969 + 3 ^ 40 * 2661395 * 2
def baseEnd_2661395 : Nat := 1366574846472720013522973

theorem tailTrace_2661395 : CollatzResearch.WordTrace tailWord_2661395 prefixEnd_2661395 1366574846472720013522973 := by
  unfold tailWord_2661395
  simp only [CollatzResearch.WordTrace]
  refine ⟨97069050193227919924121639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64712700128818613282747759 97069050193227919924121639)
  ·
    refine ⟨145603575289841879886182459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97069050193227919924121639 145603575289841879886182459)
    ·
      refine ⟨218405362934762819829273689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145603575289841879886182459 218405362934762819829273689)
      ·
        refine ⟨163804022201072114871955267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218405362934762819829273689 163804022201072114871955267)
        ·
          refine ⟨245706033301608172307932901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163804022201072114871955267 245706033301608172307932901)
          ·
            refine ⟨46069881244051532307737419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245706033301608172307932901 46069881244051532307737419)
            ·
              refine ⟨69104821866077298461606129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46069881244051532307737419 69104821866077298461606129)
              ·
                refine ⟨51828616399557973846204597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69104821866077298461606129 51828616399557973846204597)
                ·
                  refine ⟨4858932787458560048081681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51828616399557973846204597 4858932787458560048081681)
                  ·
                    refine ⟨3644199590593920036061261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4858932787458560048081681 3644199590593920036061261)
                    ·
                      refine ⟨1366574846472720013522973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3644199590593920036061261 1366574846472720013522973)
                      ·
                        rfl

theorem cell23_2661395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 3].length) (baseStart_2661395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661395 prefixEnd_2661395 := by exact prefixLift 2661395
  have htrace : WordTrace (prefixWord ++ tailWord_2661395) baseStart_2661395 baseEnd_2661395 := by
    simpa [prefixWord, tailWord_2661395, baseEnd_2661395] using wordTrace_append hprefix tailTrace_2661395
  have hstable : (prefixWord ++ tailWord_2661395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661395).length < 2 ^ (prefixWord ++ tailWord_2661395).sum := by decide
  have hdescent : baseEnd_2661395 < baseStart_2661395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661402 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_2661402 : Nat := 118140960795 + 2661402 * 2 ^ 59
def prefixEnd_2661402 : Nat := 4983230072969 + 3 ^ 40 * 2661402 * 2
def baseEnd_2661402 : Nat := 455526146945767162045147

theorem tailTrace_2661402 : CollatzResearch.WordTrace tailWord_2661402 prefixEnd_2661402 455526146945767162045147 := by
  unfold tailWord_2661402
  simp only [CollatzResearch.WordTrace]
  refine ⟨24267326376050640029906615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64712870336135040079750973 24267326376050640029906615)
  ·
    refine ⟨36400989564075960044859923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24267326376050640029906615 36400989564075960044859923)
    ·
      refine ⟨54601484346113940067289885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36400989564075960044859923 54601484346113940067289885)
      ·
        refine ⟨20475556629792727525233707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54601484346113940067289885 20475556629792727525233707)
        ·
          refine ⟨30713334944689091287850561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20475556629792727525233707 30713334944689091287850561)
          ·
            refine ⟨23035001208516818465887921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30713334944689091287850561 23035001208516818465887921)
            ·
              refine ⟨17276250906387613849415941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23035001208516818465887921 17276250906387613849415941)
              ·
                refine ⟨3239297044947677596765489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17276250906387613849415941 3239297044947677596765489)
                ·
                  refine ⟨2429472783710758197574117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3239297044947677596765489 2429472783710758197574117)
                  ·
                    refine ⟨455526146945767162045147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2429472783710758197574117 455526146945767162045147)
                    ·
                      rfl

theorem cell23_2661402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_2661402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661402 prefixEnd_2661402 := by exact prefixLift 2661402
  have htrace : WordTrace (prefixWord ++ tailWord_2661402) baseStart_2661402 baseEnd_2661402 := by
    simpa [prefixWord, tailWord_2661402, baseEnd_2661402] using wordTrace_append hprefix tailTrace_2661402
  have hstable : (prefixWord ++ tailWord_2661402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661402).length < 2 ^ (prefixWord ++ tailWord_2661402).sum := by decide
  have hdescent : baseEnd_2661402 < baseStart_2661402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661412 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2661412 : Nat := 118140960795 + 2661412 * 2 ^ 59
def prefixEnd_2661412 : Nat := 4983230072969 + 3 ^ 40 * 2661412 * 2
def baseEnd_2661412 : Nat := 1366583575643846447010395

theorem tailTrace_2661412 : CollatzResearch.WordTrace tailWord_2661412 prefixEnd_2661412 1366583575643846447010395 := by
  unfold tailWord_2661412
  simp only [CollatzResearch.WordTrace]
  refine ⟨48534835117083165913745245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64713113489444221218326993 48534835117083165913745245)
  ·
    refine ⟨18200563168906187217654467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48534835117083165913745245 18200563168906187217654467)
    ·
      refine ⟨27300844753359280826481701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18200563168906187217654467 27300844753359280826481701)
      ·
        refine ⟨5118908391254865154965319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27300844753359280826481701 5118908391254865154965319)
        ·
          refine ⟨7678362586882297732447979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5118908391254865154965319 7678362586882297732447979)
          ·
            refine ⟨11517543880323446598671969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7678362586882297732447979 11517543880323446598671969)
            ·
              refine ⟨8638157910242584949003977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11517543880323446598671969 8638157910242584949003977)
              ·
                refine ⟨6478618432681938711752983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8638157910242584949003977 6478618432681938711752983)
                ·
                  refine ⟨9717927649022908067629475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6478618432681938711752983 9717927649022908067629475)
                  ·
                    refine ⟨14576891473534362101444213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9717927649022908067629475 14576891473534362101444213)
                    ·
                      refine ⟨1366583575643846447010395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14576891473534362101444213 1366583575643846447010395)
                      ·
                        rfl

theorem cell23_2661412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2661412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661412 prefixEnd_2661412 := by exact prefixLift 2661412
  have htrace : WordTrace (prefixWord ++ tailWord_2661412) baseStart_2661412 baseEnd_2661412 := by
    simpa [prefixWord, tailWord_2661412, baseEnd_2661412] using wordTrace_append hprefix tailTrace_2661412
  have hstable : (prefixWord ++ tailWord_2661412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661412).length < 2 ^ (prefixWord ++ tailWord_2661412).sum := by decide
  have hdescent : baseEnd_2661412 < baseStart_2661412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661422 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2661422 : Nat := 118140960795 + 2661422 * 2 ^ 59
def prefixEnd_2661422 : Nat := 4983230072969 + 3 ^ 40 * 2661422 * 2
def baseEnd_2661422 : Nat := 1366588710450391407885349

theorem tailTrace_2661422 : CollatzResearch.WordTrace tailWord_2661422 prefixEnd_2661422 1366588710450391407885349 := by
  unfold tailWord_2661422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12133754370516262941919315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64713356642753402356903013 12133754370516262941919315)
  ·
    refine ⟨18200631555774394412878973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12133754370516262941919315 18200631555774394412878973)
    ·
      refine ⟨6825236833415397904829615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18200631555774394412878973 6825236833415397904829615)
      ·
        refine ⟨10237855250123096857244423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6825236833415397904829615 10237855250123096857244423)
        ·
          refine ⟨15356782875184645285866635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10237855250123096857244423 15356782875184645285866635)
          ·
            refine ⟨23035174312776967928799953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15356782875184645285866635 23035174312776967928799953)
            ·
              refine ⟨17276380734582725946599965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23035174312776967928799953 17276380734582725946599965)
              ·
                refine ⟨6478642775468522229974987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17276380734582725946599965 6478642775468522229974987)
                ·
                  refine ⟨9717964163202783344962481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6478642775468522229974987 9717964163202783344962481)
                  ·
                    refine ⟨7288473122402087508721861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9717964163202783344962481 7288473122402087508721861)
                    ·
                      refine ⟨1366588710450391407885349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7288473122402087508721861 1366588710450391407885349)
                      ·
                        rfl

theorem cell23_2661422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2661422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661422 prefixEnd_2661422 := by exact prefixLift 2661422
  have htrace : WordTrace (prefixWord ++ tailWord_2661422) baseStart_2661422 baseEnd_2661422 := by
    simpa [prefixWord, tailWord_2661422, baseEnd_2661422] using wordTrace_append hprefix tailTrace_2661422
  have hstable : (prefixWord ++ tailWord_2661422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661422).length < 2 ^ (prefixWord ++ tailWord_2661422).sum := by decide
  have hdescent : baseEnd_2661422 < baseStart_2661422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661446 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2661446 : Nat := 118140960795 + 2661446 * 2 ^ 59
def prefixEnd_2661446 : Nat := 4983230072969 + 3 ^ 40 * 2661446 * 2
def baseEnd_2661446 : Nat := 1366601033986099313985239

theorem tailTrace_2661446 : CollatzResearch.WordTrace tailWord_2661446 prefixEnd_2661446 1366601033986099313985239 := by
  unfold tailWord_2661446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3033465947376348613569631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64713940210695437089485461 3033465947376348613569631)
  ·
    refine ⟨4550198921064522920354447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3033465947376348613569631 4550198921064522920354447)
    ·
      refine ⟨6825298381596784380531671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4550198921064522920354447 6825298381596784380531671)
      ·
        refine ⟨10237947572395176570797507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6825298381596784380531671 10237947572395176570797507)
        ·
          refine ⟨15356921358592764856196261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10237947572395176570797507 15356921358592764856196261)
          ·
            refine ⟨2879422754736143410536799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15356921358592764856196261 2879422754736143410536799)
            ·
              refine ⟨4319134132104215115805199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879422754736143410536799 4319134132104215115805199)
              ·
                refine ⟨6478701198156322673707799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4319134132104215115805199 6478701198156322673707799)
                ·
                  refine ⟨9718051797234484010561699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6478701198156322673707799 9718051797234484010561699)
                  ·
                    refine ⟨14577077695851726015842549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9718051797234484010561699 14577077695851726015842549)
                    ·
                      refine ⟨1366601033986099313985239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14577077695851726015842549 1366601033986099313985239)
                      ·
                        rfl

theorem cell23_2661446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2661446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661446 prefixEnd_2661446 := by exact prefixLift 2661446
  have htrace : WordTrace (prefixWord ++ tailWord_2661446) baseStart_2661446 baseEnd_2661446 := by
    simpa [prefixWord, tailWord_2661446, baseEnd_2661446] using wordTrace_append hprefix tailTrace_2661446
  have hstable : (prefixWord ++ tailWord_2661446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661446).length < 2 ^ (prefixWord ++ tailWord_2661446).sum := by decide
  have hdescent : baseEnd_2661446 < baseStart_2661446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661495 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_2661495 : Nat := 118140960795 + 2661495 * 2 ^ 59
def prefixEnd_2661495 : Nat := 4983230072969 + 3 ^ 40 * 2661495 * 2
def baseEnd_2661495 : Nat := 1366626194538169622272513

theorem tailTrace_2661495 : CollatzResearch.WordTrace tailWord_2661495 prefixEnd_2661495 1366626194538169622272513 := by
  unfold tailWord_2661495
  simp only [CollatzResearch.WordTrace]
  refine ⟨97072697492865637002761939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64715131661910424668507959 97072697492865637002761939)
  ·
    refine ⟨145609046239298455504142909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97072697492865637002761939 145609046239298455504142909)
    ·
      refine ⟨54603392339736920814053591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145609046239298455504142909 54603392339736920814053591)
      ·
        refine ⟨81905088509605381221080387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54603392339736920814053591 81905088509605381221080387)
        ·
          refine ⟨122857632764408071831620581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81905088509605381221080387 122857632764408071831620581)
          ·
            refine ⟨23035806143326513468428859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122857632764408071831620581 23035806143326513468428859)
            ·
              refine ⟨34553709214989770202643289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23035806143326513468428859 34553709214989770202643289)
              ·
                refine ⟨25915281911242327651982467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34553709214989770202643289 25915281911242327651982467)
                ·
                  refine ⟨38872922866863491477973701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25915281911242327651982467 38872922866863491477973701)
                  ·
                    refine ⟨7288673037536904652120069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38872922866863491477973701 7288673037536904652120069)
                    ·
                      refine ⟨1366626194538169622272513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7288673037536904652120069 1366626194538169622272513)
                      ·
                        rfl

theorem cell23_2661495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_2661495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661495 prefixEnd_2661495 := by exact prefixLift 2661495
  have htrace : WordTrace (prefixWord ++ tailWord_2661495) baseStart_2661495 baseEnd_2661495 := by
    simpa [prefixWord, tailWord_2661495, baseEnd_2661495] using wordTrace_append hprefix tailTrace_2661495
  have hstable : (prefixWord ++ tailWord_2661495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661495).length < 2 ^ (prefixWord ++ tailWord_2661495).sum := by decide
  have hdescent : baseEnd_2661495 < baseStart_2661495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661522 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 7]
def baseStart_2661522 : Nat := 118140960795 + 2661522 * 2 ^ 59
def prefixEnd_2661522 : Nat := 4983230072969 + 3 ^ 40 * 2661522 * 2
def baseEnd_2661522 : Nat := 151848895390649001848321

theorem tailTrace_2661522 : CollatzResearch.WordTrace tailWord_2661522 prefixEnd_2661522 151848895390649001848321 := by
  unfold tailWord_2661522
  simp only [CollatzResearch.WordTrace]
  refine ⟨24268420565941955153498705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64715788175845213742663213 24268420565941955153498705)
  ·
    refine ⟨18201315424456466365124029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24268420565941955153498705 18201315424456466365124029)
    ·
      refine ⟨6825493284171174886921511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18201315424456466365124029 6825493284171174886921511)
      ·
        refine ⟨10238239926256762330382267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6825493284171174886921511 10238239926256762330382267)
        ·
          refine ⟨15357359889385143495573401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10238239926256762330382267 15357359889385143495573401)
          ·
            refine ⟨11518019917038857621680051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15357359889385143495573401 11518019917038857621680051)
            ·
              refine ⟨17277029875558286432520077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11518019917038857621680051 17277029875558286432520077)
              ·
                refine ⟨6478886203334357412195029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17277029875558286432520077 6478886203334357412195029)
                ·
                  refine ⟨151848895390649001848321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6478886203334357412195029 151848895390649001848321)
                  ·
                    rfl

theorem cell23_2661522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_2661522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661522 prefixEnd_2661522 := by exact prefixLift 2661522
  have htrace : WordTrace (prefixWord ++ tailWord_2661522) baseStart_2661522 baseEnd_2661522 := by
    simpa [prefixWord, tailWord_2661522, baseEnd_2661522] using wordTrace_append hprefix tailTrace_2661522
  have hstable : (prefixWord ++ tailWord_2661522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661522).length < 2 ^ (prefixWord ++ tailWord_2661522).sum := by decide
  have hdescent : baseEnd_2661522 < baseStart_2661522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661533 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_2661533 : Nat := 118140960795 + 2661533 * 2 ^ 59
def prefixEnd_2661533 : Nat := 4983230072969 + 3 ^ 40 * 2661533 * 2
def baseEnd_2661533 : Nat := 1366645706803040473597339

theorem tailTrace_2661533 : CollatzResearch.WordTrace tailWord_2661533 prefixEnd_2661533 1366645706803040473597339 := by
  unfold tailWord_2661533
  simp only [CollatzResearch.WordTrace]
  refine ⟨97074083466727969492645253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64716055644485312995096835 97074083466727969492645253)
  ·
    refine ⟨18201390650011494279870985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97074083466727969492645253 18201390650011494279870985)
    ·
      refine ⟨13651042987508620709903239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18201390650011494279870985 13651042987508620709903239)
      ·
        refine ⟨20476564481262931064854859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13651042987508620709903239 20476564481262931064854859)
        ·
          refine ⟨30714846721894396597282289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20476564481262931064854859 30714846721894396597282289)
          ·
            refine ⟨23036135041420797447961717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30714846721894396597282289 23036135041420797447961717)
            ·
              refine ⟨2159637660133199760746411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23036135041420797447961717 2159637660133199760746411)
              ·
                refine ⟨3239456490199799641119617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159637660133199760746411 3239456490199799641119617)
                ·
                  refine ⟨2429592367649849730839713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3239456490199799641119617 2429592367649849730839713)
                  ·
                    refine ⟨1822194275737387298129785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2429592367649849730839713 1822194275737387298129785)
                    ·
                      refine ⟨1366645706803040473597339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822194275737387298129785 1366645706803040473597339)
                      ·
                        rfl

theorem cell23_2661533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_2661533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661533 prefixEnd_2661533 := by exact prefixLift 2661533
  have htrace : WordTrace (prefixWord ++ tailWord_2661533) baseStart_2661533 baseEnd_2661533 := by
    simpa [prefixWord, tailWord_2661533, baseEnd_2661533] using wordTrace_append hprefix tailTrace_2661533
  have hstable : (prefixWord ++ tailWord_2661533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661533).length < 2 ^ (prefixWord ++ tailWord_2661533).sum := by decide
  have hdescent : baseEnd_2661533 < baseStart_2661533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661569 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2661569 : Nat := 118140960795 + 2661569 * 2 ^ 59
def prefixEnd_2661569 : Nat := 4983230072969 + 3 ^ 40 * 2661569 * 2
def baseEnd_2661569 : Nat := 455554730702200777582391

theorem tailTrace_2661569 : CollatzResearch.WordTrace tailWord_2661569 prefixEnd_2661569 455554730702200777582391 := by
  unfold tailWord_2661569
  simp only [CollatzResearch.WordTrace]
  refine ⟨97075396494597547640955761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64716930996398365093970507 97075396494597547640955761)
  ·
    refine ⟨72806547370948160730716821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97075396494597547640955761 72806547370948160730716821)
    ·
      refine ⟨3412806908013195034252351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72806547370948160730716821 3412806908013195034252351)
      ·
        refine ⟨5119210362019792551378527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3412806908013195034252351 5119210362019792551378527)
        ·
          refine ⟨7678815543029688827067791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119210362019792551378527 7678815543029688827067791)
          ·
            refine ⟨11518223314544533240601687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7678815543029688827067791 11518223314544533240601687)
            ·
              refine ⟨17277334971816799860902531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11518223314544533240601687 17277334971816799860902531)
              ·
                refine ⟨25916002457725199791353797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17277334971816799860902531 25916002457725199791353797)
                ·
                  refine ⟨4859250460823474960878837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25916002457725199791353797 4859250460823474960878837)
                  ·
                    refine ⟨455554730702200777582391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4859250460823474960878837 455554730702200777582391)
                    ·
                      rfl

theorem cell23_2661569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2661569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661569 prefixEnd_2661569 := by exact prefixLift 2661569
  have htrace : WordTrace (prefixWord ++ tailWord_2661569) baseStart_2661569 baseEnd_2661569 := by
    simpa [prefixWord, tailWord_2661569, baseEnd_2661569] using wordTrace_append hprefix tailTrace_2661569
  have hstable : (prefixWord ++ tailWord_2661569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661569).length < 2 ^ (prefixWord ++ tailWord_2661569).sum := by decide
  have hdescent : baseEnd_2661569 < baseStart_2661569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661633 : List Nat := [1, 2, 4, 1, 1, 3, 4, 2, 1, 4]
def baseStart_2661633 : Nat := 118140960795 + 2661633 * 2 ^ 59
def prefixEnd_2661633 : Nat := 4983230072969 + 3 ^ 40 * 2661633 * 2
def baseEnd_2661633 : Nat := 455565684956163360782293

theorem tailTrace_2661633 : CollatzResearch.WordTrace tailWord_2661633 prefixEnd_2661633 455565684956163360782293 := by
  unfold tailWord_2661633
  simp only [CollatzResearch.WordTrace]
  refine ⟨97077730766365686571285553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64718487177577124380857035 97077730766365686571285553)
  ·
    refine ⟨72808298074774264928464165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97077730766365686571285553 72808298074774264928464165)
    ·
      refine ⟨13651555889020174674087031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72808298074774264928464165 13651555889020174674087031)
      ·
        refine ⟨20477333833530262011130547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13651555889020174674087031 20477333833530262011130547)
        ·
          refine ⟨30716000750295393016695821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20477333833530262011130547 30716000750295393016695821)
          ·
            refine ⟨11518500281360772381260933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30716000750295393016695821 11518500281360772381260933)
            ·
              refine ⟨2159718802755144821486425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11518500281360772381260933 2159718802755144821486425)
              ·
                refine ⟨1619789102066358616114819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2159718802755144821486425 1619789102066358616114819)
                ·
                  refine ⟨2429683653099537924172229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619789102066358616114819 2429683653099537924172229)
                  ·
                    refine ⟨455565684956163360782293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2429683653099537924172229 455565684956163360782293)
                    ·
                      rfl

theorem cell23_2661633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_2661633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661633 prefixEnd_2661633 := by exact prefixLift 2661633
  have htrace : WordTrace (prefixWord ++ tailWord_2661633) baseStart_2661633 baseEnd_2661633 := by
    simpa [prefixWord, tailWord_2661633, baseEnd_2661633] using wordTrace_append hprefix tailTrace_2661633
  have hstable : (prefixWord ++ tailWord_2661633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661633).length < 2 ^ (prefixWord ++ tailWord_2661633).sum := by decide
  have hdescent : baseEnd_2661633 < baseStart_2661633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661649 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 1, 5, 2]
def baseStart_2661649 : Nat := 118140960795 + 2661649 * 2 ^ 59
def prefixEnd_2661649 : Nat := 4983230072969 + 3 ^ 40 * 2661649 * 2
def baseEnd_2661649 : Nat := 1366705270558962019746805

theorem tailTrace_2661649 : CollatzResearch.WordTrace tailWord_2661649 prefixEnd_2661649 1366705270558962019746805 := by
  unfold tailWord_2661649
  simp only [CollatzResearch.WordTrace]
  refine ⟨97078314334307721303868001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64718876222871814202578667 97078314334307721303868001)
  ·
    refine ⟨72808735750730790977901001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97078314334307721303868001 72808735750730790977901001)
    ·
      refine ⟨54606551813048093233425751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72808735750730790977901001 54606551813048093233425751)
      ·
        refine ⟨81909827719572139850138627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54606551813048093233425751 81909827719572139850138627)
        ·
          refine ⟨122864741579358209775207941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81909827719572139850138627 122864741579358209775207941)
          ·
            refine ⟨23037139046129664332851489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122864741579358209775207941 23037139046129664332851489)
            ·
              refine ⟨17277854284597248249638617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23037139046129664332851489 17277854284597248249638617)
              ·
                refine ⟨12958390713447936187228963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17277854284597248249638617 12958390713447936187228963)
                ·
                  refine ⟨19437586070171904280843445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12958390713447936187228963 19437586070171904280843445)
                  ·
                    refine ⟨1822273694078616026329073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19437586070171904280843445 1822273694078616026329073)
                    ·
                      refine ⟨1366705270558962019746805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822273694078616026329073 1366705270558962019746805)
                      ·
                        rfl

theorem cell23_2661649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_2661649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661649 prefixEnd_2661649 := by exact prefixLift 2661649
  have htrace : WordTrace (prefixWord ++ tailWord_2661649) baseStart_2661649 baseEnd_2661649 := by
    simpa [prefixWord, tailWord_2661649, baseEnd_2661649] using wordTrace_append hprefix tailTrace_2661649
  have hstable : (prefixWord ++ tailWord_2661649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661649).length < 2 ^ (prefixWord ++ tailWord_2661649).sum := by decide
  have hdescent : baseEnd_2661649 < baseStart_2661649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661656 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 3, 1, 3]
def baseStart_2661656 : Nat := 118140960795 + 2661656 * 2 ^ 59
def prefixEnd_2661656 : Nat := 4983230072969 + 3 ^ 40 * 2661656 * 2
def baseEnd_2661656 : Nat := 1366708864923543492359273

theorem tailTrace_2661656 : CollatzResearch.WordTrace tailWord_2661656 prefixEnd_2661656 1366708864923543492359273 := by
  unfold tailWord_2661656
  simp only [CollatzResearch.WordTrace]
  refine ⟨48539284822641180749686411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64719046430188240999581881 48539284822641180749686411)
  ·
    refine ⟨72808927233961771124529617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48539284822641180749686411 72808927233961771124529617)
    ·
      refine ⟨54606695425471328343397213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72808927233961771124529617 54606695425471328343397213)
      ·
        refine ⟨20477510784551748128773955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54606695425471328343397213 20477510784551748128773955)
        ·
          refine ⟨30716266176827622193160933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20477510784551748128773955 30716266176827622193160933)
          ·
            refine ⟨5759299908155179161217675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30716266176827622193160933 5759299908155179161217675)
            ·
              refine ⟨8638949862232768741826513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5759299908155179161217675 8638949862232768741826513)
              ·
                refine ⟨6479212396674576556369885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8638949862232768741826513 6479212396674576556369885)
                ·
                  refine ⟨2429704648752966208638707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6479212396674576556369885 2429704648752966208638707)
                  ·
                    refine ⟨3644556973129449312958061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2429704648752966208638707 3644556973129449312958061)
                    ·
                      refine ⟨1366708864923543492359273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3644556973129449312958061 1366708864923543492359273)
                      ·
                        rfl

theorem cell23_2661656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_2661656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661656 prefixEnd_2661656 := by exact prefixLift 2661656
  have htrace : WordTrace (prefixWord ++ tailWord_2661656) baseStart_2661656 baseEnd_2661656 := by
    simpa [prefixWord, tailWord_2661656, baseEnd_2661656] using wordTrace_append hprefix tailTrace_2661656
  have hstable : (prefixWord ++ tailWord_2661656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661656).length < 2 ^ (prefixWord ++ tailWord_2661656).sum := by decide
  have hdescent : baseEnd_2661656 < baseStart_2661656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661719 : List Nat := [1, 1, 3, 2, 3, 2, 4, 7]
def baseStart_2661719 : Nat := 118140960795 + 2661719 * 2 ^ 59
def prefixEnd_2661719 : Nat := 4983230072969 + 3 ^ 40 * 2661719 * 2
def baseEnd_2661719 : Nat := 50620044970547286884129

theorem tailTrace_2661719 : CollatzResearch.WordTrace tailWord_2661719 prefixEnd_2661719 50620044970547286884129 := by
  unfold tailWord_2661719
  simp only [CollatzResearch.WordTrace]
  refine ⟨97080867444054123258916211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64720578296036082172610807 97080867444054123258916211)
  ·
    refine ⟨145621301166081184888374317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97080867444054123258916211 145621301166081184888374317)
    ·
      refine ⟨54607987937280444333140369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145621301166081184888374317 54607987937280444333140369)
      ·
        refine ⟨40955990952960333249855277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54607987937280444333140369 40955990952960333249855277)
        ·
          refine ⟨15358496607360124968695729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40955990952960333249855277 15358496607360124968695729)
          ·
            refine ⟨11518872455520093726521797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15358496607360124968695729 11518872455520093726521797)
            ·
              refine ⟨2159788585410017573722837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11518872455520093726521797 2159788585410017573722837)
              ·
                refine ⟨50620044970547286884129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2159788585410017573722837 50620044970547286884129)
                ·
                  rfl

theorem cell23_2661719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 7].length) (baseStart_2661719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661719 prefixEnd_2661719 := by exact prefixLift 2661719
  have htrace : WordTrace (prefixWord ++ tailWord_2661719) baseStart_2661719 baseEnd_2661719 := by
    simpa [prefixWord, tailWord_2661719, baseEnd_2661719] using wordTrace_append hprefix tailTrace_2661719
  have hstable : (prefixWord ++ tailWord_2661719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661719).length < 2 ^ (prefixWord ++ tailWord_2661719).sum := by decide
  have hdescent : baseEnd_2661719 < baseStart_2661719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661729 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_2661729 : Nat := 118140960795 + 2661729 * 2 ^ 59
def prefixEnd_2661729 : Nat := 4983230072969 + 3 ^ 40 * 2661729 * 2
def baseEnd_2661729 : Nat := 1366746349011321706746437

theorem tailTrace_2661729 : CollatzResearch.WordTrace tailWord_2661729 prefixEnd_2661729 1366746349011321706746437 := by
  unfold tailWord_2661729
  simp only [CollatzResearch.WordTrace]
  refine ⟨97081232174017894966780241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64720821449345263311186827 97081232174017894966780241)
  ·
    refine ⟨72810924130513421225085181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97081232174017894966780241 72810924130513421225085181)
    ·
      refine ⟨27304096548942532959406943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72810924130513421225085181 27304096548942532959406943)
      ·
        refine ⟨40956144823413799439110415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27304096548942532959406943 40956144823413799439110415)
        ·
          refine ⟨61434217235120699158665623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40956144823413799439110415 61434217235120699158665623)
          ·
            refine ⟨92151325852681048737998435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61434217235120699158665623 92151325852681048737998435)
            ·
              refine ⟨138226988779021573106997653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92151325852681048737998435 138226988779021573106997653)
              ·
                refine ⟨6479390099016636239390515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138226988779021573106997653 6479390099016636239390515)
                ·
                  refine ⟨9719085148524954359085773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6479390099016636239390515 9719085148524954359085773)
                  ·
                    refine ⟨3644656930696857884657165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9719085148524954359085773 3644656930696857884657165)
                    ·
                      refine ⟨1366746349011321706746437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3644656930696857884657165 1366746349011321706746437)
                      ·
                        rfl

theorem cell23_2661729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_2661729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661729 prefixEnd_2661729 := by exact prefixLift 2661729
  have htrace : WordTrace (prefixWord ++ tailWord_2661729) baseStart_2661729 baseEnd_2661729 := by
    simpa [prefixWord, tailWord_2661729, baseEnd_2661729] using wordTrace_append hprefix tailTrace_2661729
  have hstable : (prefixWord ++ tailWord_2661729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661729).length < 2 ^ (prefixWord ++ tailWord_2661729).sum := by decide
  have hdescent : baseEnd_2661729 < baseStart_2661729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661736 : List Nat := [2, 1, 4, 2, 4, 1, 9]
def baseStart_2661736 : Nat := 118140960795 + 2661736 * 2 ^ 59
def prefixEnd_2661736 : Nat := 4983230072969 + 3 ^ 40 * 2661736 * 2
def baseEnd_2661736 : Nat := 16873456091060533078505

theorem tailTrace_2661736 : CollatzResearch.WordTrace tailWord_2661736 prefixEnd_2661736 16873456091060533078505 := by
  unfold tailWord_2661736
  simp only [CollatzResearch.WordTrace]
  refine ⟨48540743742496267581142531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64720991656661690108190041 48540743742496267581142531)
  ·
    refine ⟨72811115613744401371713797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48540743742496267581142531 72811115613744401371713797)
    ·
      refine ⟨13652084177577075257196337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72811115613744401371713797 13652084177577075257196337)
      ·
        refine ⟨10239063133182806442897253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13652084177577075257196337 10239063133182806442897253)
        ·
          refine ⟨1919824337471776208043235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10239063133182806442897253 1919824337471776208043235)
          ·
            refine ⟨2879736506207664312064853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919824337471776208043235 2879736506207664312064853)
            ·
              refine ⟨16873456091060533078505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2879736506207664312064853 16873456091060533078505)
              ·
                rfl

theorem cell23_2661736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 9].length) (baseStart_2661736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661736 prefixEnd_2661736 := by exact prefixLift 2661736
  have htrace : WordTrace (prefixWord ++ tailWord_2661736) baseStart_2661736 baseEnd_2661736 := by
    simpa [prefixWord, tailWord_2661736, baseEnd_2661736] using wordTrace_append hprefix tailTrace_2661736
  have hstable : (prefixWord ++ tailWord_2661736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661736).length < 2 ^ (prefixWord ++ tailWord_2661736).sum := by decide
  have hdescent : baseEnd_2661736 < baseStart_2661736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661746 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_2661746 : Nat := 118140960795 + 2661746 * 2 ^ 59
def prefixEnd_2661746 : Nat := 4983230072969 + 3 ^ 40 * 2661746 * 2
def baseEnd_2661746 : Nat := 1366755078182448140233859

theorem tailTrace_2661746 : CollatzResearch.WordTrace tailWord_2661746 prefixEnd_2661746 1366755078182448140233859 := by
  unfold tailWord_2661746
  simp only [CollatzResearch.WordTrace]
  refine ⟨24270463053739076717537273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64721234809970871246766061 24270463053739076717537273)
  ·
    refine ⟨18202847290304307538152955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24270463053739076717537273 18202847290304307538152955)
    ·
      refine ⟨27304270935456461307229433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18202847290304307538152955 27304270935456461307229433)
      ·
        refine ⟨20478203201592345980422075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27304270935456461307229433 20478203201592345980422075)
        ·
          refine ⟨30717304802388518970633113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20478203201592345980422075 30717304802388518970633113)
          ·
            refine ⟨23037978601791389227974835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30717304802388518970633113 23037978601791389227974835)
            ·
              refine ⟨34556967902687083841962253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23037978601791389227974835 34556967902687083841962253)
              ·
                refine ⟨12958862963507656440735845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34556967902687083841962253 12958862963507656440735845)
                ·
                  refine ⟨2429786805657685582637971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12958862963507656440735845 2429786805657685582637971)
                  ·
                    refine ⟨3644680208486528373956957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2429786805657685582637971 3644680208486528373956957)
                    ·
                      refine ⟨1366755078182448140233859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3644680208486528373956957 1366755078182448140233859)
                      ·
                        rfl

theorem cell23_2661746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_2661746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661746 prefixEnd_2661746 := by exact prefixLift 2661746
  have htrace : WordTrace (prefixWord ++ tailWord_2661746) baseStart_2661746 baseEnd_2661746 := by
    simpa [prefixWord, tailWord_2661746, baseEnd_2661746] using wordTrace_append hprefix tailTrace_2661746
  have hstable : (prefixWord ++ tailWord_2661746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661746).length < 2 ^ (prefixWord ++ tailWord_2661746).sum := by decide
  have hdescent : baseEnd_2661746 < baseStart_2661746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661756 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 3, 3, 2]
def baseStart_2661756 : Nat := 118140960795 + 2661756 * 2 ^ 59
def prefixEnd_2661756 : Nat := 4983230072969 + 3 ^ 40 * 2661756 * 2
def baseEnd_2661756 : Nat := 1366760212988993101108813

theorem tailTrace_2661756 : CollatzResearch.WordTrace tailWord_2661756 prefixEnd_2661756 1366760212988993101108813 := by
  unfold tailWord_2661756
  simp only [CollatzResearch.WordTrace]
  refine ⟨48541108472460039289006561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64721477963280052385342081 48541108472460039289006561)
  ·
    refine ⟨36405831354345029466754921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48541108472460039289006561 36405831354345029466754921)
    ·
      refine ⟨27304373515758772100066191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36405831354345029466754921 27304373515758772100066191)
      ·
        refine ⟨40956560273638158150099287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27304373515758772100066191 40956560273638158150099287)
        ·
          refine ⟨61434840410457237225148931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40956560273638158150099287 61434840410457237225148931)
          ·
            refine ⟨92152260615685855837723397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61434840410457237225148931 92152260615685855837723397)
            ·
              refine ⟨17278548865441097969573137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92152260615685855837723397 17278548865441097969573137)
              ·
                refine ⟨12958911649080823477179853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17278548865441097969573137 12958911649080823477179853)
                ·
                  refine ⟨4859591868405308803942445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12958911649080823477179853 4859591868405308803942445)
                  ·
                    refine ⟨1822346950651990801478417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4859591868405308803942445 1822346950651990801478417)
                    ·
                      refine ⟨1366760212988993101108813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822346950651990801478417 1366760212988993101108813)
                      ·
                        rfl

theorem cell23_2661756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_2661756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661756 prefixEnd_2661756 := by exact prefixLift 2661756
  have htrace : WordTrace (prefixWord ++ tailWord_2661756) baseStart_2661756 baseEnd_2661756 := by
    simpa [prefixWord, tailWord_2661756, baseEnd_2661756] using wordTrace_append hprefix tailTrace_2661756
  have hstable : (prefixWord ++ tailWord_2661756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661756).length < 2 ^ (prefixWord ++ tailWord_2661756).sum := by decide
  have hdescent : baseEnd_2661756 < baseStart_2661756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661763 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 2, 1, 3]
def baseStart_2661763 : Nat := 118140960795 + 2661763 * 2 ^ 59
def prefixEnd_2661763 : Nat := 4983230072969 + 3 ^ 40 * 2661763 * 2
def baseEnd_2661763 : Nat := 1366763807353574573721281

theorem tailTrace_2661763 : CollatzResearch.WordTrace tailWord_2661763 prefixEnd_2661763 1366763807353574573721281 := by
  unfold tailWord_2661763
  simp only [CollatzResearch.WordTrace]
  refine ⟨97082472255894718773517943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64721648170596479182345295 97082472255894718773517943)
  ·
    refine ⟨145623708383842078160276915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97082472255894718773517943 145623708383842078160276915)
    ·
      refine ⟨218435562575763117240415373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145623708383842078160276915 218435562575763117240415373)
      ·
        refine ⟨81913335965911168965155765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218435562575763117240415373 81913335965911168965155765)
        ·
          refine ⟨7679375246804172090483353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81913335965911168965155765 7679375246804172090483353)
          ·
            refine ⟨5759531435103129067862515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7679375246804172090483353 5759531435103129067862515)
            ·
              refine ⟨8639297152654693601793773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5759531435103129067862515 8639297152654693601793773)
              ·
                refine ⟨3239736432245510100672665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8639297152654693601793773 3239736432245510100672665)
                ·
                  refine ⟨2429802324184132575504499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3239736432245510100672665 2429802324184132575504499)
                  ·
                    refine ⟨3644703486276198863256749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2429802324184132575504499 3644703486276198863256749)
                    ·
                      refine ⟨1366763807353574573721281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3644703486276198863256749 1366763807353574573721281)
                      ·
                        rfl

theorem cell23_2661763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_2661763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661763 prefixEnd_2661763 := by exact prefixLift 2661763
  have htrace : WordTrace (prefixWord ++ tailWord_2661763) baseStart_2661763 baseEnd_2661763 := by
    simpa [prefixWord, tailWord_2661763, baseEnd_2661763] using wordTrace_append hprefix tailTrace_2661763
  have hstable : (prefixWord ++ tailWord_2661763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661763).length < 2 ^ (prefixWord ++ tailWord_2661763).sum := by decide
  have hdescent : baseEnd_2661763 < baseStart_2661763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661809 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 7]
def baseStart_2661809 : Nat := 118140960795 + 2661809 * 2 ^ 59
def prefixEnd_2661809 : Nat := 4983230072969 + 3 ^ 40 * 2661809 * 2
def baseEnd_2661809 : Nat := 151865269718186821527341

theorem tailTrace_2661809 : CollatzResearch.WordTrace tailWord_2661809 prefixEnd_2661809 151865269718186821527341 := by
  unfold tailWord_2661809
  simp only [CollatzResearch.WordTrace]
  refine ⟨97084150013728068629692481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64722766675818712419794987 97084150013728068629692481)
  ·
    refine ⟨72813112510296051472269361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97084150013728068629692481 72813112510296051472269361)
    ·
      refine ⟨54609834382722038604202021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72813112510296051472269361 54609834382722038604202021)
      ·
        refine ⟨10239343946760382238287879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54609834382722038604202021 10239343946760382238287879)
        ·
          refine ⟨15359015920140573357431819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10239343946760382238287879 15359015920140573357431819)
          ·
            refine ⟨23038523880210860036147729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15359015920140573357431819 23038523880210860036147729)
            ·
              refine ⟨17278892910158145027110797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23038523880210860036147729 17278892910158145027110797)
              ·
                refine ⟨6479584841309304385166549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17278892910158145027110797 6479584841309304385166549)
                ·
                  refine ⟨151865269718186821527341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6479584841309304385166549 151865269718186821527341)
                  ·
                    rfl

theorem cell23_2661809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 7].length) (baseStart_2661809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661809 prefixEnd_2661809 := by exact prefixLift 2661809
  have htrace : WordTrace (prefixWord ++ tailWord_2661809) baseStart_2661809 baseEnd_2661809 := by
    simpa [prefixWord, tailWord_2661809, baseEnd_2661809] using wordTrace_append hprefix tailTrace_2661809
  have hstable : (prefixWord ++ tailWord_2661809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661809).length < 2 ^ (prefixWord ++ tailWord_2661809).sum := by decide
  have hdescent : baseEnd_2661809 < baseStart_2661809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661820 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2661820 : Nat := 118140960795 + 2661820 * 2 ^ 59
def prefixEnd_2661820 : Nat := 4983230072969 + 3 ^ 40 * 2661820 * 2
def baseEnd_2661820 : Nat := 1366793075750880850708519

theorem tailTrace_2661820 : CollatzResearch.WordTrace tailWord_2661820 prefixEnd_2661820 1366793075750880850708519 := by
  unfold tailWord_2661820
  simp only [CollatzResearch.WordTrace]
  refine ⟨48542275608344108754171457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64723034144458811672228609 48542275608344108754171457)
  ·
    refine ⟨36406706706258081565628593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48542275608344108754171457 36406706706258081565628593)
    ·
      refine ⟨27305030029693561174221445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36406706706258081565628593 27305030029693561174221445)
      ·
        refine ⟨5119693130567542720166521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27305030029693561174221445 5119693130567542720166521)
        ·
          refine ⟨3839769847925657040124891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5119693130567542720166521 3839769847925657040124891)
          ·
            refine ⟨5759654771888485560187337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839769847925657040124891 5759654771888485560187337)
            ·
              refine ⟨4319741078916364170140503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5759654771888485560187337 4319741078916364170140503)
              ·
                refine ⟨6479611618374546255210755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4319741078916364170140503 6479611618374546255210755)
                ·
                  refine ⟨9719417427561819382816133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6479611618374546255210755 9719417427561819382816133)
                  ·
                    refine ⟨1822390767667841134278025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9719417427561819382816133 1822390767667841134278025)
                    ·
                      refine ⟨1366793075750880850708519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822390767667841134278025 1366793075750880850708519)
                      ·
                        rfl

theorem cell23_2661820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2661820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661820 prefixEnd_2661820 := by exact prefixLift 2661820
  have htrace : WordTrace (prefixWord ++ tailWord_2661820) baseStart_2661820 baseEnd_2661820 := by
    simpa [prefixWord, tailWord_2661820, baseEnd_2661820] using wordTrace_append hprefix tailTrace_2661820
  have hstable : (prefixWord ++ tailWord_2661820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661820).length < 2 ^ (prefixWord ++ tailWord_2661820).sum := by decide
  have hdescent : baseEnd_2661820 < baseStart_2661820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661896 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_2661896 : Nat := 118140960795 + 2661896 * 2 ^ 59
def prefixEnd_2661896 : Nat := 4983230072969 + 3 ^ 40 * 2661896 * 2
def baseEnd_2661896 : Nat := 1366832100280622553358169

theorem tailTrace_2661896 : CollatzResearch.WordTrace tailWord_2661896 prefixEnd_2661896 1366832100280622553358169 := by
  unfold tailWord_2661896
  simp only [CollatzResearch.WordTrace]
  refine ⟨48543661582206441244054771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64724882109608588325406361 48543661582206441244054771)
  ·
    refine ⟨72815492373309661866082157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48543661582206441244054771 72815492373309661866082157)
    ·
      refine ⟨27305809639991123199780809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72815492373309661866082157 27305809639991123199780809)
      ·
        refine ⟨20479357229993342399835607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27305809639991123199780809 20479357229993342399835607)
        ·
          refine ⟨30719035844990013599753411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20479357229993342399835607 30719035844990013599753411)
          ·
            refine ⟨46078553767485020399630117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30719035844990013599753411 46078553767485020399630117)
            ·
              refine ⟨8639728831403441324930647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46078553767485020399630117 8639728831403441324930647)
              ·
                refine ⟨12959593247105161987395971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8639728831403441324930647 12959593247105161987395971)
                ·
                  refine ⟨19439389870657742981093957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12959593247105161987395971 19439389870657742981093957)
                  ·
                    refine ⟨3644885600748326808955117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19439389870657742981093957 3644885600748326808955117)
                    ·
                      refine ⟨1366832100280622553358169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3644885600748326808955117 1366832100280622553358169)
                      ·
                        rfl

theorem cell23_2661896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_2661896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661896 prefixEnd_2661896 := by exact prefixLift 2661896
  have htrace : WordTrace (prefixWord ++ tailWord_2661896) baseStart_2661896 baseEnd_2661896 := by
    simpa [prefixWord, tailWord_2661896, baseEnd_2661896] using wordTrace_append hprefix tailTrace_2661896
  have hstable : (prefixWord ++ tailWord_2661896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661896).length < 2 ^ (prefixWord ++ tailWord_2661896).sum := by decide
  have hdescent : baseEnd_2661896 < baseStart_2661896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661916 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 6]
def baseStart_2661916 : Nat := 118140960795 + 2661916 * 2 ^ 59
def prefixEnd_2661916 : Nat := 4983230072969 + 3 ^ 40 * 2661916 * 2
def baseEnd_2661916 : Nat := 151871374432634719456453

theorem tailTrace_2661916 : CollatzResearch.WordTrace tailWord_2661916 prefixEnd_2661916 151871374432634719456453 := by
  unfold tailWord_2661916
  simp only [CollatzResearch.WordTrace]
  refine ⟨48544026312170212951918801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64725368416226950602558401 48544026312170212951918801)
  ·
    refine ⟨36408019734127659713939101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48544026312170212951918801 36408019734127659713939101)
    ·
      refine ⟨13653007400297872392727163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36408019734127659713939101 13653007400297872392727163)
      ·
        refine ⟨20479511100446808589090745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13653007400297872392727163 20479511100446808589090745)
        ·
          refine ⟨15359633325335106441818059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20479511100446808589090745 15359633325335106441818059)
          ·
            refine ⟨23039449988002659662727089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15359633325335106441818059 23039449988002659662727089)
            ·
              refine ⟨17279587491001994747045317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23039449988002659662727089 17279587491001994747045317)
              ·
                refine ⟨3239922654562874015070997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17279587491001994747045317 3239922654562874015070997)
                ·
                  refine ⟨151871374432634719456453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3239922654562874015070997 151871374432634719456453)
                  ·
                    rfl

theorem cell23_2661916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_2661916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661916 prefixEnd_2661916 := by exact prefixLift 2661916
  have htrace : WordTrace (prefixWord ++ tailWord_2661916) baseStart_2661916 baseEnd_2661916 := by
    simpa [prefixWord, tailWord_2661916, baseEnd_2661916] using wordTrace_append hprefix tailTrace_2661916
  have hstable : (prefixWord ++ tailWord_2661916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661916).length < 2 ^ (prefixWord ++ tailWord_2661916).sum := by decide
  have hdescent : baseEnd_2661916 < baseStart_2661916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661919 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_2661919 : Nat := 118140960795 + 2661919 * 2 ^ 59
def prefixEnd_2661919 : Nat := 4983230072969 + 3 ^ 40 * 2661919 * 2
def baseEnd_2661919 : Nat := 1366843910335675963370563

theorem tailTrace_2661919 : CollatzResearch.WordTrace tailWord_2661919 prefixEnd_2661919 1366843910335675963370563 := by
  unfold tailWord_2661919
  simp only [CollatzResearch.WordTrace]
  refine ⟨97088162043329557416196811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64725441362219704944131207 97088162043329557416196811)
  ·
    refine ⟨145632243064994336124295217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97088162043329557416196811 145632243064994336124295217)
    ·
      refine ⟨109224182298745752093221413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145632243064994336124295217 109224182298745752093221413)
      ·
        refine ⟨20479534181014828517479015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109224182298745752093221413 20479534181014828517479015)
        ·
          refine ⟨30719301271522242776218523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20479534181014828517479015 30719301271522242776218523)
          ·
            refine ⟨46078951907283364164327785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30719301271522242776218523 46078951907283364164327785)
            ·
              refine ⟨34559213930462523123245839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46078951907283364164327785 34559213930462523123245839)
              ·
                refine ⟨51838820895693784684868759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34559213930462523123245839 51838820895693784684868759)
                ·
                  refine ⟨77758231343540677027303139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51838820895693784684868759 77758231343540677027303139)
                  ·
                    refine ⟨116637347015311015540954709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77758231343540677027303139 116637347015311015540954709)
                    ·
                      refine ⟨1366843910335675963370563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 116637347015311015540954709 1366843910335675963370563)
                      ·
                        rfl

theorem cell23_2661919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_2661919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661919 prefixEnd_2661919 := by exact prefixLift 2661919
  have htrace : WordTrace (prefixWord ++ tailWord_2661919) baseStart_2661919 baseEnd_2661919 := by
    simpa [prefixWord, tailWord_2661919, baseEnd_2661919] using wordTrace_append hprefix tailTrace_2661919
  have hstable : (prefixWord ++ tailWord_2661919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661919).length < 2 ^ (prefixWord ++ tailWord_2661919).sum := by decide
  have hdescent : baseEnd_2661919 < baseStart_2661919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661920 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 3, 4]
def baseStart_2661920 : Nat := 118140960795 + 2661920 * 2 ^ 59
def prefixEnd_2661920 : Nat := 4983230072969 + 3 ^ 40 * 2661920 * 2
def baseEnd_2661920 : Nat := 455614807938776819819353

theorem tailTrace_2661920 : CollatzResearch.WordTrace tailWord_2661920 prefixEnd_2661920 455614807938776819819353 := by
  unfold tailWord_2661920
  simp only [CollatzResearch.WordTrace]
  refine ⟨48544099258162967293491607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64725465677550623057988809 48544099258162967293491607)
  ·
    refine ⟨72816148887244450940237411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48544099258162967293491607 72816148887244450940237411)
    ·
      refine ⟨109224223330866676410356117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72816148887244450940237411 109224223330866676410356117)
      ·
        refine ⟨5119885468634375456735443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109224223330866676410356117 5119885468634375456735443)
        ·
          refine ⟨7679828202951563185103165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119885468634375456735443 7679828202951563185103165)
          ·
            refine ⟨2879935576106836194413687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7679828202951563185103165 2879935576106836194413687)
            ·
              refine ⟨4319903364160254291620531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879935576106836194413687 4319903364160254291620531)
              ·
                refine ⟨6479855046240381437430797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4319903364160254291620531 6479855046240381437430797)
                ·
                  refine ⟨2429945642340143039036549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6479855046240381437430797 2429945642340143039036549)
                  ·
                    refine ⟨455614807938776819819353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2429945642340143039036549 455614807938776819819353)
                    ·
                      rfl

theorem cell23_2661920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3, 4].length) (baseStart_2661920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661920 prefixEnd_2661920 := by exact prefixLift 2661920
  have htrace : WordTrace (prefixWord ++ tailWord_2661920) baseStart_2661920 baseEnd_2661920 := by
    simpa [prefixWord, tailWord_2661920, baseEnd_2661920] using wordTrace_append hprefix tailTrace_2661920
  have hstable : (prefixWord ++ tailWord_2661920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661920).length < 2 ^ (prefixWord ++ tailWord_2661920).sum := by decide
  have hdescent : baseEnd_2661920 < baseStart_2661920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661946 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_2661946 : Nat := 118140960795 + 2661946 * 2 ^ 59
def prefixEnd_2661946 : Nat := 4983230072969 + 3 ^ 40 * 2661946 * 2
def baseEnd_2661946 : Nat := 455619258104449119244313

theorem tailTrace_2661946 : CollatzResearch.WordTrace tailWord_2661946 prefixEnd_2661946 455619258104449119244313 := by
  unfold tailWord_2661946
  simp only [CollatzResearch.WordTrace]
  refine ⟨24272286703557935256857423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64726097876154494018286461 24272286703557935256857423)
  ·
    refine ⟨36408430055336902885286135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24272286703557935256857423 36408430055336902885286135)
    ·
      refine ⟨54612645083005354327929203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36408430055336902885286135 54612645083005354327929203)
      ·
        refine ⟨81918967624508031491893805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54612645083005354327929203 81918967624508031491893805)
        ·
          refine ⟨30719612859190511809460177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81918967624508031491893805 30719612859190511809460177)
          ·
            refine ⟨23039709644392883857095133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30719612859190511809460177 23039709644392883857095133)
            ·
              refine ⟨8639891116647331446410675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23039709644392883857095133 8639891116647331446410675)
              ·
                refine ⟨12959836674970997169616013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8639891116647331446410675 12959836674970997169616013)
                ·
                  refine ⟨4859938753114123938606005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12959836674970997169616013 4859938753114123938606005)
                  ·
                    refine ⟨455619258104449119244313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4859938753114123938606005 455619258104449119244313)
                    ·
                      rfl

theorem cell23_2661946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_2661946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661946 prefixEnd_2661946 := by exact prefixLift 2661946
  have htrace : WordTrace (prefixWord ++ tailWord_2661946) baseStart_2661946 baseEnd_2661946 := by
    simpa [prefixWord, tailWord_2661946, baseEnd_2661946] using wordTrace_append hprefix tailTrace_2661946
  have hstable : (prefixWord ++ tailWord_2661946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661946).length < 2 ^ (prefixWord ++ tailWord_2661946).sum := by decide
  have hdescent : baseEnd_2661946 < baseStart_2661946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661970 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_2661970 : Nat := 118140960795 + 2661970 * 2 ^ 59
def prefixEnd_2661970 : Nat := 4983230072969 + 3 ^ 40 * 2661970 * 2
def baseEnd_2661970 : Nat := 1366870097849055263832829

theorem tailTrace_2661970 : CollatzResearch.WordTrace tailWord_2661970 prefixEnd_2661970 1366870097849055263832829 := by
  unfold tailWord_2661970
  simp only [CollatzResearch.WordTrace]
  refine ⟨24272505541536198281575841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64726681444096528750868909 24272505541536198281575841)
  ·
    refine ⟨18204379156152148711181881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24272505541536198281575841 18204379156152148711181881)
    ·
      refine ⟨13653284367114111533386411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18204379156152148711181881 13653284367114111533386411)
      ·
        refine ⟨20479926550671167300079617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13653284367114111533386411 20479926550671167300079617)
        ·
          refine ⟨15359944913003375475059713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20479926550671167300079617 15359944913003375475059713)
          ·
            refine ⟨11519958684752531606294785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15359944913003375475059713 11519958684752531606294785)
            ·
              refine ⟨8639969013564398704721089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11519958684752531606294785 8639969013564398704721089)
              ·
                refine ⟨6479976760173299028540817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8639969013564398704721089 6479976760173299028540817)
                ·
                  refine ⟨4859982570129974271405613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6479976760173299028540817 4859982570129974271405613)
                  ·
                    refine ⟨1822493463798740351777105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4859982570129974271405613 1822493463798740351777105)
                    ·
                      refine ⟨1366870097849055263832829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822493463798740351777105 1366870097849055263832829)
                      ·
                        rfl

theorem cell23_2661970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_2661970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661970 prefixEnd_2661970 := by exact prefixLift 2661970
  have htrace : WordTrace (prefixWord ++ tailWord_2661970) baseStart_2661970 baseEnd_2661970 := by
    simpa [prefixWord, tailWord_2661970, baseEnd_2661970] using wordTrace_append hprefix tailTrace_2661970
  have hstable : (prefixWord ++ tailWord_2661970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661970).length < 2 ^ (prefixWord ++ tailWord_2661970).sum := by decide
  have hdescent : baseEnd_2661970 < baseStart_2661970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661993 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 2, 4]
def baseStart_2661993 : Nat := 118140960795 + 2661993 * 2 ^ 59
def prefixEnd_2661993 : Nat := 4983230072969 + 3 ^ 40 * 2661993 * 2
def baseEnd_2661993 : Nat := 455627302634702891281741

theorem tailTrace_2661993 : CollatzResearch.WordTrace tailWord_2661993 prefixEnd_2661993 455627302634702891281741 := by
  unfold tailWord_2661993
  simp only [CollatzResearch.WordTrace]
  refine ⟨97090861045061468054390633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64727240696707645369593755 97090861045061468054390633)
  ·
    refine ⟨72818145783796101040792975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97090861045061468054390633 72818145783796101040792975)
    ·
      refine ⟨109227218675694151561189463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72818145783796101040792975 109227218675694151561189463)
      ·
        refine ⟨163840828013541227341784195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109227218675694151561189463 163840828013541227341784195)
        ·
          refine ⟨245761242020311841012676293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163840828013541227341784195 245761242020311841012676293)
          ·
            refine ⟨46080232878808470189876805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245761242020311841012676293 46080232878808470189876805)
            ·
              refine ⟨8640043664776588160601901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46080232878808470189876805 8640043664776588160601901)
              ·
                refine ⟨3240016374291220560225713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8640043664776588160601901 3240016374291220560225713)
                ·
                  refine ⟨2430012280718415420169285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3240016374291220560225713 2430012280718415420169285)
                  ·
                    refine ⟨455627302634702891281741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2430012280718415420169285 455627302634702891281741)
                    ·
                      rfl

theorem cell23_2661993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 4].length) (baseStart_2661993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661993 prefixEnd_2661993 := by exact prefixLift 2661993
  have htrace : WordTrace (prefixWord ++ tailWord_2661993) baseStart_2661993 baseEnd_2661993 := by
    simpa [prefixWord, tailWord_2661993, baseEnd_2661993] using wordTrace_append hprefix tailTrace_2661993
  have hstable : (prefixWord ++ tailWord_2661993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661993).length < 2 ^ (prefixWord ++ tailWord_2661993).sum := by decide
  have hdescent : baseEnd_2661993 < baseStart_2661993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662000 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 5, 2, 2]
def baseStart_2662000 : Nat := 118140960795 + 2662000 * 2 ^ 59
def prefixEnd_2662000 : Nat := 4983230072969 + 3 ^ 40 * 2662000 * 2
def baseEnd_2662000 : Nat := 1366885502268690146457691

theorem tailTrace_2662000 : CollatzResearch.WordTrace tailWord_2662000 prefixEnd_2662000 1366885502268690146457691 := by
  unfold tailWord_2662000
  simp only [CollatzResearch.WordTrace]
  refine ⟨48545558178018054124947727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64727410904024072166596969 48545558178018054124947727)
  ·
    refine ⟨72818337267027081187421591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48545558178018054124947727 72818337267027081187421591)
    ·
      refine ⟨109227505900540621781132387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72818337267027081187421591 109227505900540621781132387)
      ·
        refine ⟨163841258850810932671698581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109227505900540621781132387 163841258850810932671698581)
        ·
          refine ⟨7680059008631762468985871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 163841258850810932671698581 7680059008631762468985871)
          ·
            refine ⟨11520088512947643703478807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7680059008631762468985871 11520088512947643703478807)
            ·
              refine ⟨17280132769421465555218211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11520088512947643703478807 17280132769421465555218211)
              ·
                refine ⟨25920199154132198332827317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17280132769421465555218211 25920199154132198332827317)
                ·
                  refine ⟨2430018670699893593702561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25920199154132198332827317 2430018670699893593702561)
                  ·
                    refine ⟨1822514003024920195276921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2430018670699893593702561 1822514003024920195276921)
                    ·
                      refine ⟨1366885502268690146457691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822514003024920195276921 1366885502268690146457691)
                      ·
                        rfl

theorem cell23_2662000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5, 2, 2].length) (baseStart_2662000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662000 prefixEnd_2662000 := by exact prefixLift 2662000
  have htrace : WordTrace (prefixWord ++ tailWord_2662000) baseStart_2662000 baseEnd_2662000 := by
    simpa [prefixWord, tailWord_2662000, baseEnd_2662000] using wordTrace_append hprefix tailTrace_2662000
  have hstable : (prefixWord ++ tailWord_2662000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662000).length < 2 ^ (prefixWord ++ tailWord_2662000).sum := by decide
  have hdescent : baseEnd_2662000 < baseStart_2662000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662013 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_2662013 : Nat := 118140960795 + 2662013 * 2 ^ 59
def prefixEnd_2662013 : Nat := 4983230072969 + 3 ^ 40 * 2662013 * 2
def baseEnd_2662013 : Nat := 1366892177517198595595131

theorem tailTrace_2662013 : CollatzResearch.WordTrace tailWord_2662013 prefixEnd_2662013 1366892177517198595595131 := by
  unfold tailWord_2662013
  simp only [CollatzResearch.WordTrace]
  refine ⟨97091590504989011470118693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64727727003326007646745795 97091590504989011470118693)
  ·
    refine ⟨18204673219685439650647255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97091590504989011470118693 18204673219685439650647255)
    ·
      refine ⟨27307009829528159475970883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18204673219685439650647255 27307009829528159475970883)
      ·
        refine ⟨40960514744292239213956325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27307009829528159475970883 40960514744292239213956325)
        ·
          refine ⟨7680096514554794852616811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40960514744292239213956325 7680096514554794852616811)
          ·
            refine ⟨11520144771832192278925217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7680096514554794852616811 11520144771832192278925217)
            ·
              refine ⟨8640108578874144209193913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11520144771832192278925217 8640108578874144209193913)
              ·
                refine ⟨6480081434155608156895435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8640108578874144209193913 6480081434155608156895435)
                ·
                  refine ⟨9720122151233412235343153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6480081434155608156895435 9720122151233412235343153)
                  ·
                    refine ⟨7290091613425059176507365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9720122151233412235343153 7290091613425059176507365)
                    ·
                      refine ⟨1366892177517198595595131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7290091613425059176507365 1366892177517198595595131)
                      ·
                        rfl

theorem cell23_2662013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_2662013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662013 prefixEnd_2662013 := by exact prefixLift 2662013
  have htrace : WordTrace (prefixWord ++ tailWord_2662013) baseStart_2662013 baseEnd_2662013 := by
    simpa [prefixWord, tailWord_2662013, baseEnd_2662013] using wordTrace_append hprefix tailTrace_2662013
  have hstable : (prefixWord ++ tailWord_2662013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662013).length < 2 ^ (prefixWord ++ tailWord_2662013).sum := by decide
  have hdescent : baseEnd_2662013 < baseStart_2662013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662017 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_2662017 : Nat := 118140960795 + 2662017 * 2 ^ 59
def prefixEnd_2662017 : Nat := 4983230072969 + 3 ^ 40 * 2662017 * 2
def baseEnd_2662017 : Nat := 1366894231439816579945113

theorem tailTrace_2662017 : CollatzResearch.WordTrace tailWord_2662017 prefixEnd_2662017 1366894231439816579945113 := by
  unfold tailWord_2662017
  simp only [CollatzResearch.WordTrace]
  refine ⟨97091736396974520153264305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64727824264649680102176203 97091736396974520153264305)
  ·
    refine ⟨72818802297730890114948229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97091736396974520153264305 72818802297730890114948229)
    ·
      refine ⟨13653525430824541896552793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72818802297730890114948229 13653525430824541896552793)
      ·
        refine ⟨10240144073118406422414595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13653525430824541896552793 10240144073118406422414595)
        ·
          refine ⟨15360216109677609633621893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10240144073118406422414595 15360216109677609633621893)
          ·
            refine ⟨2880040520564551806304105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15360216109677609633621893 2880040520564551806304105)
            ·
              refine ⟨2160030390423413854728079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2880040520564551806304105 2160030390423413854728079)
              ·
                refine ⟨3240045585635120782092119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2160030390423413854728079 3240045585635120782092119)
                ·
                  refine ⟨4860068378452681173138179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240045585635120782092119 4860068378452681173138179)
                  ·
                    refine ⟨7290102567679021759707269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4860068378452681173138179 7290102567679021759707269)
                    ·
                      refine ⟨1366894231439816579945113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7290102567679021759707269 1366894231439816579945113)
                      ·
                        rfl

theorem cell23_2662017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_2662017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662017 prefixEnd_2662017 := by exact prefixLift 2662017
  have htrace : WordTrace (prefixWord ++ tailWord_2662017) baseStart_2662017 baseEnd_2662017 := by
    simpa [prefixWord, tailWord_2662017, baseEnd_2662017] using wordTrace_append hprefix tailTrace_2662017
  have hstable : (prefixWord ++ tailWord_2662017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662017).length < 2 ^ (prefixWord ++ tailWord_2662017).sum := by decide
  have hdescent : baseEnd_2662017 < baseStart_2662017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662034 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_2662034 : Nat := 118140960795 + 2662034 * 2 ^ 59
def prefixEnd_2662034 : Nat := 4983230072969 + 3 ^ 40 * 2662034 * 2
def baseEnd_2662034 : Nat := 1366902960610943013432535

theorem tailTrace_2662034 : CollatzResearch.WordTrace tailWord_2662034 prefixEnd_2662034 1366902960610943013432535 := by
  unfold tailWord_2662034
  simp only [CollatzResearch.WordTrace]
  refine ⟨24273089109478233014158289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64728237625275288037755437 24273089109478233014158289)
  ·
    refine ⟨18204816832108674760618717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24273089109478233014158289 18204816832108674760618717)
    ·
      refine ⟨6826806312040753035232019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18204816832108674760618717 6826806312040753035232019)
      ·
        refine ⟨10240209468061129552848029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6826806312040753035232019 10240209468061129552848029)
        ·
          refine ⟨3840078550522923582318011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10240209468061129552848029 3840078550522923582318011)
          ·
            refine ⟨5760117825784385373477017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3840078550522923582318011 5760117825784385373477017)
            ·
              refine ⟨4320088369338289030107763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5760117825784385373477017 4320088369338289030107763)
              ·
                refine ⟨6480132554007433545161645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4320088369338289030107763 6480132554007433545161645)
                ·
                  refine ⟨2430049707752787579435617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6480132554007433545161645 2430049707752787579435617)
                  ·
                    refine ⟨1822537280814590684576713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2430049707752787579435617 1822537280814590684576713)
                    ·
                      refine ⟨1366902960610943013432535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822537280814590684576713 1366902960610943013432535)
                      ·
                        rfl

theorem cell23_2662034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_2662034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662034 prefixEnd_2662034 := by exact prefixLift 2662034
  have htrace : WordTrace (prefixWord ++ tailWord_2662034) baseStart_2662034 baseEnd_2662034 := by
    simpa [prefixWord, tailWord_2662034, baseEnd_2662034] using wordTrace_append hprefix tailTrace_2662034
  have hstable : (prefixWord ++ tailWord_2662034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662034).length < 2 ^ (prefixWord ++ tailWord_2662034).sum := by decide
  have hdescent : baseEnd_2662034 < baseStart_2662034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662047 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2662047 : Nat := 118140960795 + 2662047 * 2 ^ 59
def prefixEnd_2662047 : Nat := 4983230072969 + 3 ^ 40 * 2662047 * 2
def baseEnd_2662047 : Nat := 1366909635859451462569975

theorem tailTrace_2662047 : CollatzResearch.WordTrace tailWord_2662047 prefixEnd_2662047 1366909635859451462569975 := by
  unfold tailWord_2662047
  simp only [CollatzResearch.WordTrace]
  refine ⟨97092830586865835276856395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64728553724577223517904263 97092830586865835276856395)
  ·
    refine ⟨145639245880298752915284593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97092830586865835276856395 145639245880298752915284593)
    ·
      refine ⟨109229434410224064686463445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145639245880298752915284593 109229434410224064686463445)
      ·
        refine ⟨2560064868989626516088987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 109229434410224064686463445 2560064868989626516088987)
        ·
          refine ⟨3840097303484439774133481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560064868989626516088987 3840097303484439774133481)
          ·
            refine ⟨2880072977613329830600111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3840097303484439774133481 2880072977613329830600111)
            ·
              refine ⟨4320109466419994745900167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880072977613329830600111 4320109466419994745900167)
              ·
                refine ⟨6480164199629992118850251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4320109466419994745900167 6480164199629992118850251)
                ·
                  refine ⟨9720246299444988178275377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6480164199629992118850251 9720246299444988178275377)
                  ·
                    refine ⟨7290184724583741133706533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9720246299444988178275377 7290184724583741133706533)
                    ·
                      refine ⟨1366909635859451462569975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7290184724583741133706533 1366909635859451462569975)
                      ·
                        rfl

theorem cell23_2662047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2662047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662047 prefixEnd_2662047 := by exact prefixLift 2662047
  have htrace : WordTrace (prefixWord ++ tailWord_2662047) baseStart_2662047 baseEnd_2662047 := by
    simpa [prefixWord, tailWord_2662047, baseEnd_2662047] using wordTrace_append hprefix tailTrace_2662047
  have hstable : (prefixWord ++ tailWord_2662047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662047).length < 2 ^ (prefixWord ++ tailWord_2662047).sum := by decide
  have hdescent : baseEnd_2662047 < baseStart_2662047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662066 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_2662066 : Nat := 118140960795 + 2662066 * 2 ^ 59
def prefixEnd_2662066 : Nat := 4983230072969 + 3 ^ 40 * 2662066 * 2
def baseEnd_2662066 : Nat := 455639797330628962744129

theorem tailTrace_2662066 : CollatzResearch.WordTrace tailWord_2662066 prefixEnd_2662066 455639797330628962744129 := by
  unfold tailWord_2662066
  simp only [CollatzResearch.WordTrace]
  refine ⟨24273380893449250380449513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64729015715864667681198701 24273380893449250380449513)
  ·
    refine ⟨18205035670086937785337135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24273380893449250380449513 18205035670086937785337135)
    ·
      refine ⟨27307553505130406678005703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18205035670086937785337135 27307553505130406678005703)
      ·
        refine ⟨40961330257695610017008555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27307553505130406678005703 40961330257695610017008555)
        ·
          refine ⟨61441995386543415025512833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40961330257695610017008555 61441995386543415025512833)
          ·
            refine ⟨46081496539907561269134625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61441995386543415025512833 46081496539907561269134625)
            ·
              refine ⟨34561122404930670951850969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46081496539907561269134625 34561122404930670951850969)
              ·
                refine ⟨25920841803698003213888227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34561122404930670951850969 25920841803698003213888227)
                ·
                  refine ⟨38881262705547004820832341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25920841803698003213888227 38881262705547004820832341)
                  ·
                    refine ⟨455639797330628962744129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38881262705547004820832341 455639797330628962744129)
                    ·
                      rfl

theorem cell23_2662066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_2662066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662066 prefixEnd_2662066 := by exact prefixLift 2662066
  have htrace : WordTrace (prefixWord ++ tailWord_2662066) baseStart_2662066 baseEnd_2662066 := by
    simpa [prefixWord, tailWord_2662066, baseEnd_2662066] using wordTrace_append hprefix tailTrace_2662066
  have hstable : (prefixWord ++ tailWord_2662066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662066).length < 2 ^ (prefixWord ++ tailWord_2662066).sum := by decide
  have hdescent : baseEnd_2662066 < baseStart_2662066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662096 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 7]
def baseStart_2662096 : Nat := 118140960795 + 2662096 * 2 ^ 59
def prefixEnd_2662096 : Nat := 4983230072969 + 3 ^ 40 * 2662096 * 2
def baseEnd_2662096 : Nat := 151881644045724641206361

theorem tailTrace_2662096 : CollatzResearch.WordTrace tailWord_2662096 prefixEnd_2662096 151881644045724641206361 := by
  unfold tailWord_2662096
  simp only [CollatzResearch.WordTrace]
  refine ⟨48547308881844158322695071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64729745175792211096926761 48547308881844158322695071)
  ·
    refine ⟨72820963322766237484042607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48547308881844158322695071 72820963322766237484042607)
    ·
      refine ⟨109231444984149356226063911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72820963322766237484042607 109231444984149356226063911)
      ·
        refine ⟨163847167476224034339095867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109231444984149356226063911 163847167476224034339095867)
        ·
          refine ⟨245770751214336051508643801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163847167476224034339095867 245770751214336051508643801)
          ·
            refine ⟨184328063410752038631482851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245770751214336051508643801 184328063410752038631482851)
            ·
              refine ⟨276492095116128057947224277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184328063410752038631482851 276492095116128057947224277)
              ·
                refine ⟨6480283479284251358138069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 276492095116128057947224277 6480283479284251358138069)
                ·
                  refine ⟨151881644045724641206361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6480283479284251358138069 151881644045724641206361)
                  ·
                    rfl

theorem cell23_2662096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 7].length) (baseStart_2662096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662096 prefixEnd_2662096 := by exact prefixLift 2662096
  have htrace : WordTrace (prefixWord ++ tailWord_2662096) baseStart_2662096 baseEnd_2662096 := by
    simpa [prefixWord, tailWord_2662096, baseEnd_2662096] using wordTrace_append hprefix tailTrace_2662096
  have hstable : (prefixWord ++ tailWord_2662096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662096).length < 2 ^ (prefixWord ++ tailWord_2662096).sum := by decide
  have hdescent : baseEnd_2662096 < baseStart_2662096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662130 : List Nat := [3, 2, 1, 3, 1, 1, 2, 5, 5]
def baseStart_2662130 : Nat := 118140960795 + 2662130 * 2 ^ 59
def prefixEnd_2662130 : Nat := 4983230072969 + 3 ^ 40 * 2662130 * 2
def baseEnd_2662130 : Nat := 151883583861530515314677

theorem tailTrace_2662130 : CollatzResearch.WordTrace tailWord_2662130 prefixEnd_2662130 151883583861530515314677 := by
  unfold tailWord_2662130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24273964461391285113031961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64730571897043426968085229 24273964461391285113031961)
  ·
    refine ⟨18205473346043463834773971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24273964461391285113031961 18205473346043463834773971)
    ·
      refine ⟨27308210019065195752160957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18205473346043463834773971 27308210019065195752160957)
      ·
        refine ⟨10240578757149448407060359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27308210019065195752160957 10240578757149448407060359)
        ·
          refine ⟨15360868135724172610590539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10240578757149448407060359 15360868135724172610590539)
          ·
            refine ⟨23041302203586258915885809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15360868135724172610590539 23041302203586258915885809)
            ·
              refine ⟨17280976652689694186914357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23041302203586258915885809 17280976652689694186914357)
              ·
                refine ⟨1620091561189658830023221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17280976652689694186914357 1620091561189658830023221)
                ·
                  refine ⟨151883583861530515314677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1620091561189658830023221 151883583861530515314677)
                  ·
                    rfl

theorem cell23_2662130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_2662130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662130 prefixEnd_2662130 := by exact prefixLift 2662130
  have htrace : WordTrace (prefixWord ++ tailWord_2662130) baseStart_2662130 baseEnd_2662130 := by
    simpa [prefixWord, tailWord_2662130, baseEnd_2662130] using wordTrace_append hprefix tailTrace_2662130
  have hstable : (prefixWord ++ tailWord_2662130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662130).length < 2 ^ (prefixWord ++ tailWord_2662130).sum := by decide
  have hdescent : baseEnd_2662130 < baseStart_2662130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662143 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 2, 5]
def baseStart_2662143 : Nat := 118140960795 + 2662143 * 2 ^ 59
def prefixEnd_2662143 : Nat := 4983230072969 + 3 ^ 40 * 2662143 * 2
def baseEnd_2662143 : Nat := 455652976667427695656511

theorem tailTrace_2662143 : CollatzResearch.WordTrace tailWord_2662143 prefixEnd_2662143 455652976667427695656511 := by
  unfold tailWord_2662143
  simp only [CollatzResearch.WordTrace]
  refine ⟨97096331994518043672351083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64730887996345362448234055 97096331994518043672351083)
  ·
    refine ⟨145644497991777065508526625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97096331994518043672351083 145644497991777065508526625)
    ·
      refine ⟨109233373493832799131394969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145644497991777065508526625 109233373493832799131394969)
      ·
        refine ⟨81925030120374599348546227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109233373493832799131394969 81925030120374599348546227)
        ·
          refine ⟨122887545180561899022819341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81925030120374599348546227 122887545180561899022819341)
          ·
            refine ⟨46082829442710712133557253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122887545180561899022819341 46082829442710712133557253)
            ·
              refine ⟨8640530520508258525041985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46082829442710712133557253 8640530520508258525041985)
              ·
                refine ⟨6480397890381193893781489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8640530520508258525041985 6480397890381193893781489)
                ·
                  refine ⟨4860298417785895420336117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6480397890381193893781489 4860298417785895420336117)
                  ·
                    refine ⟨455652976667427695656511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4860298417785895420336117 455652976667427695656511)
                    ·
                      rfl

theorem cell23_2662143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_2662143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662143 prefixEnd_2662143 := by exact prefixLift 2662143
  have htrace : WordTrace (prefixWord ++ tailWord_2662143) baseStart_2662143 baseEnd_2662143 := by
    simpa [prefixWord, tailWord_2662143, baseEnd_2662143] using wordTrace_append hprefix tailTrace_2662143
  have hstable : (prefixWord ++ tailWord_2662143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662143).length < 2 ^ (prefixWord ++ tailWord_2662143).sum := by decide
  have hdescent : baseEnd_2662143 < baseStart_2662143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662164 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 7]
def baseStart_2662164 : Nat := 118140960795 + 2662164 * 2 ^ 59
def prefixEnd_2662164 : Nat := 4983230072969 + 3 ^ 40 * 2662164 * 2
def baseEnd_2662164 : Nat := 151885523677336389422993

theorem tailTrace_2662164 : CollatzResearch.WordTrace tailWord_2662164 prefixEnd_2662164 151885523677336389422993 := by
  unfold tailWord_2662164
  simp only [CollatzResearch.WordTrace]
  refine ⟨48548548963720982129432773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64731398618294642839243697 48548548963720982129432773)
  ·
    refine ⟨9102852930697684149268645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48548548963720982129432773 9102852930697684149268645)
    ·
      refine ⟨1706784924505815777987871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9102852930697684149268645 1706784924505815777987871)
      ·
        refine ⟨2560177386758723666981807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706784924505815777987871 2560177386758723666981807)
        ·
          refine ⟨3840266080138085500472711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560177386758723666981807 3840266080138085500472711)
          ·
            refine ⟨5760399120207128250709067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3840266080138085500472711 5760399120207128250709067)
            ·
              refine ⟨8640598680310692376063601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5760399120207128250709067 8640598680310692376063601)
              ·
                refine ⟨6480449010233019282047701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8640598680310692376063601 6480449010233019282047701)
                ·
                  refine ⟨151885523677336389422993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6480449010233019282047701 151885523677336389422993)
                  ·
                    rfl

theorem cell23_2662164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_2662164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662164 prefixEnd_2662164 := by exact prefixLift 2662164
  have htrace : WordTrace (prefixWord ++ tailWord_2662164) baseStart_2662164 baseEnd_2662164 := by
    simpa [prefixWord, tailWord_2662164, baseEnd_2662164] using wordTrace_append hprefix tailTrace_2662164
  have hstable : (prefixWord ++ tailWord_2662164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662164).length < 2 ^ (prefixWord ++ tailWord_2662164).sum := by decide
  have hdescent : baseEnd_2662164 < baseStart_2662164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662180 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2662180 : Nat := 118140960795 + 2662180 * 2 ^ 59
def prefixEnd_2662180 : Nat := 4983230072969 + 3 ^ 40 * 2662180 * 2
def baseEnd_2662180 : Nat := 1366977928786499442206863

theorem tailTrace_2662180 : CollatzResearch.WordTrace tailWord_2662180 prefixEnd_2662180 1366977928786499442206863 := by
  unfold tailWord_2662180
  simp only [CollatzResearch.WordTrace]
  refine ⟨48548840747691999495723997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64731787663589332660965329 48548840747691999495723997)
  ·
    refine ⟨18205815280384499810896499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48548840747691999495723997 18205815280384499810896499)
    ·
      refine ⟨27308722920576749716344749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18205815280384499810896499 27308722920576749716344749)
      ·
        refine ⟨10240771095216281143629281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27308722920576749716344749 10240771095216281143629281)
        ·
          refine ⟨7680578321412210857721961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10240771095216281143629281 7680578321412210857721961)
          ·
            refine ⟨5760433741059158143291471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7680578321412210857721961 5760433741059158143291471)
            ·
              refine ⟨8640650611588737214937207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5760433741059158143291471 8640650611588737214937207)
              ·
                refine ⟨12960975917383105822405811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8640650611588737214937207 12960975917383105822405811)
                ·
                  refine ⟨19441463876074658733608717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12960975917383105822405811 19441463876074658733608717)
                  ·
                    refine ⟨7290548953527997025103269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19441463876074658733608717 7290548953527997025103269)
                    ·
                      refine ⟨1366977928786499442206863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7290548953527997025103269 1366977928786499442206863)
                      ·
                        rfl

theorem cell23_2662180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2662180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662180 prefixEnd_2662180 := by exact prefixLift 2662180
  have htrace : WordTrace (prefixWord ++ tailWord_2662180) baseStart_2662180 baseEnd_2662180 := by
    simpa [prefixWord, tailWord_2662180, baseEnd_2662180] using wordTrace_append hprefix tailTrace_2662180
  have hstable : (prefixWord ++ tailWord_2662180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662180).length < 2 ^ (prefixWord ++ tailWord_2662180).sum := by decide
  have hdescent : baseEnd_2662180 < baseStart_2662180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662193 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2662193 : Nat := 118140960795 + 2662193 * 2 ^ 59
def prefixEnd_2662193 : Nat := 4983230072969 + 3 ^ 40 * 2662193 * 2
def baseEnd_2662193 : Nat := 1366984604035007891344303

theorem tailTrace_2662193 : CollatzResearch.WordTrace tailWord_2662193 prefixEnd_2662193 1366984604035007891344303 := by
  unfold tailWord_2662193
  simp only [CollatzResearch.WordTrace]
  refine ⟨97098155644336902211671233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64732103762891268141114155 97098155644336902211671233)
  ·
    refine ⟨72823616733252676658753425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97098155644336902211671233 72823616733252676658753425)
    ·
      refine ⟨54617712549939507494065069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72823616733252676658753425 54617712549939507494065069)
      ·
        refine ⟨20481642206227315310274401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54617712549939507494065069 20481642206227315310274401)
        ·
          refine ⟨15361231654670486482705801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20481642206227315310274401 15361231654670486482705801)
          ·
            refine ⟨11520923741002864862029351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15361231654670486482705801 11520923741002864862029351)
            ·
              refine ⟨17281385611504297293044027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11520923741002864862029351 17281385611504297293044027)
              ·
                refine ⟨25922078417256445939566041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17281385611504297293044027 25922078417256445939566041)
                ·
                  refine ⟨19441558812942334454674531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25922078417256445939566041 19441558812942334454674531)
                  ·
                    refine ⟨29162338219413501682011797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19441558812942334454674531 29162338219413501682011797)
                    ·
                      refine ⟨1366984604035007891344303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29162338219413501682011797 1366984604035007891344303)
                      ·
                        rfl

theorem cell23_2662193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2662193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662193 prefixEnd_2662193 := by exact prefixLift 2662193
  have htrace : WordTrace (prefixWord ++ tailWord_2662193) baseStart_2662193 baseEnd_2662193 := by
    simpa [prefixWord, tailWord_2662193, baseEnd_2662193] using wordTrace_append hprefix tailTrace_2662193
  have hstable : (prefixWord ++ tailWord_2662193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662193).length < 2 ^ (prefixWord ++ tailWord_2662193).sum := by decide
  have hdescent : baseEnd_2662193 < baseStart_2662193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662207 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 3, 4]
def baseStart_2662207 : Nat := 118140960795 + 2662207 * 2 ^ 59
def prefixEnd_2662207 : Nat := 4983230072969 + 3 ^ 40 * 2662207 * 2
def baseEnd_2662207 : Nat := 455663930921390278856413

theorem tailTrace_2662207 : CollatzResearch.WordTrace tailWord_2662207 prefixEnd_2662207 455663930921390278856413 := by
  unfold tailWord_2662207
  simp only [CollatzResearch.WordTrace]
  refine ⟨97098666266286182602680875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64732444177524121735120583 97098666266286182602680875)
  ·
    refine ⟨145647999399429273904021313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97098666266286182602680875 145647999399429273904021313)
    ·
      refine ⟨109235999549571955428015985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145647999399429273904021313 109235999549571955428015985)
      ·
        refine ⟨81926999662178966571011989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109235999549571955428015985 81926999662178966571011989)
        ·
          refine ⟨3840328109164639058016187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81926999662178966571011989 3840328109164639058016187)
          ·
            refine ⟨5760492163746958587024281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3840328109164639058016187 5760492163746958587024281)
            ·
              refine ⟨4320369122810218940268211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5760492163746958587024281 4320369122810218940268211)
              ·
                refine ⟨6480553684215328410402317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4320369122810218940268211 6480553684215328410402317)
                ·
                  refine ⟨2430207631580748153900869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6480553684215328410402317 2430207631580748153900869)
                  ·
                    refine ⟨455663930921390278856413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2430207631580748153900869 455663930921390278856413)
                    ·
                      rfl

theorem cell23_2662207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 4].length) (baseStart_2662207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662207 prefixEnd_2662207 := by exact prefixLift 2662207
  have htrace : WordTrace (prefixWord ++ tailWord_2662207) baseStart_2662207 baseEnd_2662207 := by
    simpa [prefixWord, tailWord_2662207, baseEnd_2662207] using wordTrace_append hprefix tailTrace_2662207
  have hstable : (prefixWord ++ tailWord_2662207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662207).length < 2 ^ (prefixWord ++ tailWord_2662207).sum := by decide
  have hdescent : baseEnd_2662207 < baseStart_2662207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662257 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 2, 3, 2]
def baseStart_2662257 : Nat := 118140960795 + 2662257 * 2 ^ 59
def prefixEnd_2662257 : Nat := 4983230072969 + 3 ^ 40 * 2662257 * 2
def baseEnd_2662257 : Nat := 1367017466796895640944009

theorem tailTrace_2662257 : CollatzResearch.WordTrace tailWord_2662257 prefixEnd_2662257 1367017466796895640944009 := by
  unfold tailWord_2662257
  simp only [CollatzResearch.WordTrace]
  refine ⟨97100489916105041142001025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64733659944070027428000683 97100489916105041142001025)
  ·
    refine ⟨72825367437078780856500769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97100489916105041142001025 72825367437078780856500769)
    ·
      refine ⟨54619025577809085642375577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72825367437078780856500769 54619025577809085642375577)
      ·
        refine ⟨40964269183356814231781683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54619025577809085642375577 40964269183356814231781683)
        ·
          refine ⟨61446403775035221347672525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40964269183356814231781683 61446403775035221347672525)
          ·
            refine ⟨23042401415638208005377197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61446403775035221347672525 23042401415638208005377197)
            ·
              refine ⟨8640900530864328002016449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23042401415638208005377197 8640900530864328002016449)
              ·
                refine ⟨6480675398148246001512337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8640900530864328002016449 6480675398148246001512337)
                ·
                  refine ⟨4860506548611184501134253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6480675398148246001512337 4860506548611184501134253)
                  ·
                    refine ⟨1822689955729194187925345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4860506548611184501134253 1822689955729194187925345)
                    ·
                      refine ⟨1367017466796895640944009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822689955729194187925345 1367017466796895640944009)
                      ·
                        rfl

theorem cell23_2662257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_2662257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662257 prefixEnd_2662257 := by exact prefixLift 2662257
  have htrace : WordTrace (prefixWord ++ tailWord_2662257) baseStart_2662257 baseEnd_2662257 := by
    simpa [prefixWord, tailWord_2662257, baseEnd_2662257] using wordTrace_append hprefix tailTrace_2662257
  have hstable : (prefixWord ++ tailWord_2662257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662257).length < 2 ^ (prefixWord ++ tailWord_2662257).sum := by decide
  have hdescent : baseEnd_2662257 < baseStart_2662257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662293 : List Nat := [1, 3, 2, 1, 1, 3, 1, 11]
def baseStart_2662293 : Nat := 118140960795 + 2662293 * 2 ^ 59
def prefixEnd_2662293 : Nat := 4983230072969 + 3 ^ 40 * 2662293 * 2
def baseEnd_2662293 : Nat := 50630961188905833336809

theorem tailTrace_2662293 : CollatzResearch.WordTrace tailWord_2662293 prefixEnd_2662293 50630961188905833336809 := by
  unfold tailWord_2662293
  simp only [CollatzResearch.WordTrace]
  refine ⟨97101802943974619290311533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64734535295983079526874355 97101802943974619290311533)
  ·
    refine ⟨36413176103990482233866825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97101802943974619290311533 36413176103990482233866825)
    ·
      refine ⟨27309882077992861675400119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36413176103990482233866825 27309882077992861675400119)
      ·
        refine ⟨40964823116989292513100179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27309882077992861675400119 40964823116989292513100179)
        ·
          refine ⟨61447234675483938769650269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40964823116989292513100179 61447234675483938769650269)
          ·
            refine ⟨23042713003306477038618851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61447234675483938769650269 23042713003306477038618851)
            ·
              refine ⟨34564069504959715557928277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23042713003306477038618851 34564069504959715557928277)
              ·
                refine ⟨50630961188905833336809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 34564069504959715557928277 50630961188905833336809)
                ·
                  rfl

theorem cell23_2662293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 11].length) (baseStart_2662293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662293 prefixEnd_2662293 := by exact prefixLift 2662293
  have htrace : WordTrace (prefixWord ++ tailWord_2662293) baseStart_2662293 baseEnd_2662293 := by
    simpa [prefixWord, tailWord_2662293, baseEnd_2662293] using wordTrace_append hprefix tailTrace_2662293
  have hstable : (prefixWord ++ tailWord_2662293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662293).length < 2 ^ (prefixWord ++ tailWord_2662293).sum := by decide
  have hdescent : baseEnd_2662293 < baseStart_2662293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662313 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_2662313 : Nat := 118140960795 + 2662313 * 2 ^ 59
def prefixEnd_2662313 : Nat := 4983230072969 + 3 ^ 40 * 2662313 * 2
def baseEnd_2662313 : Nat := 1367046221713547421843751

theorem tailTrace_2662313 : CollatzResearch.WordTrace tailWord_2662313 prefixEnd_2662313 1367046221713547421843751 := by
  unfold tailWord_2662313
  simp only [CollatzResearch.WordTrace]
  refine ⟨97102532403902162706039593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64735021602601441804026395 97102532403902162706039593)
  ·
    refine ⟨72826899302926622029529695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97102532403902162706039593 72826899302926622029529695)
    ·
      refine ⟨109240348954389933044294543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72826899302926622029529695 109240348954389933044294543)
      ·
        refine ⟨163860523431584899566441815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109240348954389933044294543 163860523431584899566441815)
        ·
          refine ⟨245790785147377349349662723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163860523431584899566441815 245790785147377349349662723)
          ·
            refine ⟨368686177721066024024494085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245790785147377349349662723 368686177721066024024494085)
            ·
              refine ⟨69128658322699879504592641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 368686177721066024024494085 69128658322699879504592641)
              ·
                refine ⟨51846493742024909628444481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69128658322699879504592641 51846493742024909628444481)
                ·
                  refine ⟨38884870306518682221333361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51846493742024909628444481 38884870306518682221333361)
                  ·
                    refine ⟨29163652729889011666000021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38884870306518682221333361 29163652729889011666000021)
                    ·
                      refine ⟨1367046221713547421843751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29163652729889011666000021 1367046221713547421843751)
                      ·
                        rfl

theorem cell23_2662313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_2662313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662313 prefixEnd_2662313 := by exact prefixLift 2662313
  have htrace : WordTrace (prefixWord ++ tailWord_2662313) baseStart_2662313 baseEnd_2662313 := by
    simpa [prefixWord, tailWord_2662313, baseEnd_2662313] using wordTrace_append hprefix tailTrace_2662313
  have hstable : (prefixWord ++ tailWord_2662313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662313).length < 2 ^ (prefixWord ++ tailWord_2662313).sum := by decide
  have hdescent : baseEnd_2662313 < baseStart_2662313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662323 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 1, 9]
def baseStart_2662323 : Nat := 118140960795 + 2662323 * 2 ^ 59
def prefixEnd_2662323 : Nat := 4983230072969 + 3 ^ 40 * 2662323 * 2
def baseEnd_2662323 : Nat := 455683785506697460906235

theorem tailTrace_2662323 : CollatzResearch.WordTrace tailWord_2662323 prefixEnd_2662323 455683785506697460906235 := by
  unfold tailWord_2662323
  simp only [CollatzResearch.WordTrace]
  refine ⟨97102897133865934413903623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64735264755910622942602415 97102897133865934413903623)
  ·
    refine ⟨145654345700798901620855435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97102897133865934413903623 145654345700798901620855435)
    ·
      refine ⟨218481518551198352431283153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145654345700798901620855435 218481518551198352431283153)
      ·
        refine ⟨163861138913398764323462365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218481518551198352431283153 163861138913398764323462365)
        ·
          refine ⟨61447927092524536621298387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163861138913398764323462365 61447927092524536621298387)
          ·
            refine ⟨92171890638786804931947581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61447927092524536621298387 92171890638786804931947581)
            ·
              refine ⟨34564458989545051849480343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92171890638786804931947581 34564458989545051849480343)
              ·
                refine ⟨51846688484317577774220515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34564458989545051849480343 51846688484317577774220515)
                ·
                  refine ⟨77770032726476366661330773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51846688484317577774220515 77770032726476366661330773)
                  ·
                    refine ⟨455683785506697460906235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 77770032726476366661330773 455683785506697460906235)
                    ·
                      rfl

theorem cell23_2662323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 9].length) (baseStart_2662323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662323 prefixEnd_2662323 := by exact prefixLift 2662323
  have htrace : WordTrace (prefixWord ++ tailWord_2662323) baseStart_2662323 baseEnd_2662323 := by
    simpa [prefixWord, tailWord_2662323, baseEnd_2662323] using wordTrace_append hprefix tailTrace_2662323
  have hstable : (prefixWord ++ tailWord_2662323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662323).length < 2 ^ (prefixWord ++ tailWord_2662323).sum := by decide
  have hdescent : baseEnd_2662323 < baseStart_2662323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662347 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 3, 3, 2]
def baseStart_2662347 : Nat := 118140960795 + 2662347 * 2 ^ 59
def prefixEnd_2662347 : Nat := 4983230072969 + 3 ^ 40 * 2662347 * 2
def baseEnd_2662347 : Nat := 1367063680055800288818595

theorem tailTrace_2662347 : CollatzResearch.WordTrace tailWord_2662347 prefixEnd_2662347 1367063680055800288818595 := by
  unfold tailWord_2662347
  simp only [CollatzResearch.WordTrace]
  refine ⟨97103772485778986512777295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64735848323852657675184863 97103772485778986512777295)
  ·
    refine ⟨145655658728668479769165943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97103772485778986512777295 145655658728668479769165943)
    ·
      refine ⟨218483488093002719653748915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145655658728668479769165943 218483488093002719653748915)
      ·
        refine ⟨327725232139504079480623373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218483488093002719653748915 327725232139504079480623373)
        ·
          refine ⟨122896962052314029805233765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327725232139504079480623373 122896962052314029805233765)
          ·
            refine ⟨23043180384808880588481331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122896962052314029805233765 23043180384808880588481331)
            ·
              refine ⟨34564770577213320882721997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23043180384808880588481331 34564770577213320882721997)
              ·
                refine ⟨12961788966454995331020749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34564770577213320882721997 12961788966454995331020749)
                ·
                  refine ⟨4860670862420623249132781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12961788966454995331020749 4860670862420623249132781)
                  ·
                    refine ⟨1822751573407733718424793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4860670862420623249132781 1822751573407733718424793)
                    ·
                      refine ⟨1367063680055800288818595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822751573407733718424793 1367063680055800288818595)
                      ·
                        rfl

theorem cell23_2662347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 3, 2].length) (baseStart_2662347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662347 prefixEnd_2662347 := by exact prefixLift 2662347
  have htrace : WordTrace (prefixWord ++ tailWord_2662347) baseStart_2662347 baseEnd_2662347 := by
    simpa [prefixWord, tailWord_2662347, baseEnd_2662347] using wordTrace_append hprefix tailTrace_2662347
  have hstable : (prefixWord ++ tailWord_2662347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662347).length < 2 ^ (prefixWord ++ tailWord_2662347).sum := by decide
  have hdescent : baseEnd_2662347 < baseStart_2662347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662350 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2662350 : Nat := 118140960795 + 2662350 * 2 ^ 59
def prefixEnd_2662350 : Nat := 4983230072969 + 3 ^ 40 * 2662350 * 2
def baseEnd_2662350 : Nat := 1367065220497763777081081

theorem tailTrace_2662350 : CollatzResearch.WordTrace tailWord_2662350 prefixEnd_2662350 1367065220497763777081081 := by
  unfold tailWord_2662350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12137985238096014753142063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64735921269845412016757669 12137985238096014753142063)
  ·
    refine ⟨18206977857144022129713095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12137985238096014753142063 18206977857144022129713095)
    ·
      refine ⟨27310466785716033194569643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18206977857144022129713095 27310466785716033194569643)
      ·
        refine ⟨40965700178574049791854465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27310466785716033194569643 40965700178574049791854465)
        ·
          refine ⟨30724275133930537343890849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40965700178574049791854465 30724275133930537343890849)
          ·
            refine ⟨23043206350447903007918137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30724275133930537343890849 23043206350447903007918137)
            ·
              refine ⟨17282404762835927255938603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23043206350447903007918137 17282404762835927255938603)
              ·
                refine ⟨25923607144253890883907905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17282404762835927255938603 25923607144253890883907905)
                ·
                  refine ⟨19442705358190418162930929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25923607144253890883907905 19442705358190418162930929)
                  ·
                    refine ⟨14582029018642813622198197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19442705358190418162930929 14582029018642813622198197)
                    ·
                      refine ⟨1367065220497763777081081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14582029018642813622198197 1367065220497763777081081)
                      ·
                        rfl

theorem cell23_2662350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2662350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662350 prefixEnd_2662350 := by exact prefixLift 2662350
  have htrace : WordTrace (prefixWord ++ tailWord_2662350) baseStart_2662350 baseEnd_2662350 := by
    simpa [prefixWord, tailWord_2662350, baseEnd_2662350] using wordTrace_append hprefix tailTrace_2662350
  have hstable : (prefixWord ++ tailWord_2662350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662350).length < 2 ^ (prefixWord ++ tailWord_2662350).sum := by decide
  have hdescent : baseEnd_2662350 < baseStart_2662350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662371 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2662371 : Nat := 118140960795 + 2662371 * 2 ^ 59
def prefixEnd_2662371 : Nat := 4983230072969 + 3 ^ 40 * 2662371 * 2
def baseEnd_2662371 : Nat := 1367076003591508194918485

theorem tailTrace_2662371 : CollatzResearch.WordTrace tailWord_2662371 prefixEnd_2662371 1367076003591508194918485 := by
  unfold tailWord_2662371
  simp only [CollatzResearch.WordTrace]
  refine ⟨97104647837692038611650967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64736431891794692407767311 97104647837692038611650967)
  ·
    refine ⟨145656971756538057917476451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97104647837692038611650967 145656971756538057917476451)
    ·
      refine ⟨218485457634807086876214677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145656971756538057917476451 218485457634807086876214677)
      ·
        refine ⟨10241505826631582197322563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 218485457634807086876214677 10241505826631582197322563)
        ·
          refine ⟨15362258739947373295983845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10241505826631582197322563 15362258739947373295983845)
          ·
            refine ⟨2880423513740132492996971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15362258739947373295983845 2880423513740132492996971)
            ·
              refine ⟨4320635270610198739495457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880423513740132492996971 4320635270610198739495457)
              ·
                refine ⟨3240476452957649054621593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4320635270610198739495457 3240476452957649054621593)
                ·
                  refine ⟨2430357339718236790966195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3240476452957649054621593 2430357339718236790966195)
                  ·
                    refine ⟨3645536009577355186449293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2430357339718236790966195 3645536009577355186449293)
                    ·
                      refine ⟨1367076003591508194918485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3645536009577355186449293 1367076003591508194918485)
                      ·
                        rfl

theorem cell23_2662371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2662371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662371 prefixEnd_2662371 := by exact prefixLift 2662371
  have htrace : WordTrace (prefixWord ++ tailWord_2662371) baseStart_2662371 baseEnd_2662371 := by
    simpa [prefixWord, tailWord_2662371, baseEnd_2662371] using wordTrace_append hprefix tailTrace_2662371
  have hstable : (prefixWord ++ tailWord_2662371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662371).length < 2 ^ (prefixWord ++ tailWord_2662371).sum := by decide
  have hdescent : baseEnd_2662371 < baseStart_2662371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662380 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 3]
def baseStart_2662380 : Nat := 118140960795 + 2662380 * 2 ^ 59
def prefixEnd_2662380 : Nat := 4983230072969 + 3 ^ 40 * 2662380 * 2
def baseEnd_2662380 : Nat := 1367080624917398659705943

theorem tailTrace_2662380 : CollatzResearch.WordTrace tailWord_2662380 prefixEnd_2662380 1367080624917398659705943 := by
  unfold tailWord_2662380
  simp only [CollatzResearch.WordTrace]
  refine ⟨48552488047329716574364297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64736650729772955432485729 48552488047329716574364297)
  ·
    refine ⟨36414366035497287430773223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48552488047329716574364297 36414366035497287430773223)
    ·
      refine ⟨54621549053245931146159835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36414366035497287430773223 54621549053245931146159835)
      ·
        refine ⟨81932323579868896719239753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54621549053245931146159835 81932323579868896719239753)
        ·
          refine ⟨61449242684901672539429815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81932323579868896719239753 61449242684901672539429815)
          ·
            refine ⟨92173864027352508809144723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61449242684901672539429815 92173864027352508809144723)
            ·
              refine ⟨138260796041028763213717085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92173864027352508809144723 138260796041028763213717085)
              ·
                refine ⟨51847798515385786205143907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138260796041028763213717085 51847798515385786205143907)
                ·
                  refine ⟨77771697773078679307715861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51847798515385786205143907 77771697773078679307715861)
                  ·
                    refine ⟨3645548333113063092549181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77771697773078679307715861 3645548333113063092549181)
                    ·
                      refine ⟨1367080624917398659705943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3645548333113063092549181 1367080624917398659705943)
                      ·
                        rfl

theorem cell23_2662380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_2662380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662380 prefixEnd_2662380 := by exact prefixLift 2662380
  have htrace : WordTrace (prefixWord ++ tailWord_2662380) baseStart_2662380 baseEnd_2662380 := by
    simpa [prefixWord, tailWord_2662380, baseEnd_2662380] using wordTrace_append hprefix tailTrace_2662380
  have hstable : (prefixWord ++ tailWord_2662380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662380).length < 2 ^ (prefixWord ++ tailWord_2662380).sum := by decide
  have hdescent : baseEnd_2662380 < baseStart_2662380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662398 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2662398 : Nat := 118140960795 + 2662398 * 2 ^ 59
def prefixEnd_2662398 : Nat := 4983230072969 + 3 ^ 40 * 2662398 * 2
def baseEnd_2662398 : Nat := 1367089867569179589280861

theorem tailTrace_2662398 : CollatzResearch.WordTrace tailWord_2662398 prefixEnd_2662398 1367089867569179589280861 := by
  unfold tailWord_2662398
  simp only [CollatzResearch.WordTrace]
  refine ⟨12138204076074277777860481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64737088405729481481922565 12138204076074277777860481)
  ·
    refine ⟨9103653057055708333395361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12138204076074277777860481 9103653057055708333395361)
    ·
      refine ⟨6827739792791781250046521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9103653057055708333395361 6827739792791781250046521)
      ·
        refine ⟨5120804844593835937534891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6827739792791781250046521 5120804844593835937534891)
        ·
          refine ⟨7681207266890753906302337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5120804844593835937534891 7681207266890753906302337)
          ·
            refine ⟨5760905450168065429726753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7681207266890753906302337 5760905450168065429726753)
            ·
              refine ⟨4320679087626049072295065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5760905450168065429726753 4320679087626049072295065)
              ·
                refine ⟨3240509315719536804221299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4320679087626049072295065 3240509315719536804221299)
                ·
                  refine ⟨4860763973579305206331949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240509315719536804221299 4860763973579305206331949)
                  ·
                    refine ⟨1822786490092239452374481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4860763973579305206331949 1822786490092239452374481)
                    ·
                      refine ⟨1367089867569179589280861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822786490092239452374481 1367089867569179589280861)
                      ·
                        rfl

theorem cell23_2662398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2662398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662398 prefixEnd_2662398 := by exact prefixLift 2662398
  have htrace : WordTrace (prefixWord ++ tailWord_2662398) baseStart_2662398 baseEnd_2662398 := by
    simpa [prefixWord, tailWord_2662398, baseEnd_2662398] using wordTrace_append hprefix tailTrace_2662398
  have hstable : (prefixWord ++ tailWord_2662398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662398).length < 2 ^ (prefixWord ++ tailWord_2662398).sum := by decide
  have hdescent : baseEnd_2662398 < baseStart_2662398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662406 : List Nat := [6, 2, 1, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2662406 : Nat := 118140960795 + 2662406 * 2 ^ 59
def prefixEnd_2662406 : Nat := 4983230072969 + 3 ^ 40 * 2662406 * 2
def baseEnd_2662406 : Nat := 1367093975414415557980825

theorem tailTrace_2662406 : CollatzResearch.WordTrace tailWord_2662406 prefixEnd_2662406 1367093975414415557980825 := by
  unfold tailWord_2662406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034560137267663737161721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64737282928376826392783381 3034560137267663737161721)
  ·
    refine ⟨2275920102950747802871291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3034560137267663737161721 2275920102950747802871291)
    ·
      refine ⟨3413880154426121704306937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2275920102950747802871291 3413880154426121704306937)
      ·
        refine ⟨2560410115819591278230203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3413880154426121704306937 2560410115819591278230203)
        ·
          refine ⟨3840615173729386917345305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560410115819591278230203 3840615173729386917345305)
          ·
            refine ⟨2880461380297040188008979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3840615173729386917345305 2880461380297040188008979)
            ·
              refine ⟨4320692070445560282013469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880461380297040188008979 4320692070445560282013469)
              ·
                refine ⟨1620259526417085105755051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4320692070445560282013469 1620259526417085105755051)
                ·
                  refine ⟨2430389289625627658632577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620259526417085105755051 2430389289625627658632577)
                  ·
                    refine ⟨1822791967219220743974433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2430389289625627658632577 1822791967219220743974433)
                    ·
                      refine ⟨1367093975414415557980825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822791967219220743974433 1367093975414415557980825)
                      ·
                        rfl

theorem cell23_2662406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2662406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662406 prefixEnd_2662406 := by exact prefixLift 2662406
  have htrace : WordTrace (prefixWord ++ tailWord_2662406) baseStart_2662406 baseEnd_2662406 := by
    simpa [prefixWord, tailWord_2662406, baseEnd_2662406] using wordTrace_append hprefix tailTrace_2662406
  have hstable : (prefixWord ++ tailWord_2662406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662406).length < 2 ^ (prefixWord ++ tailWord_2662406).sum := by decide
  have hdescent : baseEnd_2662406 < baseStart_2662406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662467 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 3, 6, 2]
def baseStart_2662467 : Nat := 118140960795 + 2662467 * 2 ^ 59
def prefixEnd_2662467 : Nat := 4983230072969 + 3 ^ 40 * 2662467 * 2
def baseEnd_2662467 : Nat := 1367125297734339819318043

theorem tailTrace_2662467 : CollatzResearch.WordTrace tailWord_2662467 prefixEnd_2662467 1367125297734339819318043 := by
  unfold tailWord_2662467
  simp only [CollatzResearch.WordTrace]
  refine ⟨97108149245344247007145655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64738766163562831338097103 97108149245344247007145655)
  ·
    refine ⟨145662223868016370510718483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97108149245344247007145655 145662223868016370510718483)
    ·
      refine ⟨218493335802024555766077725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145662223868016370510718483 218493335802024555766077725)
      ·
        refine ⟨81935000925759208412279147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218493335802024555766077725 81935000925759208412279147)
        ·
          refine ⟨122902501388638812618418721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81935000925759208412279147 122902501388638812618418721)
          ·
            refine ⟨92176876041479109463814041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122902501388638812618418721 92176876041479109463814041)
            ·
              refine ⟨69132657031109332097860531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92176876041479109463814041 69132657031109332097860531)
              ·
                refine ⟨103698985546663998146790797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69132657031109332097860531 103698985546663998146790797)
                ·
                  refine ⟨38887119579998999305046549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103698985546663998146790797 38887119579998999305046549)
                  ·
                    refine ⟨1822833730312453092424057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38887119579998999305046549 1822833730312453092424057)
                    ·
                      refine ⟨1367125297734339819318043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822833730312453092424057 1367125297734339819318043)
                      ·
                        rfl

theorem cell23_2662467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_2662467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662467 prefixEnd_2662467 := by exact prefixLift 2662467
  have htrace : WordTrace (prefixWord ++ tailWord_2662467) baseStart_2662467 baseEnd_2662467 := by
    simpa [prefixWord, tailWord_2662467, baseEnd_2662467] using wordTrace_append hprefix tailTrace_2662467
  have hstable : (prefixWord ++ tailWord_2662467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662467).length < 2 ^ (prefixWord ++ tailWord_2662467).sum := by decide
  have hdescent : baseEnd_2662467 < baseStart_2662467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662484 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_2662484 : Nat := 118140960795 + 2662484 * 2 ^ 59
def prefixEnd_2662484 : Nat := 4983230072969 + 3 ^ 40 * 2662484 * 2
def baseEnd_2662484 : Nat := 1367134026905466252805465

theorem tailTrace_2662484 : CollatzResearch.WordTrace tailWord_2662484 prefixEnd_2662484 1367134026905466252805465 := by
  unfold tailWord_2662484
  simp only [CollatzResearch.WordTrace]
  refine ⟨48554384643141329455257253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64739179524188439273676337 48554384643141329455257253)
  ·
    refine ⟨9103947120588999272860735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48554384643141329455257253 9103947120588999272860735)
    ·
      refine ⟨13655920680883498909291103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9103947120588999272860735 13655920680883498909291103)
      ·
        refine ⟨20483881021325248363936655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13655920680883498909291103 20483881021325248363936655)
        ·
          refine ⟨30725821531987872545904983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20483881021325248363936655 30725821531987872545904983)
          ·
            refine ⟨46088732297981808818857475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30725821531987872545904983 46088732297981808818857475)
            ·
              refine ⟨69133098446972713228286213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46088732297981808818857475 69133098446972713228286213)
              ·
                refine ⟨12962455958807383730303665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69133098446972713228286213 12962455958807383730303665)
                ·
                  refine ⟨9721841969105537797727749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12962455958807383730303665 9721841969105537797727749)
                  ·
                    refine ⟨1822845369207288337073953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9721841969105537797727749 1822845369207288337073953)
                    ·
                      refine ⟨1367134026905466252805465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822845369207288337073953 1367134026905466252805465)
                      ·
                        rfl

theorem cell23_2662484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_2662484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662484 prefixEnd_2662484 := by exact prefixLift 2662484
  have htrace : WordTrace (prefixWord ++ tailWord_2662484) baseStart_2662484 baseEnd_2662484 := by
    simpa [prefixWord, tailWord_2662484, baseEnd_2662484] using wordTrace_append hprefix tailTrace_2662484
  have hstable : (prefixWord ++ tailWord_2662484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662484).length < 2 ^ (prefixWord ++ tailWord_2662484).sum := by decide
  have hdescent : baseEnd_2662484 < baseStart_2662484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662521 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 2, 2, 3]
def baseStart_2662521 : Nat := 118140960795 + 2662521 * 2 ^ 59
def prefixEnd_2662521 : Nat := 4983230072969 + 3 ^ 40 * 2662521 * 2
def baseEnd_2662521 : Nat := 1367153025689682608042795

theorem tailTrace_2662521 : CollatzResearch.WordTrace tailWord_2662521 prefixEnd_2662521 1367153025689682608042795 := by
  unfold tailWord_2662521
  simp only [CollatzResearch.WordTrace]
  refine ⟨97110118787148614229611417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64740079191432409486407611 97110118787148614229611417)
  ·
    refine ⟨72832589090361460672208563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97110118787148614229611417 72832589090361460672208563)
    ·
      refine ⟨109248883635542191008312845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72832589090361460672208563 109248883635542191008312845)
      ·
        refine ⟨40968331363328321628117317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109248883635542191008312845 40968331363328321628117317)
        ·
          refine ⟨7681562130624060305271997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40968331363328321628117317 7681562130624060305271997)
          ·
            refine ⟨2880585798984022614476999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7681562130624060305271997 2880585798984022614476999)
            ·
              refine ⟨4320878698476033921715499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880585798984022614476999 4320878698476033921715499)
              ·
                refine ⟨6481318047714050882573249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4320878698476033921715499 6481318047714050882573249)
                ·
                  refine ⟨4860988535785538161929937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6481318047714050882573249 4860988535785538161929937)
                  ·
                    refine ⟨3645741401839153621447453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4860988535785538161929937 3645741401839153621447453)
                    ·
                      refine ⟨1367153025689682608042795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3645741401839153621447453 1367153025689682608042795)
                      ·
                        rfl

theorem cell23_2662521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_2662521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662521 prefixEnd_2662521 := by exact prefixLift 2662521
  have htrace : WordTrace (prefixWord ++ tailWord_2662521) baseStart_2662521 baseEnd_2662521 := by
    simpa [prefixWord, tailWord_2662521, baseEnd_2662521] using wordTrace_append hprefix tailTrace_2662521
  have hstable : (prefixWord ++ tailWord_2662521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662521).length < 2 ^ (prefixWord ++ tailWord_2662521).sum := by decide
  have hdescent : baseEnd_2662521 < baseStart_2662521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662544 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 4, 3, 2]
def baseStart_2662544 : Nat := 118140960795 + 2662544 * 2 ^ 59
def prefixEnd_2662544 : Nat := 4983230072969 + 3 ^ 40 * 2662544 * 2
def baseEnd_2662544 : Nat := 1367164835744736018055189

theorem tailTrace_2662544 : CollatzResearch.WordTrace tailWord_2662544 prefixEnd_2662544 1367164835744736018055189 := by
  unfold tailWord_2662544
  simp only [CollatzResearch.WordTrace]
  refine ⟨48555478833032644578849343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64740638444043526105132457 48555478833032644578849343)
  ·
    refine ⟨72833218249548966868274015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48555478833032644578849343 72833218249548966868274015)
    ·
      refine ⟨109249827374323450302411023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72833218249548966868274015 109249827374323450302411023)
      ·
        refine ⟨163874741061485175453616535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109249827374323450302411023 163874741061485175453616535)
        ·
          refine ⟨245812111592227763180424803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163874741061485175453616535 245812111592227763180424803)
          ·
            refine ⟨368718167388341644770637205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245812111592227763180424803 368718167388341644770637205)
            ·
              refine ⟨17283664096328514598623619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 368718167388341644770637205 17283664096328514598623619)
              ·
                refine ⟨25925496144492771897935429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17283664096328514598623619 25925496144492771897935429)
                ·
                  refine ⟨4861030527092394730862893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25925496144492771897935429 4861030527092394730862893)
                  ·
                    refine ⟨1822886447659648024073585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4861030527092394730862893 1822886447659648024073585)
                    ·
                      refine ⟨1367164835744736018055189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822886447659648024073585 1367164835744736018055189)
                      ·
                        rfl

theorem cell23_2662544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 3, 2].length) (baseStart_2662544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662544 prefixEnd_2662544 := by exact prefixLift 2662544
  have htrace : WordTrace (prefixWord ++ tailWord_2662544) baseStart_2662544 baseEnd_2662544 := by
    simpa [prefixWord, tailWord_2662544, baseEnd_2662544] using wordTrace_append hprefix tailTrace_2662544
  have hstable : (prefixWord ++ tailWord_2662544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662544).length < 2 ^ (prefixWord ++ tailWord_2662544).sum := by decide
  have hdescent : baseEnd_2662544 < baseStart_2662544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662558 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_2662558 : Nat := 118140960795 + 2662558 * 2 ^ 59
def prefixEnd_2662558 : Nat := 4983230072969 + 3 ^ 40 * 2662558 * 2
def baseEnd_2662558 : Nat := 151908002719322107031125

theorem tailTrace_2662558 : CollatzResearch.WordTrace tailWord_2662558 prefixEnd_2662558 151908002719322107031125 := by
  unfold tailWord_2662558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12138933536001821193588541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64740978858676379699138885 12138933536001821193588541)
  ·
    refine ⟨4552100076000682947595703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12138933536001821193588541 4552100076000682947595703)
    ·
      refine ⟨6828150114001024421393555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4552100076000682947595703 6828150114001024421393555)
      ·
        refine ⟨10242225171001536632090333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6828150114001024421393555 10242225171001536632090333)
        ·
          refine ⟨3840834439125576237033875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10242225171001536632090333 3840834439125576237033875)
          ·
            refine ⟨5761251658688364355550813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3840834439125576237033875 5761251658688364355550813)
            ·
              refine ⟨2160469372008136633331555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5761251658688364355550813 2160469372008136633331555)
              ·
                refine ⟨3240704058012204949997333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2160469372008136633331555 3240704058012204949997333)
                ·
                  refine ⟨151908002719322107031125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3240704058012204949997333 151908002719322107031125)
                  ·
                    rfl

theorem cell23_2662558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_2662558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662558 prefixEnd_2662558 := by exact prefixLift 2662558
  have htrace : WordTrace (prefixWord ++ tailWord_2662558) baseStart_2662558 baseEnd_2662558 := by
    simpa [prefixWord, tailWord_2662558, baseEnd_2662558] using wordTrace_append hprefix tailTrace_2662558
  have hstable : (prefixWord ++ tailWord_2662558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662558).length < 2 ^ (prefixWord ++ tailWord_2662558).sum := by decide
  have hdescent : baseEnd_2662558 < baseStart_2662558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662587 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 4]
def baseStart_2662587 : Nat := 118140960795 + 2662587 * 2 ^ 59
def prefixEnd_2662587 : Nat := 4983230072969 + 3 ^ 40 * 2662587 * 2
def baseEnd_2662587 : Nat := 1367186915412879349817491

theorem tailTrace_2662587 : CollatzResearch.WordTrace tailWord_2662587 prefixEnd_2662587 1367186915412879349817491 := by
  unfold tailWord_2662587
  simp only [CollatzResearch.WordTrace]
  refine ⟨97112526004909507501514015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64741684003273005001009343 97112526004909507501514015)
  ·
    refine ⟨145668789007364261252271023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97112526004909507501514015 145668789007364261252271023)
    ·
      refine ⟨218503183511046391878406535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145668789007364261252271023 218503183511046391878406535)
      ·
        refine ⟨327754775266569587817609803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218503183511046391878406535 327754775266569587817609803)
        ·
          refine ⟨491632162899854381726414705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327754775266569587817609803 491632162899854381726414705)
          ·
            refine ⟨368724122174890786294811029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491632162899854381726414705 368724122174890786294811029)
            ·
              refine ⟨17283943226948005607569267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 368724122174890786294811029 17283943226948005607569267)
              ·
                refine ⟨25925914840422008411353901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17283943226948005607569267 25925914840422008411353901)
                ·
                  refine ⟨9722218065158253154257713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25925914840422008411353901 9722218065158253154257713)
                  ·
                    refine ⟨7291663548868689865693285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9722218065158253154257713 7291663548868689865693285)
                    ·
                      refine ⟨1367186915412879349817491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7291663548868689865693285 1367186915412879349817491)
                      ·
                        rfl

theorem cell23_2662587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 4].length) (baseStart_2662587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662587 prefixEnd_2662587 := by exact prefixLift 2662587
  have htrace : WordTrace (prefixWord ++ tailWord_2662587) baseStart_2662587 baseEnd_2662587 := by
    simpa [prefixWord, tailWord_2662587, baseEnd_2662587] using wordTrace_append hprefix tailTrace_2662587
  have hstable : (prefixWord ++ tailWord_2662587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662587).length < 2 ^ (prefixWord ++ tailWord_2662587).sum := by decide
  have hdescent : baseEnd_2662587 < baseStart_2662587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662624 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 3]
def baseStart_2662624 : Nat := 118140960795 + 2662624 * 2 ^ 59
def prefixEnd_2662624 : Nat := 4983230072969 + 3 ^ 40 * 2662624 * 2
def baseEnd_2662624 : Nat := 1367205914197095705054821

theorem tailTrace_2662624 : CollatzResearch.WordTrace tailWord_2662624 prefixEnd_2662624 1367205914197095705054821 := by
  unfold tailWord_2662624
  simp only [CollatzResearch.WordTrace]
  refine ⟨48556937752887731410305463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64742583670516975213740617 48556937752887731410305463)
  ·
    refine ⟨72835406629331597115458195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48556937752887731410305463 72835406629331597115458195)
    ·
      refine ⟨109253109943997395673187293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72835406629331597115458195 109253109943997395673187293)
      ·
        refine ⟨40969916228999023377445235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109253109943997395673187293 40969916228999023377445235)
        ·
          refine ⟨61454874343498535066167853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40969916228999023377445235 61454874343498535066167853)
          ·
            refine ⟨23045577878811950649812945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61454874343498535066167853 23045577878811950649812945)
            ·
              refine ⟨17284183409108962987359709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23045577878811950649812945 17284183409108962987359709)
              ·
                refine ⟨6481568778415861120259891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17284183409108962987359709 6481568778415861120259891)
                ·
                  refine ⟨9722353167623791680389837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6481568778415861120259891 9722353167623791680389837)
                  ·
                    refine ⟨3645882437858921880146189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9722353167623791680389837 3645882437858921880146189)
                    ·
                      refine ⟨1367205914197095705054821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3645882437858921880146189 1367205914197095705054821)
                      ·
                        rfl

theorem cell23_2662624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_2662624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662624 prefixEnd_2662624 := by exact prefixLift 2662624
  have htrace : WordTrace (prefixWord ++ tailWord_2662624) baseStart_2662624 baseEnd_2662624 := by
    simpa [prefixWord, tailWord_2662624, baseEnd_2662624] using wordTrace_append hprefix tailTrace_2662624
  have hstable : (prefixWord ++ tailWord_2662624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662624).length < 2 ^ (prefixWord ++ tailWord_2662624).sum := by decide
  have hdescent : baseEnd_2662624 < baseStart_2662624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662647 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_2662647 : Nat := 118140960795 + 2662647 * 2 ^ 59
def prefixEnd_2662647 : Nat := 4983230072969 + 3 ^ 40 * 2662647 * 2
def baseEnd_2662647 : Nat := 1367217724252149115067215

theorem tailTrace_2662647 : CollatzResearch.WordTrace tailWord_2662647 prefixEnd_2662647 1367217724252149115067215 := by
  unfold tailWord_2662647
  simp only [CollatzResearch.WordTrace]
  refine ⟨97114714384692137748698195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64743142923128091832465463 97114714384692137748698195)
  ·
    refine ⟨145672071577038206623047293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97114714384692137748698195 145672071577038206623047293)
    ·
      refine ⟨54627026841389327483642735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145672071577038206623047293 54627026841389327483642735)
      ·
        refine ⟨81940540262083991225464103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54627026841389327483642735 81940540262083991225464103)
        ·
          refine ⟨122910810393125986838196155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81940540262083991225464103 122910810393125986838196155)
          ·
            refine ⟨184366215589688980257294233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122910810393125986838196155 184366215589688980257294233)
            ·
              refine ⟨138274661692266735192970675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184366215589688980257294233 138274661692266735192970675)
              ·
                refine ⟨207411992538400102789456013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138274661692266735192970675 207411992538400102789456013)
                ·
                  refine ⟨77779497201900038546046005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207411992538400102789456013 77779497201900038546046005)
                  ·
                    refine ⟨7291827862678128613691813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77779497201900038546046005 7291827862678128613691813)
                    ·
                      refine ⟨1367217724252149115067215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7291827862678128613691813 1367217724252149115067215)
                      ·
                        rfl

theorem cell23_2662647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_2662647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662647 prefixEnd_2662647 := by exact prefixLift 2662647
  have htrace : WordTrace (prefixWord ++ tailWord_2662647) baseStart_2662647 baseEnd_2662647 := by
    simpa [prefixWord, tailWord_2662647, baseEnd_2662647] using wordTrace_append hprefix tailTrace_2662647
  have hstable : (prefixWord ++ tailWord_2662647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662647).length < 2 ^ (prefixWord ++ tailWord_2662647).sum := by decide
  have hdescent : baseEnd_2662647 < baseStart_2662647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662664 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2662664 : Nat := 118140960795 + 2662664 * 2 ^ 59
def prefixEnd_2662664 : Nat := 4983230072969 + 3 ^ 40 * 2662664 * 2
def baseEnd_2662664 : Nat := 1367226453423275548554637

theorem tailTrace_2662664 : CollatzResearch.WordTrace tailWord_2662664 prefixEnd_2662664 1367226453423275548554637 := by
  unfold tailWord_2662664
  simp only [CollatzResearch.WordTrace]
  refine ⟨48557667212815274826033523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64743556283753699768044697 48557667212815274826033523)
  ·
    refine ⟨72836500819222912239050285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48557667212815274826033523 72836500819222912239050285)
    ·
      refine ⟨27313687807208592089643857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72836500819222912239050285 27313687807208592089643857)
      ·
        refine ⟨20485265855406444067232893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27313687807208592089643857 20485265855406444067232893)
        ·
          refine ⟨7681974695777416525212335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20485265855406444067232893 7681974695777416525212335)
          ·
            refine ⟨11522962043666124787818503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7681974695777416525212335 11522962043666124787818503)
            ·
              refine ⟨17284443065499187181727755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11522962043666124787818503 17284443065499187181727755)
              ·
                refine ⟨25926664598248780772591633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17284443065499187181727755 25926664598248780772591633)
                ·
                  refine ⟨19444998448686585579443725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25926664598248780772591633 19444998448686585579443725)
                  ·
                    refine ⟨7291874418257469592291397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19444998448686585579443725 7291874418257469592291397)
                    ·
                      refine ⟨1367226453423275548554637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7291874418257469592291397 1367226453423275548554637)
                      ·
                        rfl

theorem cell23_2662664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2662664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662664 prefixEnd_2662664 := by exact prefixLift 2662664
  have htrace : WordTrace (prefixWord ++ tailWord_2662664) baseStart_2662664 baseEnd_2662664 := by
    simpa [prefixWord, tailWord_2662664, baseEnd_2662664] using wordTrace_append hprefix tailTrace_2662664
  have hstable : (prefixWord ++ tailWord_2662664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662664).length < 2 ^ (prefixWord ++ tailWord_2662664).sum := by decide
  have hdescent : baseEnd_2662664 < baseStart_2662664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662684 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_2662684 : Nat := 118140960795 + 2662684 * 2 ^ 59
def prefixEnd_2662684 : Nat := 4983230072969 + 3 ^ 40 * 2662684 * 2
def baseEnd_2662684 : Nat := 1367236723036365470304545

theorem tailTrace_2662684 : CollatzResearch.WordTrace tailWord_2662684 prefixEnd_2662684 1367236723036365470304545 := by
  unfold tailWord_2662684
  simp only [CollatzResearch.WordTrace]
  refine ⟨48558031942779046533897553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64744042590372062045196737 48558031942779046533897553)
  ·
    refine ⟨36418523957084284900423165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48558031942779046533897553 36418523957084284900423165)
    ·
      refine ⟨13656946483906606837658687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36418523957084284900423165 13656946483906606837658687)
      ·
        refine ⟨20485419725859910256488031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13656946483906606837658687 20485419725859910256488031)
        ·
          refine ⟨30728129588789865384732047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20485419725859910256488031 30728129588789865384732047)
          ·
            refine ⟨46092194383184798077098071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30728129588789865384732047 46092194383184798077098071)
            ·
              refine ⟨69138291574777197115647107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46092194383184798077098071 69138291574777197115647107)
              ·
                refine ⟨103707437362165795673470661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69138291574777197115647107 103707437362165795673470661)
                ·
                  refine ⟨19445144505406086688775749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103707437362165795673470661 19445144505406086688775749)
                  ·
                    refine ⟨3645964594763641254145453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19445144505406086688775749 3645964594763641254145453)
                    ·
                      refine ⟨1367236723036365470304545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3645964594763641254145453 1367236723036365470304545)
                      ·
                        rfl

theorem cell23_2662684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_2662684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662684 prefixEnd_2662684 := by exact prefixLift 2662684
  have htrace : WordTrace (prefixWord ++ tailWord_2662684) baseStart_2662684 baseEnd_2662684 := by
    simpa [prefixWord, tailWord_2662684, baseEnd_2662684] using wordTrace_append hprefix tailTrace_2662684
  have hstable : (prefixWord ++ tailWord_2662684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662684).length < 2 ^ (prefixWord ++ tailWord_2662684).sum := by decide
  have hdescent : baseEnd_2662684 < baseStart_2662684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662702 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2662702 : Nat := 118140960795 + 2662702 * 2 ^ 59
def prefixEnd_2662702 : Nat := 4983230072969 + 3 ^ 40 * 2662702 * 2
def baseEnd_2662702 : Nat := 1367245965688146399879463

theorem tailTrace_2662702 : CollatzResearch.WordTrace tailWord_2662702 prefixEnd_2662702 1367245965688146399879463 := by
  unfold tailWord_2662702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12139590049936610267743795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64744480266328588094633573 12139590049936610267743795)
  ·
    refine ⟨18209385074904915401615693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12139590049936610267743795 18209385074904915401615693)
    ·
      refine ⟨6828519403089343275605885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18209385074904915401615693 6828519403089343275605885)
      ·
        refine ⟨2560694776158503728352207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6828519403089343275605885 2560694776158503728352207)
        ·
          refine ⟨3841042164237755592528311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560694776158503728352207 3841042164237755592528311)
          ·
            refine ⟨5761563246356633388792467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3841042164237755592528311 5761563246356633388792467)
            ·
              refine ⟨8642344869534950083188701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5761563246356633388792467 8642344869534950083188701)
              ·
                refine ⟨3240879326075606281195763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8642344869534950083188701 3240879326075606281195763)
                ·
                  refine ⟨4861318989113409421793645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240879326075606281195763 4861318989113409421793645)
                  ·
                    refine ⟨1822994620917528533172617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4861318989113409421793645 1822994620917528533172617)
                    ·
                      refine ⟨1367245965688146399879463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822994620917528533172617 1367245965688146399879463)
                      ·
                        rfl

theorem cell23_2662702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2662702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662702 prefixEnd_2662702 := by exact prefixLift 2662702
  have htrace : WordTrace (prefixWord ++ tailWord_2662702) baseStart_2662702 baseEnd_2662702 := by
    simpa [prefixWord, tailWord_2662702, baseEnd_2662702] using wordTrace_append hprefix tailTrace_2662702
  have hstable : (prefixWord ++ tailWord_2662702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662702).length < 2 ^ (prefixWord ++ tailWord_2662702).sum := by decide
  have hdescent : baseEnd_2662702 < baseStart_2662702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662734 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_2662734 : Nat := 118140960795 + 2662734 * 2 ^ 59
def prefixEnd_2662734 : Nat := 4983230072969 + 3 ^ 40 * 2662734 * 2
def baseEnd_2662734 : Nat := 455754132356363424893105

theorem tailTrace_2662734 : CollatzResearch.WordTrace tailWord_2662734 prefixEnd_2662734 455754132356363424893105 := by
  unfold tailWord_2662734
  simp only [CollatzResearch.WordTrace]
  refine ⟨12139735941922118950889407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64745258356917967738076837 12139735941922118950889407)
  ·
    refine ⟨18209603912883178426334111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12139735941922118950889407 18209603912883178426334111)
    ·
      refine ⟨27314405869324767639501167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18209603912883178426334111 27314405869324767639501167)
      ·
        refine ⟨40971608803987151459251751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27314405869324767639501167 40971608803987151459251751)
        ·
          refine ⟨61457413205980727188877627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40971608803987151459251751 61457413205980727188877627)
          ·
            refine ⟨92186119808971090783316441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61457413205980727188877627 92186119808971090783316441)
            ·
              refine ⟨69139589856728318087487331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92186119808971090783316441 69139589856728318087487331)
              ·
                refine ⟨103709384785092477131230997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69139589856728318087487331 103709384785092477131230997)
                ·
                  refine ⟨4861377411801209865526453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103709384785092477131230997 4861377411801209865526453)
                  ·
                    refine ⟨455754132356363424893105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4861377411801209865526453 455754132356363424893105)
                    ·
                      rfl

theorem cell23_2662734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_2662734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662734 prefixEnd_2662734 := by exact prefixLift 2662734
  have htrace : WordTrace (prefixWord ++ tailWord_2662734) baseStart_2662734 baseEnd_2662734 := by
    simpa [prefixWord, tailWord_2662734, baseEnd_2662734] using wordTrace_append hprefix tailTrace_2662734
  have hstable : (prefixWord ++ tailWord_2662734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662734).length < 2 ^ (prefixWord ++ tailWord_2662734).sum := by decide
  have hdescent : baseEnd_2662734 < baseStart_2662734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662791 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_2662791 : Nat := 118140960795 + 2662791 * 2 ^ 59
def prefixEnd_2662791 : Nat := 4983230072969 + 3 ^ 40 * 2662791 * 2
def baseEnd_2662791 : Nat := 1367291665466396551666553

theorem tailTrace_2662791 : CollatzResearch.WordTrace tailWord_2662791 prefixEnd_2662791 1367291665466396551666553 := by
  unfold tailWord_2662791
  simp only [CollatzResearch.WordTrace]
  refine ⟨97119966496170450341940227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64746644330780300227960151 97119966496170450341940227)
  ·
    refine ⟨145679949744255675512910341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97119966496170450341940227 145679949744255675512910341)
    ·
      refine ⟨27314990577047939158670689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145679949744255675512910341 27314990577047939158670689)
      ·
        refine ⟨20486242932785954369003017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27314990577047939158670689 20486242932785954369003017)
        ·
          refine ⟨15364682199589465776752263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20486242932785954369003017 15364682199589465776752263)
          ·
            refine ⟨23047023299384198665128395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15364682199589465776752263 23047023299384198665128395)
            ·
              refine ⟨34570534949076297997692593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23047023299384198665128395 34570534949076297997692593)
              ·
                refine ⟨25927901211807223498269445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34570534949076297997692593 25927901211807223498269445)
                ·
                  refine ⟨4861481477213854405925521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25927901211807223498269445 4861481477213854405925521)
                  ·
                    refine ⟨3646111107910390804444141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4861481477213854405925521 3646111107910390804444141)
                    ·
                      refine ⟨1367291665466396551666553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3646111107910390804444141 1367291665466396551666553)
                      ·
                        rfl

theorem cell23_2662791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_2662791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662791 prefixEnd_2662791 := by exact prefixLift 2662791
  have htrace : WordTrace (prefixWord ++ tailWord_2662791) baseStart_2662791 baseEnd_2662791 := by
    simpa [prefixWord, tailWord_2662791, baseEnd_2662791] using wordTrace_append hprefix tailTrace_2662791
  have hstable : (prefixWord ++ tailWord_2662791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662791).length < 2 ^ (prefixWord ++ tailWord_2662791).sum := by decide
  have hdescent : baseEnd_2662791 < baseStart_2662791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662808 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2662808 : Nat := 118140960795 + 2662808 * 2 ^ 59
def prefixEnd_2662808 : Nat := 4983230072969 + 3 ^ 40 * 2662808 * 2
def baseEnd_2662808 : Nat := 1367300394637522985153975

theorem tailTrace_2662808 : CollatzResearch.WordTrace tailWord_2662808 prefixEnd_2662808 1367300394637522985153975 := by
  unfold tailWord_2662808
  simp only [CollatzResearch.WordTrace]
  refine ⟨48560293268554431122654539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64747057691405908163539385 48560293268554431122654539)
  ·
    refine ⟨72840439902831646683981809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48560293268554431122654539 72840439902831646683981809)
    ·
      refine ⟨54630329927123735012986357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72840439902831646683981809 54630329927123735012986357)
      ·
        refine ⟨5121593430667850157467471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54630329927123735012986357 5121593430667850157467471)
        ·
          refine ⟨7682390146001775236201207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5121593430667850157467471 7682390146001775236201207)
          ·
            refine ⟨11523585219002662854301811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7682390146001775236201207 11523585219002662854301811)
            ·
              refine ⟨17285377828503994281452717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11523585219002662854301811 17285377828503994281452717)
              ·
                refine ⟨6482016685688997855544769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17285377828503994281452717 6482016685688997855544769)
                ·
                  refine ⟨4861512514266748391658577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6482016685688997855544769 4861512514266748391658577)
                  ·
                    refine ⟨3646134385700061293743933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4861512514266748391658577 3646134385700061293743933)
                    ·
                      refine ⟨1367300394637522985153975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3646134385700061293743933 1367300394637522985153975)
                      ·
                        rfl

theorem cell23_2662808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2662808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662808 prefixEnd_2662808 := by exact prefixLift 2662808
  have htrace : WordTrace (prefixWord ++ tailWord_2662808) baseStart_2662808 baseEnd_2662808 := by
    simpa [prefixWord, tailWord_2662808, baseEnd_2662808] using wordTrace_append hprefix tailTrace_2662808
  have hstable : (prefixWord ++ tailWord_2662808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662808).length < 2 ^ (prefixWord ++ tailWord_2662808).sum := by decide
  have hdescent : baseEnd_2662808 < baseStart_2662808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662831 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 5, 5, 2]
def baseStart_2662831 : Nat := 118140960795 + 2662831 * 2 ^ 59
def prefixEnd_2662831 : Nat := 4983230072969 + 3 ^ 40 * 2662831 * 2
def baseEnd_2662831 : Nat := 1367312204692576395166369

theorem tailTrace_2662831 : CollatzResearch.WordTrace tailWord_2662831 prefixEnd_2662831 1367312204692576395166369 := by
  unfold tailWord_2662831
  simp only [CollatzResearch.WordTrace]
  refine ⟨97121425416025537173396347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64747616944017024782264231 97121425416025537173396347)
  ·
    refine ⟨145682138124038305760094521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97121425416025537173396347 145682138124038305760094521)
    ·
      refine ⟨109261603593028729320070891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145682138124038305760094521 109261603593028729320070891)
      ·
        refine ⟨163892405389543093980106337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109261603593028729320070891 163892405389543093980106337)
        ·
          refine ⟨122919304042157320485079753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163892405389543093980106337 122919304042157320485079753)
          ·
            refine ⟨92189478031617990363809815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122919304042157320485079753 92189478031617990363809815)
            ·
              refine ⟨138284217047426985545714723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92189478031617990363809815 138284217047426985545714723)
              ·
                refine ⟨207426325571140478318572085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138284217047426985545714723 207426325571140478318572085)
                ·
                  refine ⟨19446218022294419842366133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207426325571140478318572085 19446218022294419842366133)
                  ·
                    refine ⟨1823082939590101860221825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19446218022294419842366133 1823082939590101860221825)
                    ·
                      refine ⟨1367312204692576395166369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823082939590101860221825 1367312204692576395166369)
                      ·
                        rfl

theorem cell23_2662831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 5, 2].length) (baseStart_2662831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662831 prefixEnd_2662831 := by exact prefixLift 2662831
  have htrace : WordTrace (prefixWord ++ tailWord_2662831) baseStart_2662831 baseEnd_2662831 := by
    simpa [prefixWord, tailWord_2662831, baseEnd_2662831] using wordTrace_append hprefix tailTrace_2662831
  have hstable : (prefixWord ++ tailWord_2662831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662831).length < 2 ^ (prefixWord ++ tailWord_2662831).sum := by decide
  have hdescent : baseEnd_2662831 < baseStart_2662831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662841 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 3, 5]
def baseStart_2662841 : Nat := 118140960795 + 2662841 * 2 ^ 59
def prefixEnd_2662841 : Nat := 4983230072969 + 3 ^ 40 * 2662841 * 2
def baseEnd_2662841 : Nat := 455772446499707118680441

theorem tailTrace_2662841 : CollatzResearch.WordTrace tailWord_2662841 prefixEnd_2662841 455772446499707118680441 := by
  unfold tailWord_2662841
  simp only [CollatzResearch.WordTrace]
  refine ⟨97121790145989308881260377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64747860097326205920840251 97121790145989308881260377)
  ·
    refine ⟨72841342609491981660945283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97121790145989308881260377 72841342609491981660945283)
    ·
      refine ⟨109262013914237972491417925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72841342609491981660945283 109262013914237972491417925)
      ·
        refine ⟨20486627608919619842140861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109262013914237972491417925 20486627608919619842140861)
        ·
          refine ⟨7682485353344857440802823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20486627608919619842140861 7682485353344857440802823)
          ·
            refine ⟨11523728030017286161204235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7682485353344857440802823 11523728030017286161204235)
            ·
              refine ⟨17285592045025929241806353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11523728030017286161204235 17285592045025929241806353)
              ·
                refine ⟨12964194033769446931354765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17285592045025929241806353 12964194033769446931354765)
                ·
                  refine ⟨4861572762663542599258037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12964194033769446931354765 4861572762663542599258037)
                  ·
                    refine ⟨455772446499707118680441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4861572762663542599258037 455772446499707118680441)
                    ·
                      rfl

theorem cell23_2662841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_2662841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662841 prefixEnd_2662841 := by exact prefixLift 2662841
  have htrace : WordTrace (prefixWord ++ tailWord_2662841) baseStart_2662841 baseEnd_2662841 := by
    simpa [prefixWord, tailWord_2662841, baseEnd_2662841] using wordTrace_append hprefix tailTrace_2662841
  have hstable : (prefixWord ++ tailWord_2662841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662841).length < 2 ^ (prefixWord ++ tailWord_2662841).sum := by decide
  have hdescent : baseEnd_2662841 < baseStart_2662841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662864 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_2662864 : Nat := 118140960795 + 2662864 * 2 ^ 59
def prefixEnd_2662864 : Nat := 4983230072969 + 3 ^ 40 * 2662864 * 2
def baseEnd_2662864 : Nat := 1367329149554174766053717

theorem tailTrace_2662864 : CollatzResearch.WordTrace tailWord_2662864 prefixEnd_2662864 1367329149554174766053717 := by
  unfold tailWord_2662864
  simp only [CollatzResearch.WordTrace]
  refine ⟨48561314512452991904673823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64748419349937322539565097 48561314512452991904673823)
  ·
    refine ⟨72841971768679487857010735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48561314512452991904673823 72841971768679487857010735)
    ·
      refine ⟨109262957653019231785516103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72841971768679487857010735 109262957653019231785516103)
      ·
        refine ⟨163894436479528847678274155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109262957653019231785516103 163894436479528847678274155)
        ·
          refine ⟨245841654719293271517411233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163894436479528847678274155 245841654719293271517411233)
          ·
            refine ⟨184381241039469953638058425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245841654719293271517411233 184381241039469953638058425)
            ·
              refine ⟨138285930779602465228543819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184381241039469953638058425 138285930779602465228543819)
              ·
                refine ⟨207428896169403697842815729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138285930779602465228543819 207428896169403697842815729)
                ·
                  refine ⟨155571672127052773382111797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207428896169403697842815729 155571672127052773382111797)
                  ·
                    refine ⟨14584844261911197504572981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 155571672127052773382111797 14584844261911197504572981)
                    ·
                      refine ⟨1367329149554174766053717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14584844261911197504572981 1367329149554174766053717)
                      ·
                        rfl

theorem cell23_2662864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_2662864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662864 prefixEnd_2662864 := by exact prefixLift 2662864
  have htrace : WordTrace (prefixWord ++ tailWord_2662864) baseStart_2662864 baseEnd_2662864 := by
    simpa [prefixWord, tailWord_2662864, baseEnd_2662864] using wordTrace_append hprefix tailTrace_2662864
  have hstable : (prefixWord ++ tailWord_2662864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662864).length < 2 ^ (prefixWord ++ tailWord_2662864).sum := by decide
  have hdescent : baseEnd_2662864 < baseStart_2662864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662881 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_2662881 : Nat := 118140960795 + 2662881 * 2 ^ 59
def prefixEnd_2662881 : Nat := 4983230072969 + 3 ^ 40 * 2662881 * 2
def baseEnd_2662881 : Nat := 1367337878725301199541139

theorem tailTrace_2662881 : CollatzResearch.WordTrace tailWord_2662881 prefixEnd_2662881 1367337878725301199541139 := by
  unfold tailWord_2662881
  simp only [CollatzResearch.WordTrace]
  refine ⟨97123249065844395712716497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64748832710562930475144331 97123249065844395712716497)
  ·
    refine ⟨72842436799383296784537373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97123249065844395712716497 72842436799383296784537373)
    ·
      refine ⟨27315913799768736294201515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72842436799383296784537373 27315913799768736294201515)
      ·
        refine ⟨40973870699653104441302273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27315913799768736294201515 40973870699653104441302273)
        ·
          refine ⟨30730403024739828330976705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40973870699653104441302273 30730403024739828330976705)
          ·
            refine ⟨23047802268554871248232529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30730403024739828330976705 23047802268554871248232529)
            ·
              refine ⟨17285851701416153436174397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23047802268554871248232529 17285851701416153436174397)
              ·
                refine ⟨6482194388031057538565399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17285851701416153436174397 6482194388031057538565399)
                ·
                  refine ⟨9723291582046586307848099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6482194388031057538565399 9723291582046586307848099)
                  ·
                    refine ⟨14584937373069879461772149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9723291582046586307848099 14584937373069879461772149)
                    ·
                      refine ⟨1367337878725301199541139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14584937373069879461772149 1367337878725301199541139)
                      ·
                        rfl

theorem cell23_2662881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_2662881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662881 prefixEnd_2662881 := by exact prefixLift 2662881
  have htrace : WordTrace (prefixWord ++ tailWord_2662881) baseStart_2662881 baseEnd_2662881 := by
    simpa [prefixWord, tailWord_2662881, baseEnd_2662881] using wordTrace_append hprefix tailTrace_2662881
  have hstable : (prefixWord ++ tailWord_2662881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662881).length < 2 ^ (prefixWord ++ tailWord_2662881).sum := by decide
  have hdescent : baseEnd_2662881 < baseStart_2662881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662888 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 4, 4]
def baseStart_2662888 : Nat := 118140960795 + 2662888 * 2 ^ 59
def prefixEnd_2662888 : Nat := 4983230072969 + 3 ^ 40 * 2662888 * 2
def baseEnd_2662888 : Nat := 455780491029960890717869

theorem tailTrace_2662888 : CollatzResearch.WordTrace tailWord_2662888 prefixEnd_2662888 455780491029960890717869 := by
  unfold tailWord_2662888
  simp only [CollatzResearch.WordTrace]
  refine ⟨48561752188409517954110659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64749002917879357272147545 48561752188409517954110659)
  ·
    refine ⟨72842628282614276931165989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48561752188409517954110659 72842628282614276931165989)
    ·
      refine ⟨13657992802990176924593623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72842628282614276931165989 13657992802990176924593623)
      ·
        refine ⟨20486989204485265386890435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13657992802990176924593623 20486989204485265386890435)
        ·
          refine ⟨30730483806727898080335653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20486989204485265386890435 30730483806727898080335653)
          ·
            refine ⟨5761965713761480890062935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30730483806727898080335653 5761965713761480890062935)
            ·
              refine ⟨8642948570642221335094403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5761965713761480890062935 8642948570642221335094403)
              ·
                refine ⟨12964422855963332002641605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8642948570642221335094403 12964422855963332002641605)
                ·
                  refine ⟨2430829285493124750495301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12964422855963332002641605 2430829285493124750495301)
                  ·
                    refine ⟨455780491029960890717869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2430829285493124750495301 455780491029960890717869)
                    ·
                      rfl

theorem cell23_2662888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_2662888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662888 prefixEnd_2662888 := by exact prefixLift 2662888
  have htrace : WordTrace (prefixWord ++ tailWord_2662888) baseStart_2662888 baseEnd_2662888 := by
    simpa [prefixWord, tailWord_2662888, baseEnd_2662888] using wordTrace_append hprefix tailTrace_2662888
  have hstable : (prefixWord ++ tailWord_2662888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662888).length < 2 ^ (prefixWord ++ tailWord_2662888).sum := by decide
  have hdescent : baseEnd_2662888 < baseStart_2662888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662932 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2662932 : Nat := 118140960795 + 2662932 * 2 ^ 59
def prefixEnd_2662932 : Nat := 4983230072969 + 3 ^ 40 * 2662932 * 2
def baseEnd_2662932 : Nat := 1367364066238680500003405

theorem tailTrace_2662932 : CollatzResearch.WordTrace tailWord_2662932 prefixEnd_2662932 1367364066238680500003405 := by
  unfold tailWord_2662932
  simp only [CollatzResearch.WordTrace]
  refine ⟨48562554594329815711411525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64750072792439754281882033 48562554594329815711411525)
  ·
    refine ⟨9105478986436840445889661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48562554594329815711411525 9105478986436840445889661)
    ·
      refine ⟨3414554619913815167208623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9105478986436840445889661 3414554619913815167208623)
      ·
        refine ⟨5121831929870722750812935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3414554619913815167208623 5121831929870722750812935)
        ·
          refine ⟨7682747894806084126219403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5121831929870722750812935 7682747894806084126219403)
          ·
            refine ⟨11524121842209126189329105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7682747894806084126219403 11524121842209126189329105)
            ·
              refine ⟨8643091381656844641996829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11524121842209126189329105 8643091381656844641996829)
              ·
                refine ⟨3241159268121316740748811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8643091381656844641996829 3241159268121316740748811)
                ·
                  refine ⟨4861738902181975111123217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241159268121316740748811 4861738902181975111123217)
                  ·
                    refine ⟨3646304176636481333342413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4861738902181975111123217 3646304176636481333342413)
                    ·
                      refine ⟨1367364066238680500003405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3646304176636481333342413 1367364066238680500003405)
                      ·
                        rfl

theorem cell23_2662932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2662932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662932 prefixEnd_2662932 := by exact prefixLift 2662932
  have htrace : WordTrace (prefixWord ++ tailWord_2662932) baseStart_2662932 baseEnd_2662932 := by
    simpa [prefixWord, tailWord_2662932, baseEnd_2662932] using wordTrace_append hprefix tailTrace_2662932
  have hstable : (prefixWord ++ tailWord_2662932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662932).length < 2 ^ (prefixWord ++ tailWord_2662932).sum := by decide
  have hdescent : baseEnd_2662932 < baseStart_2662932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662935 : List Nat := [1, 1, 3, 6, 2, 1, 9]
def baseStart_2662935 : Nat := 118140960795 + 2662935 * 2 ^ 59
def prefixEnd_2662935 : Nat := 4983230072969 + 3 ^ 40 * 2662935 * 2
def baseEnd_2662935 : Nat := 16881056872600543065011

theorem tailTrace_2662935 : CollatzResearch.WordTrace tailWord_2662935 prefixEnd_2662935 16881056872600543065011 := by
  unfold tailWord_2662935
  simp only [CollatzResearch.WordTrace]
  refine ⟨97125218607648762935182259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64750145738432508623454839 97125218607648762935182259)
  ·
    refine ⟨145687827911473144402773389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97125218607648762935182259 145687827911473144402773389)
    ·
      refine ⟨54632935466802429151040021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145687827911473144402773389 54632935466802429151040021)
      ·
        refine ⟨2560918850006363866455001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54632935466802429151040021 2560918850006363866455001)
        ·
          refine ⟨1920689137504772899841251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2560918850006363866455001 1920689137504772899841251)
          ·
            refine ⟨2881033706257159349761877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920689137504772899841251 2881033706257159349761877)
            ·
              refine ⟨16881056872600543065011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2881033706257159349761877 16881056872600543065011)
              ·
                rfl

theorem cell23_2662935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 9].length) (baseStart_2662935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662935 prefixEnd_2662935 := by exact prefixLift 2662935
  have htrace : WordTrace (prefixWord ++ tailWord_2662935) baseStart_2662935 baseEnd_2662935 := by
    simpa [prefixWord, tailWord_2662935, baseEnd_2662935] using wordTrace_append hprefix tailTrace_2662935
  have hstable : (prefixWord ++ tailWord_2662935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662935).length < 2 ^ (prefixWord ++ tailWord_2662935).sum := by decide
  have hdescent : baseEnd_2662935 < baseStart_2662935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662945 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_2662945 : Nat := 118140960795 + 2662945 * 2 ^ 59
def prefixEnd_2662945 : Nat := 4983230072969 + 3 ^ 40 * 2662945 * 2
def baseEnd_2662945 : Nat := 1367370741487188949140845

theorem tailTrace_2662945 : CollatzResearch.WordTrace tailWord_2662945 prefixEnd_2662945 1367370741487188949140845 := by
  unfold tailWord_2662945
  simp only [CollatzResearch.WordTrace]
  refine ⟨97125583337612534643046289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64750388891741689762030859 97125583337612534643046289)
  ·
    refine ⟨72844187503209400982284717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97125583337612534643046289 72844187503209400982284717)
    ·
      refine ⟨27316570313703525368356769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72844187503209400982284717 27316570313703525368356769)
      ·
        refine ⟨20487427735277644026267577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27316570313703525368356769 20487427735277644026267577)
        ·
          refine ⟨15365570801458233019700683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20487427735277644026267577 15365570801458233019700683)
          ·
            refine ⟨23048356202187349529551025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15365570801458233019700683 23048356202187349529551025)
            ·
              refine ⟨17286267151640512147163269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23048356202187349529551025 17286267151640512147163269)
              ·
                refine ⟨3241175090932596027593113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17286267151640512147163269 3241175090932596027593113)
                ·
                  refine ⟨2430881318199447020694835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3241175090932596027593113 2430881318199447020694835)
                  ·
                    refine ⟨3646321977299170531042253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2430881318199447020694835 3646321977299170531042253)
                    ·
                      refine ⟨1367370741487188949140845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3646321977299170531042253 1367370741487188949140845)
                      ·
                        rfl

theorem cell23_2662945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_2662945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662945 prefixEnd_2662945 := by exact prefixLift 2662945
  have htrace : WordTrace (prefixWord ++ tailWord_2662945) baseStart_2662945 baseEnd_2662945 := by
    simpa [prefixWord, tailWord_2662945, baseEnd_2662945] using wordTrace_append hprefix tailTrace_2662945
  have hstable : (prefixWord ++ tailWord_2662945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662945).length < 2 ^ (prefixWord ++ tailWord_2662945).sum := by decide
  have hdescent : baseEnd_2662945 < baseStart_2662945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662961 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 2, 6]
def baseStart_2662961 : Nat := 118140960795 + 2662961 * 2 ^ 59
def prefixEnd_2662961 : Nat := 4983230072969 + 3 ^ 40 * 2662961 * 2
def baseEnd_2662961 : Nat := 455792985725886962180257

theorem tailTrace_2662961 : CollatzResearch.WordTrace tailWord_2662961 prefixEnd_2662961 455792985725886962180257 := by
  unfold tailWord_2662961
  simp only [CollatzResearch.WordTrace]
  refine ⟨97126166905554569375628737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64750777937036379583752491 97126166905554569375628737)
  ·
    refine ⟨72844625179165927031721553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97126166905554569375628737 72844625179165927031721553)
    ·
      refine ⟨54633468884374445273791165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72844625179165927031721553 54633468884374445273791165)
      ·
        refine ⟨20487550831640416977671687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54633468884374445273791165 20487550831640416977671687)
        ·
          refine ⟨30731326247460625466507531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20487550831640416977671687 30731326247460625466507531)
          ·
            refine ⟨46096989371190938199761297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30731326247460625466507531 46096989371190938199761297)
            ·
              refine ⟨34572742028393203649820973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46096989371190938199761297 34572742028393203649820973)
              ·
                refine ⟨12964778260647451368682865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34572742028393203649820973 12964778260647451368682865)
                ·
                  refine ⟨9723583695485588526512149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12964778260647451368682865 9723583695485588526512149)
                  ·
                    refine ⟨455792985725886962180257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9723583695485588526512149 455792985725886962180257)
                    ·
                      rfl

theorem cell23_2662961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_2662961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662961 prefixEnd_2662961 := by exact prefixLift 2662961
  have htrace : WordTrace (prefixWord ++ tailWord_2662961) baseStart_2662961 baseEnd_2662961 := by
    simpa [prefixWord, tailWord_2662961, baseEnd_2662961] using wordTrace_append hprefix tailTrace_2662961
  have hstable : (prefixWord ++ tailWord_2662961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662961).length < 2 ^ (prefixWord ++ tailWord_2662961).sum := by decide
  have hdescent : baseEnd_2662961 < baseStart_2662961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662962 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3]
def baseStart_2662962 : Nat := 118140960795 + 2662962 * 2 ^ 59
def prefixEnd_2662962 : Nat := 4983230072969 + 3 ^ 40 * 2662962 * 2
def baseEnd_2662962 : Nat := 1367379470658315382628267

theorem tailTrace_2662962 : CollatzResearch.WordTrace tailWord_2662962 prefixEnd_2662962 1367379470658315382628267 := by
  unfold tailWord_2662962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24281550844637736636603785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64750802252367297697610093 24281550844637736636603785)
  ·
    refine ⟨18211163133478302477452839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24281550844637736636603785 18211163133478302477452839)
    ·
      refine ⟨27316744700217453716179259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18211163133478302477452839 27316744700217453716179259)
      ·
        refine ⟨40975117050326180574268889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27316744700217453716179259 40975117050326180574268889)
        ·
          refine ⟨30731337787744635430701667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40975117050326180574268889 30731337787744635430701667)
          ·
            refine ⟨46097006681616953146052501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30731337787744635430701667 46097006681616953146052501)
            ·
              refine ⟨2160797188200794678721211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46097006681616953146052501 2160797188200794678721211)
              ·
                refine ⟨3241195782301192018081817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2160797188200794678721211 3241195782301192018081817)
                ·
                  refine ⟨2430896836725894013561363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3241195782301192018081817 2430896836725894013561363)
                  ·
                    refine ⟨3646345255088841020342045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2430896836725894013561363 3646345255088841020342045)
                    ·
                      refine ⟨1367379470658315382628267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3646345255088841020342045 1367379470658315382628267)
                      ·
                        rfl

theorem cell23_2662962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_2662962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662962 prefixEnd_2662962 := by exact prefixLift 2662962
  have htrace : WordTrace (prefixWord ++ tailWord_2662962) baseStart_2662962 baseEnd_2662962 := by
    simpa [prefixWord, tailWord_2662962, baseEnd_2662962] using wordTrace_append hprefix tailTrace_2662962
  have hstable : (prefixWord ++ tailWord_2662962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662962).length < 2 ^ (prefixWord ++ tailWord_2662962).sum := by decide
  have hdescent : baseEnd_2662962 < baseStart_2662962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662972 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 1, 3, 2]
def baseStart_2662972 : Nat := 118140960795 + 2662972 * 2 ^ 59
def prefixEnd_2662972 : Nat := 4983230072969 + 3 ^ 40 * 2662972 * 2
def baseEnd_2662972 : Nat := 1367384605464860343503221

theorem tailTrace_2662972 : CollatzResearch.WordTrace tailWord_2662972 prefixEnd_2662972 1367384605464860343503221 := by
  unfold tailWord_2662972
  simp only [CollatzResearch.WordTrace]
  refine ⟨48563284054257359127139585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64751045405676478836186113 48563284054257359127139585)
  ·
    refine ⟨36422463040693019345354689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48563284054257359127139585 36422463040693019345354689)
    ·
      refine ⟨27316847280519764509016017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36422463040693019345354689 27316847280519764509016017)
      ·
        refine ⟨20487635460389823381762013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27316847280519764509016017 20487635460389823381762013)
        ·
          refine ⟨7682863297646183768160755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20487635460389823381762013 7682863297646183768160755)
          ·
            refine ⟨11524294946469275652241133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7682863297646183768160755 11524294946469275652241133)
            ·
              refine ⟨4321610604925978369590425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11524294946469275652241133 4321610604925978369590425)
              ·
                refine ⟨3241207953694483777192819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4321610604925978369590425 3241207953694483777192819)
                ·
                  refine ⟨4861811930541725665789229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241207953694483777192819 4861811930541725665789229)
                  ·
                    refine ⟨1823179473953147124670961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4861811930541725665789229 1823179473953147124670961)
                    ·
                      refine ⟨1367384605464860343503221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823179473953147124670961 1367384605464860343503221)
                      ·
                        rfl

theorem cell23_2662972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_2662972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2662972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2662972 prefixEnd_2662972 := by exact prefixLift 2662972
  have htrace : WordTrace (prefixWord ++ tailWord_2662972) baseStart_2662972 baseEnd_2662972 := by
    simpa [prefixWord, tailWord_2662972, baseEnd_2662972] using wordTrace_append hprefix tailTrace_2662972
  have hstable : (prefixWord ++ tailWord_2662972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662972).length < 2 ^ (prefixWord ++ tailWord_2662972).sum := by decide
  have hdescent : baseEnd_2662972 < baseStart_2662972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663031 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_2663031 : Nat := 118140960795 + 2663031 * 2 ^ 59
def prefixEnd_2663031 : Nat := 4983230072969 + 3 ^ 40 * 2663031 * 2
def baseEnd_2663031 : Nat := 1367414900823475612665449

theorem tailTrace_2663031 : CollatzResearch.WordTrace tailWord_2663031 prefixEnd_2663031 1367414900823475612665449 := by
  unfold tailWord_2663031
  simp only [CollatzResearch.WordTrace]
  refine ⟨97128720015300971330676947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64752480010200647553784631 97128720015300971330676947)
  ·
    refine ⟨145693080022951456996015421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97128720015300971330676947 145693080022951456996015421)
    ·
      refine ⟨54634905008606796373505783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145693080022951456996015421 54634905008606796373505783)
      ·
        refine ⟨81952357512910194560258675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54634905008606796373505783 81952357512910194560258675)
        ·
          refine ⟨122928536269365291840388013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81952357512910194560258675 122928536269365291840388013)
          ·
            refine ⟨46098201101011984440145505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122928536269365291840388013 46098201101011984440145505)
            ·
              refine ⟨34573650825758988330109129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46098201101011984440145505 34573650825758988330109129)
              ·
                refine ⟨25930238119319241247581847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34573650825758988330109129 25930238119319241247581847)
                ·
                  refine ⟨38895357178978861871372771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25930238119319241247581847 38895357178978861871372771)
                  ·
                    refine ⟨58343035768468292807059157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38895357178978861871372771 58343035768468292807059157)
                    ·
                      refine ⟨1367414900823475612665449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58343035768468292807059157 1367414900823475612665449)
                      ·
                        rfl

theorem cell23_2663031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_2663031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663031 prefixEnd_2663031 := by exact prefixLift 2663031
  have htrace : WordTrace (prefixWord ++ tailWord_2663031) baseStart_2663031 baseEnd_2663031 := by
    simpa [prefixWord, tailWord_2663031, baseEnd_2663031] using wordTrace_append hprefix tailTrace_2663031
  have hstable : (prefixWord ++ tailWord_2663031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663031).length < 2 ^ (prefixWord ++ tailWord_2663031).sum := by decide
  have hdescent : baseEnd_2663031 < baseStart_2663031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663081 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 10]
def baseStart_2663081 : Nat := 118140960795 + 2663081 * 2 ^ 59
def prefixEnd_2663081 : Nat := 4983230072969 + 3 ^ 40 * 2663081 * 2
def baseEnd_2663081 : Nat := 151937841650688935226691

theorem tailTrace_2663081 : CollatzResearch.WordTrace tailWord_2663081 prefixEnd_2663081 151937841650688935226691 := by
  unfold tailWord_2663081
  simp only [CollatzResearch.WordTrace]
  refine ⟨97130543665119829869997097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64753695776746553246664731 97130543665119829869997097)
  ·
    refine ⟨72847907748839872402497823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97130543665119829869997097 72847907748839872402497823)
    ·
      refine ⟨109271861623259808603746735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72847907748839872402497823 109271861623259808603746735)
      ·
        refine ⟨163907792434889712905620103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109271861623259808603746735 163907792434889712905620103)
        ·
          refine ⟨245861688652334569358430155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163907792434889712905620103 245861688652334569358430155)
          ·
            refine ⟨368792532978501854037645233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245861688652334569358430155 368792532978501854037645233)
            ·
              refine ⟨276594399733876390528233925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368792532978501854037645233 276594399733876390528233925)
              ·
                refine ⟨51861449950101823224043861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276594399733876390528233925 51861449950101823224043861)
                ·
                  refine ⟨151937841650688935226691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 51861449950101823224043861 151937841650688935226691)
                  ·
                    rfl

theorem cell23_2663081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 10].length) (baseStart_2663081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663081 prefixEnd_2663081 := by exact prefixLift 2663081
  have htrace : WordTrace (prefixWord ++ tailWord_2663081) baseStart_2663081 baseEnd_2663081 := by
    simpa [prefixWord, tailWord_2663081, baseEnd_2663081] using wordTrace_append hprefix tailTrace_2663081
  have hstable : (prefixWord ++ tailWord_2663081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663081).length < 2 ^ (prefixWord ++ tailWord_2663081).sum := by decide
  have hdescent : baseEnd_2663081 < baseStart_2663081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663132 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 6]
def baseStart_2663132 : Nat := 118140960795 + 2663132 * 2 ^ 59
def prefixEnd_2663132 : Nat := 4983230072969 + 3 ^ 40 * 2663132 * 2
def baseEnd_2663132 : Nat := 151940751374397746389165

theorem tailTrace_2663132 : CollatzResearch.WordTrace tailWord_2663132 prefixEnd_2663132 151940751374397746389165 := by
  unfold tailWord_2663132
  simp only [CollatzResearch.WordTrace]
  refine ⟨48566201893967532790051825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64754935858623377053402433 48566201893967532790051825)
  ·
    refine ⟨36424651420475649592538869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48566201893967532790051825 36424651420475649592538869)
    ·
      refine ⟨3414811070669592149300519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36424651420475649592538869 3414811070669592149300519)
      ·
        refine ⟨5122216606004388223950779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3414811070669592149300519 5122216606004388223950779)
        ·
          refine ⟨7683324909006582335926169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122216606004388223950779 7683324909006582335926169)
          ·
            refine ⟨5762493681754936751944627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7683324909006582335926169 5762493681754936751944627)
            ·
              refine ⟨8643740522632405127916941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5762493681754936751944627 8643740522632405127916941)
              ·
                refine ⟨3241402695987151922968853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8643740522632405127916941 3241402695987151922968853)
                ·
                  refine ⟨151940751374397746389165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3241402695987151922968853 151940751374397746389165)
                  ·
                    rfl

theorem cell23_2663132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_2663132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663132 prefixEnd_2663132 := by exact prefixLift 2663132
  have htrace : WordTrace (prefixWord ++ tailWord_2663132) baseStart_2663132 baseEnd_2663132 := by
    simpa [prefixWord, tailWord_2663132, baseEnd_2663132] using wordTrace_append hprefix tailTrace_2663132
  have hstable : (prefixWord ++ tailWord_2663132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663132).length < 2 ^ (prefixWord ++ tailWord_2663132).sum := by decide
  have hdescent : baseEnd_2663132 < baseStart_2663132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663145 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 1, 5]
def baseStart_2663145 : Nat := 118140960795 + 2663145 * 2 ^ 59
def prefixEnd_2663145 : Nat := 4983230072969 + 3 ^ 40 * 2663145 * 2
def baseEnd_2663145 : Nat := 455824479206029388879975

theorem tailTrace_2663145 : CollatzResearch.WordTrace tailWord_2663145 prefixEnd_2663145 455824479206029388879975 := by
  unfold tailWord_2663145
  simp only [CollatzResearch.WordTrace]
  refine ⟨97132877936887968800326889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64755251957925312533551259 97132877936887968800326889)
  ·
    refine ⟨72849658452665976600245167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97132877936887968800326889 72849658452665976600245167)
    ·
      refine ⟨109274487678998964900367751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72849658452665976600245167 109274487678998964900367751)
      ·
        refine ⟨163911731518498447350551627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109274487678998964900367751 163911731518498447350551627)
        ·
          refine ⟨245867597277747671025827441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163911731518498447350551627 245867597277747671025827441)
          ·
            refine ⟨184400697958310753269370581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245867597277747671025827441 184400697958310753269370581)
            ·
              refine ⟨4321891358397908279750873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 184400697958310753269370581 4321891358397908279750873)
              ·
                refine ⟨3241418518798431209813155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4321891358397908279750873 3241418518798431209813155)
                ·
                  refine ⟨4862127778197646814719733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241418518798431209813155 4862127778197646814719733)
                  ·
                    refine ⟨455824479206029388879975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4862127778197646814719733 455824479206029388879975)
                    ·
                      rfl

theorem cell23_2663145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 5].length) (baseStart_2663145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663145 prefixEnd_2663145 := by exact prefixLift 2663145
  have htrace : WordTrace (prefixWord ++ tailWord_2663145) baseStart_2663145 baseEnd_2663145 := by
    simpa [prefixWord, tailWord_2663145, baseEnd_2663145] using wordTrace_append hprefix tailTrace_2663145
  have hstable : (prefixWord ++ tailWord_2663145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663145).length < 2 ^ (prefixWord ++ tailWord_2663145).sum := by decide
  have hdescent : baseEnd_2663145 < baseStart_2663145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663152 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 2, 3, 2]
def baseStart_2663152 : Nat := 118140960795 + 2663152 * 2 ^ 59
def prefixEnd_2663152 : Nat := 4983230072969 + 3 ^ 40 * 2663152 * 2
def baseEnd_2663152 : Nat := 1367477031982669639252393

theorem tailTrace_2663152 : CollatzResearch.WordTrace tailWord_2663152 prefixEnd_2663152 1367477031982669639252393 := by
  unfold tailWord_2663152
  simp only [CollatzResearch.WordTrace]
  refine ⟨48566566623931304497915855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64755422165241739330554473 48566566623931304497915855)
  ·
    refine ⟨72849849935896956746873783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48566566623931304497915855 72849849935896956746873783)
    ·
      refine ⟨109274774903845435120310675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72849849935896956746873783 109274774903845435120310675)
      ·
        refine ⟨163912162355768152680466013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109274774903845435120310675 163912162355768152680466013)
        ·
          refine ⟨61467060883413057255174755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163912162355768152680466013 61467060883413057255174755)
          ·
            refine ⟨92200591325119585882762133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61467060883413057255174755 92200591325119585882762133)
            ·
              refine ⟨4321902718364980588254475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92200591325119585882762133 4321902718364980588254475)
              ·
                refine ⟨6482854077547470882381713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4321902718364980588254475 6482854077547470882381713)
                ·
                  refine ⟨4862140558160603161786285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6482854077547470882381713 4862140558160603161786285)
                  ·
                    refine ⟨1823302709310226185669857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4862140558160603161786285 1823302709310226185669857)
                    ·
                      refine ⟨1367477031982669639252393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823302709310226185669857 1367477031982669639252393)
                      ·
                        rfl

theorem cell23_2663152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 3, 2].length) (baseStart_2663152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663152 prefixEnd_2663152 := by exact prefixLift 2663152
  have htrace : WordTrace (prefixWord ++ tailWord_2663152) baseStart_2663152 baseEnd_2663152 := by
    simpa [prefixWord, tailWord_2663152, baseEnd_2663152] using wordTrace_append hprefix tailTrace_2663152
  have hstable : (prefixWord ++ tailWord_2663152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663152).length < 2 ^ (prefixWord ++ tailWord_2663152).sum := by decide
  have hdescent : baseEnd_2663152 < baseStart_2663152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663176 : List Nat := [2, 1, 3, 2, 2, 2, 4, 2, 1, 1, 3]
def baseStart_2663176 : Nat := 118140960795 + 2663176 * 2 ^ 59
def prefixEnd_2663176 : Nat := 4983230072969 + 3 ^ 40 * 2663176 * 2
def baseEnd_2663176 : Nat := 1367489355518377545352283

theorem tailTrace_2663176 : CollatzResearch.WordTrace tailWord_2663176 prefixEnd_2663176 1367489355518377545352283 := by
  unfold tailWord_2663176
  simp only [CollatzResearch.WordTrace]
  refine ⟨48567004299887830547352691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64756005733183774063136921 48567004299887830547352691)
  ·
    refine ⟨72850506449831745821029037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48567004299887830547352691 72850506449831745821029037)
    ·
      refine ⟨27318939918686904682885889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72850506449831745821029037 27318939918686904682885889)
      ·
        refine ⟨20489204939015178512164417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27318939918686904682885889 20489204939015178512164417)
        ·
          refine ⟨15366903704261383884123313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20489204939015178512164417 15366903704261383884123313)
          ·
            refine ⟨11525177778196037913092485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15366903704261383884123313 11525177778196037913092485)
            ·
              refine ⟨2160970833411757108704841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11525177778196037913092485 2160970833411757108704841)
              ·
                refine ⟨1620728125058817831528631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160970833411757108704841 1620728125058817831528631)
                ·
                  refine ⟨2431092187588226747292947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620728125058817831528631 2431092187588226747292947)
                  ·
                    refine ⟨3646638281382340120939421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2431092187588226747292947 3646638281382340120939421)
                    ·
                      refine ⟨1367489355518377545352283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3646638281382340120939421 1367489355518377545352283)
                      ·
                        rfl

theorem cell23_2663176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_2663176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663176 prefixEnd_2663176 := by exact prefixLift 2663176
  have htrace : WordTrace (prefixWord ++ tailWord_2663176) baseStart_2663176 baseEnd_2663176 := by
    simpa [prefixWord, tailWord_2663176, baseEnd_2663176] using wordTrace_append hprefix tailTrace_2663176
  have hstable : (prefixWord ++ tailWord_2663176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663176).length < 2 ^ (prefixWord ++ tailWord_2663176).sum := by decide
  have hdescent : baseEnd_2663176 < baseStart_2663176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663185 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 3]
def baseStart_2663185 : Nat := 118140960795 + 2663185 * 2 ^ 59
def prefixEnd_2663185 : Nat := 4983230072969 + 3 ^ 40 * 2663185 * 2
def baseEnd_2663185 : Nat := 1367493976844268010139741

theorem tailTrace_2663185 : CollatzResearch.WordTrace tailWord_2663185 prefixEnd_2663185 1367493976844268010139741 := by
  unfold tailWord_2663185
  simp only [CollatzResearch.WordTrace]
  refine ⟨97134336856743055631783009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64756224571162037087855339 97134336856743055631783009)
  ·
    refine ⟨72850752642557291723837257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97134336856743055631783009 72850752642557291723837257)
    ·
      refine ⟨54638064481917968792877943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72850752642557291723837257 54638064481917968792877943)
      ·
        refine ⟨81957096722876953189316915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54638064481917968792877943 81957096722876953189316915)
        ·
          refine ⟨122935645084315429783975373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81957096722876953189316915 122935645084315429783975373)
          ·
            refine ⟨46100866906618286168990765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122935645084315429783975373 46100866906618286168990765)
            ·
              refine ⟨17287825089981857313371537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46100866906618286168990765 17287825089981857313371537)
              ·
                refine ⟨12965868817486392985028653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17287825089981857313371537 12965868817486392985028653)
                ·
                  refine ⟨4862200806557397369385745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12965868817486392985028653 4862200806557397369385745)
                  ·
                    refine ⟨3646650604918048027039309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4862200806557397369385745 3646650604918048027039309)
                    ·
                      refine ⟨1367493976844268010139741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3646650604918048027039309 1367493976844268010139741)
                      ·
                        rfl

theorem cell23_2663185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_2663185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663185 prefixEnd_2663185 := by exact prefixLift 2663185
  have htrace : WordTrace (prefixWord ++ tailWord_2663185) baseStart_2663185 baseEnd_2663185 := by
    simpa [prefixWord, tailWord_2663185, baseEnd_2663185] using wordTrace_append hprefix tailTrace_2663185
  have hstable : (prefixWord ++ tailWord_2663185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663185).length < 2 ^ (prefixWord ++ tailWord_2663185).sum := by decide
  have hdescent : baseEnd_2663185 < baseStart_2663185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663199 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 3, 2, 2]
def baseStart_2663199 : Nat := 118140960795 + 2663199 * 2 ^ 59
def prefixEnd_2663199 : Nat := 4983230072969 + 3 ^ 40 * 2663199 * 2
def baseEnd_2663199 : Nat := 1367501165573430955364677

theorem tailTrace_2663199 : CollatzResearch.WordTrace tailWord_2663199 prefixEnd_2663199 1367501165573430955364677 := by
  unfold tailWord_2663199
  simp only [CollatzResearch.WordTrace]
  refine ⟨97134847478692336022792651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64756564985794890681861767 97134847478692336022792651)
  ·
    refine ⟨145702271218038504034188977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97134847478692336022792651 145702271218038504034188977)
    ·
      refine ⟨109276703413528878025641733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145702271218038504034188977 109276703413528878025641733)
      ·
        refine ⟨20489381890036664629807825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109276703413528878025641733 20489381890036664629807825)
        ·
          refine ⟨15367036417527498472355869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20489381890036664629807825 15367036417527498472355869)
          ·
            refine ⟨5762638656572811927133451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15367036417527498472355869 5762638656572811927133451)
            ·
              refine ⟨8643957984859217890700177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5762638656572811927133451 8643957984859217890700177)
              ·
                refine ⟨6482968488644413418025133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8643957984859217890700177 6482968488644413418025133)
                ·
                  refine ⟨2431113183241655031759425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6482968488644413418025133 2431113183241655031759425)
                  ·
                    refine ⟨1823334887431241273819569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2431113183241655031759425 1823334887431241273819569)
                    ·
                      refine ⟨1367501165573430955364677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823334887431241273819569 1367501165573430955364677)
                      ·
                        rfl

theorem cell23_2663199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_2663199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663199 prefixEnd_2663199 := by exact prefixLift 2663199
  have htrace : WordTrace (prefixWord ++ tailWord_2663199) baseStart_2663199 baseEnd_2663199 := by
    simpa [prefixWord, tailWord_2663199, baseEnd_2663199] using wordTrace_append hprefix tailTrace_2663199
  have hstable : (prefixWord ++ tailWord_2663199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663199).length < 2 ^ (prefixWord ++ tailWord_2663199).sum := by decide
  have hdescent : baseEnd_2663199 < baseStart_2663199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663202 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_2663202 : Nat := 118140960795 + 2663202 * 2 ^ 59
def prefixEnd_2663202 : Nat := 4983230072969 + 3 ^ 40 * 2663202 * 2
def baseEnd_2663202 : Nat := 1367502706015394443627163

theorem tailTrace_2663202 : CollatzResearch.WordTrace tailWord_2663202 prefixEnd_2663202 1367502706015394443627163 := by
  unfold tailWord_2663202
  simp only [CollatzResearch.WordTrace]
  refine ⟨24283739224420366883787965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64756637931787645023434573 24283739224420366883787965)
  ·
    refine ⟨9106402209157637581420487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24283739224420366883787965 9106402209157637581420487)
    ·
      refine ⟨13659603313736456372130731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9106402209157637581420487 13659603313736456372130731)
      ·
        refine ⟨20489404970604684558196097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13659603313736456372130731 20489404970604684558196097)
        ·
          refine ⟨15367053727953513418647073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20489404970604684558196097 15367053727953513418647073)
          ·
            refine ⟨11525290295965135063985305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15367053727953513418647073 11525290295965135063985305)
            ·
              refine ⟨8643967721973851297988979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11525290295965135063985305 8643967721973851297988979)
              ·
                refine ⟨12965951582960776946983469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8643967721973851297988979 12965951582960776946983469)
                ·
                  refine ⟨4862231843610291355118801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12965951582960776946983469 4862231843610291355118801)
                  ·
                    refine ⟨3646673882707718516339101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4862231843610291355118801 3646673882707718516339101)
                    ·
                      refine ⟨1367502706015394443627163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3646673882707718516339101 1367502706015394443627163)
                      ·
                        rfl

theorem cell23_2663202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_2663202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663202 prefixEnd_2663202 := by exact prefixLift 2663202
  have htrace : WordTrace (prefixWord ++ tailWord_2663202) baseStart_2663202 baseEnd_2663202 := by
    simpa [prefixWord, tailWord_2663202, baseEnd_2663202] using wordTrace_append hprefix tailTrace_2663202
  have hstable : (prefixWord ++ tailWord_2663202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663202).length < 2 ^ (prefixWord ++ tailWord_2663202).sum := by decide
  have hdescent : baseEnd_2663202 < baseStart_2663202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663205 : List Nat := [1, 3, 1, 2, 3, 1, 5, 7]
def baseStart_2663205 : Nat := 118140960795 + 2663205 * 2 ^ 59
def prefixEnd_2663205 : Nat := 4983230072969 + 3 ^ 40 * 2663205 * 2
def baseEnd_2663205 : Nat := 50648305424346590069987

theorem tailTrace_2663205 : CollatzResearch.WordTrace tailWord_2663205 prefixEnd_2663205 50648305424346590069987 := by
  unfold tailWord_2663205
  simp only [CollatzResearch.WordTrace]
  refine ⟨97135066316670599047511069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64756710877780399365007379 97135066316670599047511069)
  ·
    refine ⟨36425649868751474642816651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97135066316670599047511069 36425649868751474642816651)
    ·
      refine ⟨54638474803127211964224977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36425649868751474642816651 54638474803127211964224977)
      ·
        refine ⟨40978856102345408973168733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54638474803127211964224977 40978856102345408973168733)
        ·
          refine ⟨15367071038379528364938275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40978856102345408973168733 15367071038379528364938275)
          ·
            refine ⟨23050606557569292547407413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15367071038379528364938275 23050606557569292547407413)
            ·
              refine ⟨2160994364772121176319445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23050606557569292547407413 2160994364772121176319445)
              ·
                refine ⟨50648305424346590069987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2160994364772121176319445 50648305424346590069987)
                ·
                  rfl

theorem cell23_2663205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 7].length) (baseStart_2663205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663205 prefixEnd_2663205 := by exact prefixLift 2663205
  have htrace : WordTrace (prefixWord ++ tailWord_2663205) baseStart_2663205 baseEnd_2663205 := by
    simpa [prefixWord, tailWord_2663205, baseEnd_2663205] using wordTrace_append hprefix tailTrace_2663205
  have hstable : (prefixWord ++ tailWord_2663205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663205).length < 2 ^ (prefixWord ++ tailWord_2663205).sum := by decide
  have hdescent : baseEnd_2663205 < baseStart_2663205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663213 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2663213 : Nat := 118140960795 + 2663213 * 2 ^ 59
def prefixEnd_2663213 : Nat := 4983230072969 + 3 ^ 40 * 2663213 * 2
def baseEnd_2663213 : Nat := 455836118100864633529871

theorem tailTrace_2663213 : CollatzResearch.WordTrace tailWord_2663213 prefixEnd_2663213 455836118100864633529871 := by
  unfold tailWord_2663213
  simp only [CollatzResearch.WordTrace]
  refine ⟨97135358100641616413802293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64756905400427744275868195 97135358100641616413802293)
  ·
    refine ⟨9106439821935151538793965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97135358100641616413802293 9106439821935151538793965)
    ·
      refine ⟨3414914933225681827047737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9106439821935151538793965 3414914933225681827047737)
      ·
        refine ⟨2561186199919261370285803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3414914933225681827047737 2561186199919261370285803)
        ·
          refine ⟨3841779299878892055428705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561186199919261370285803 3841779299878892055428705)
          ·
            refine ⟨2881334474909169041571529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3841779299878892055428705 2881334474909169041571529)
            ·
              refine ⟨2161000856181876781178647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2881334474909169041571529 2161000856181876781178647)
              ·
                refine ⟨3241501284272815171767971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161000856181876781178647 3241501284272815171767971)
                ·
                  refine ⟨4862251926409222757651957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241501284272815171767971 4862251926409222757651957)
                  ·
                    refine ⟨455836118100864633529871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4862251926409222757651957 455836118100864633529871)
                    ·
                      rfl

theorem cell23_2663213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2663213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663213 prefixEnd_2663213 := by exact prefixLift 2663213
  have htrace : WordTrace (prefixWord ++ tailWord_2663213) baseStart_2663213 baseEnd_2663213 := by
    simpa [prefixWord, tailWord_2663213, baseEnd_2663213] using wordTrace_append hprefix tailTrace_2663213
  have hstable : (prefixWord ++ tailWord_2663213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663213).length < 2 ^ (prefixWord ++ tailWord_2663213).sum := by decide
  have hdescent : baseEnd_2663213 < baseStart_2663213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663219 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 1, 2, 3]
def baseStart_2663219 : Nat := 118140960795 + 2663219 * 2 ^ 59
def prefixEnd_2663219 : Nat := 4983230072969 + 3 ^ 40 * 2663219 * 2
def baseEnd_2663219 : Nat := 1367511435186520877114585

theorem tailTrace_2663219 : CollatzResearch.WordTrace tailWord_2663219 prefixEnd_2663219 1367511435186520877114585 := by
  unfold tailWord_2663219
  simp only [CollatzResearch.WordTrace]
  refine ⟨97135576938619879438520711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64757051292413252959013807 97135576938619879438520711)
  ·
    refine ⟨145703365407929819157781067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97135576938619879438520711 145703365407929819157781067)
    ·
      refine ⟨218555048111894728736671601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145703365407929819157781067 218555048111894728736671601)
      ·
        refine ⟨163916286083921046552503701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218555048111894728736671601 163916286083921046552503701)
        ·
          refine ⟨7683575910183799057148611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 163916286083921046552503701 7683575910183799057148611)
          ·
            refine ⟨11525363865275698585722917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7683575910183799057148611 11525363865275698585722917)
            ·
              refine ⟨2161005724739193484823047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11525363865275698585722917 2161005724739193484823047)
              ·
                refine ⟨3241508587108790227234571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161005724739193484823047 3241508587108790227234571)
                ·
                  refine ⟨4862262880663185340851857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241508587108790227234571 4862262880663185340851857)
                  ·
                    refine ⟨3646697160497389005638893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4862262880663185340851857 3646697160497389005638893)
                    ·
                      refine ⟨1367511435186520877114585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3646697160497389005638893 1367511435186520877114585)
                      ·
                        rfl

theorem cell23_2663219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 2, 3].length) (baseStart_2663219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663219 prefixEnd_2663219 := by exact prefixLift 2663219
  have htrace : WordTrace (prefixWord ++ tailWord_2663219) baseStart_2663219 baseEnd_2663219 := by
    simpa [prefixWord, tailWord_2663219, baseEnd_2663219] using wordTrace_append hprefix tailTrace_2663219
  have hstable : (prefixWord ++ tailWord_2663219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663219).length < 2 ^ (prefixWord ++ tailWord_2663219).sum := by decide
  have hdescent : baseEnd_2663219 < baseStart_2663219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663222 : List Nat := [5, 1, 2, 2, 2, 1, 10]
def baseStart_2663222 : Nat := 118140960795 + 2663222 * 2 ^ 59
def prefixEnd_2663222 : Nat := 4983230072969 + 3 ^ 40 * 2663222 * 2
def baseEnd_2663222 : Nat := 16882876242326967473791

theorem tailTrace_2663222 : CollatzResearch.WordTrace tailWord_2663222 prefixEnd_2663222 16882876242326967473791 := by
  unfold tailWord_2663222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6070980397350563184429995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64757124238406007300586613 6070980397350563184429995)
  ·
    refine ⟨9106470596025844776644993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6070980397350563184429995 9106470596025844776644993)
    ·
      refine ⟨6829852947019383582483745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9106470596025844776644993 6829852947019383582483745)
      ·
        refine ⟨5122389710264537686862809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6829852947019383582483745 5122389710264537686862809)
        ·
          refine ⟨3841792282698403265147107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5122389710264537686862809 3841792282698403265147107)
          ·
            refine ⟨5762688424047604897720661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3841792282698403265147107 5762688424047604897720661)
            ·
              refine ⟨16882876242326967473791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5762688424047604897720661 16882876242326967473791)
              ·
                rfl

theorem cell23_2663222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 10].length) (baseStart_2663222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663222 prefixEnd_2663222 := by exact prefixLift 2663222
  have htrace : WordTrace (prefixWord ++ tailWord_2663222) baseStart_2663222 baseEnd_2663222 := by
    simpa [prefixWord, tailWord_2663222, baseEnd_2663222] using wordTrace_append hprefix tailTrace_2663222
  have hstable : (prefixWord ++ tailWord_2663222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663222).length < 2 ^ (prefixWord ++ tailWord_2663222).sum := by decide
  have hdescent : baseEnd_2663222 < baseStart_2663222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663226 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 2, 4]
def baseStart_2663226 : Nat := 118140960795 + 2663226 * 2 ^ 59
def prefixEnd_2663226 : Nat := 4983230072969 + 3 ^ 40 * 2663226 * 2
def baseEnd_2663226 : Nat := 455838343183700783242351

theorem tailTrace_2663226 : CollatzResearch.WordTrace tailWord_2663226 prefixEnd_2663226 455838343183700783242351 := by
  unfold tailWord_2663226
  simp only [CollatzResearch.WordTrace]
  refine ⟨24283958062398629908506383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64757221499729679756017021 24283958062398629908506383)
  ·
    refine ⟨36425937093597944862759575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24283958062398629908506383 36425937093597944862759575)
    ·
      refine ⟨54638905640396917294139363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36425937093597944862759575 54638905640396917294139363)
      ·
        refine ⟨81958358460595375941209045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54638905640396917294139363 81958358460595375941209045)
        ·
          refine ⟨1920899026420204123622087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 81958358460595375941209045 1920899026420204123622087)
          ·
            refine ⟨2881348539630306185433131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920899026420204123622087 2881348539630306185433131)
            ·
              refine ⟨4322022809445459278149697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881348539630306185433131 4322022809445459278149697)
              ·
                refine ⟨3241517107084094458612273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4322022809445459278149697 3241517107084094458612273)
                ·
                  refine ⟨2431137830313070843959205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3241517107084094458612273 2431137830313070843959205)
                  ·
                    refine ⟨455838343183700783242351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2431137830313070843959205 455838343183700783242351)
                    ·
                      rfl

theorem cell23_2663226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_2663226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663226 prefixEnd_2663226 := by exact prefixLift 2663226
  have htrace : WordTrace (prefixWord ++ tailWord_2663226) baseStart_2663226 baseEnd_2663226 := by
    simpa [prefixWord, tailWord_2663226, baseEnd_2663226] using wordTrace_append hprefix tailTrace_2663226
  have hstable : (prefixWord ++ tailWord_2663226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663226).length < 2 ^ (prefixWord ++ tailWord_2663226).sum := by decide
  have hdescent : baseEnd_2663226 < baseStart_2663226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663233 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2663233 : Nat := 118140960795 + 2663233 * 2 ^ 59
def prefixEnd_2663233 : Nat := 4983230072969 + 3 ^ 40 * 2663233 * 2
def baseEnd_2663233 : Nat := 1367518623915683822339521

theorem tailTrace_2663233 : CollatzResearch.WordTrace tailWord_2663233 prefixEnd_2663233 1367518623915683822339521 := by
  unfold tailWord_2663233
  simp only [CollatzResearch.WordTrace]
  refine ⟨97136087560569159829530353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64757391707046106553020235 97136087560569159829530353)
  ·
    refine ⟨72852065670426869872147765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97136087560569159829530353 72852065670426869872147765)
    ·
      refine ⟨6829881156602519050513853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72852065670426869872147765 6829881156602519050513853)
      ·
        refine ⟨2561205433725944643942695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6829881156602519050513853 2561205433725944643942695)
        ·
          refine ⟨3841808150588916965914043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561205433725944643942695 3841808150588916965914043)
          ·
            refine ⟨5762712225883375448871065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3841808150588916965914043 5762712225883375448871065)
            ·
              refine ⟨4322034169412531586653299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5762712225883375448871065 4322034169412531586653299)
              ·
                refine ⟨6483051254118797379979949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322034169412531586653299 6483051254118797379979949)
                ·
                  refine ⟨2431144220294549017492481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6483051254118797379979949 2431144220294549017492481)
                  ·
                    refine ⟨1823358165220911763119361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2431144220294549017492481 1823358165220911763119361)
                    ·
                      refine ⟨1367518623915683822339521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823358165220911763119361 1367518623915683822339521)
                      ·
                        rfl

theorem cell23_2663233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2663233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663233 prefixEnd_2663233 := by exact prefixLift 2663233
  have htrace : WordTrace (prefixWord ++ tailWord_2663233) baseStart_2663233 baseEnd_2663233 := by
    simpa [prefixWord, tailWord_2663233, baseEnd_2663233] using wordTrace_append hprefix tailTrace_2663233
  have hstable : (prefixWord ++ tailWord_2663233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663233).length < 2 ^ (prefixWord ++ tailWord_2663233).sum := by decide
  have hdescent : baseEnd_2663233 < baseStart_2663233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663242 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2]
def baseStart_2663242 : Nat := 118140960795 + 2663242 * 2 ^ 59
def prefixEnd_2663242 : Nat := 4983230072969 + 3 ^ 40 * 2663242 * 2
def baseEnd_2663242 : Nat := 1367523245241574287126979

theorem tailTrace_2663242 : CollatzResearch.WordTrace tailWord_2663242 prefixEnd_2663242 1367523245241574287126979 := by
  unfold tailWord_2663242
  simp only [CollatzResearch.WordTrace]
  refine ⟨24284103954384138591651995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64757610545024369577738653 24284103954384138591651995)
  ·
    refine ⟨36426155931576207887477993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24284103954384138591651995 36426155931576207887477993)
    ·
      refine ⟨27319616948682155915608495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36426155931576207887477993 27319616948682155915608495)
      ·
        refine ⟨40979425423023233873412743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27319616948682155915608495 40979425423023233873412743)
        ·
          refine ⟨61469138134534850810119115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40979425423023233873412743 61469138134534850810119115)
          ·
            refine ⟨92203707201802276215178673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61469138134534850810119115 92203707201802276215178673)
            ·
              refine ⟨69152780401351707161384005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92203707201802276215178673 69152780401351707161384005)
              ·
                refine ⟨12966146325253445092759501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69152780401351707161384005 12966146325253445092759501)
                ·
                  refine ⟨4862304871970041909784813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12966146325253445092759501 4862304871970041909784813)
                  ·
                    refine ⟨1823364326988765716169305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4862304871970041909784813 1823364326988765716169305)
                    ·
                      refine ⟨1367523245241574287126979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823364326988765716169305 1367523245241574287126979)
                      ·
                        rfl

theorem cell23_2663242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_2663242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663242 prefixEnd_2663242 := by exact prefixLift 2663242
  have htrace : WordTrace (prefixWord ++ tailWord_2663242) baseStart_2663242 baseEnd_2663242 := by
    simpa [prefixWord, tailWord_2663242, baseEnd_2663242] using wordTrace_append hprefix tailTrace_2663242
  have hstable : (prefixWord ++ tailWord_2663242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663242).length < 2 ^ (prefixWord ++ tailWord_2663242).sum := by decide
  have hdescent : baseEnd_2663242 < baseStart_2663242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663249 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 1, 3, 3]
def baseStart_2663249 : Nat := 118140960795 + 2663249 * 2 ^ 59
def prefixEnd_2663249 : Nat := 4983230072969 + 3 ^ 40 * 2663249 * 2
def baseEnd_2663249 : Nat := 1367526839606155759739447

theorem tailTrace_2663249 : CollatzResearch.WordTrace tailWord_2663249 prefixEnd_2663249 1367526839606155759739447 := by
  unfold tailWord_2663249
  simp only [CollatzResearch.WordTrace]
  refine ⟨97136671128511194562112801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64757780752340796374741867 97136671128511194562112801)
  ·
    refine ⟨72852503346383395921584601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97136671128511194562112801 72852503346383395921584601)
    ·
      refine ⟨54639377509787546941188451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72852503346383395921584601 54639377509787546941188451)
      ·
        refine ⟨81959066264681320411782677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54639377509787546941188451 81959066264681320411782677)
        ·
          refine ⟨3841831231156936894302313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81959066264681320411782677 3841831231156936894302313)
          ·
            refine ⟨2881373423367702670726735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3841831231156936894302313 2881373423367702670726735)
            ·
              refine ⟨4322060135051554006090103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881373423367702670726735 4322060135051554006090103)
              ·
                refine ⟨6483090202577331009135155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322060135051554006090103 6483090202577331009135155)
                ·
                  refine ⟨9724635303865996513702733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6483090202577331009135155 9724635303865996513702733)
                  ·
                    refine ⟨3646738238949748692638525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9724635303865996513702733 3646738238949748692638525)
                    ·
                      refine ⟨1367526839606155759739447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3646738238949748692638525 1367526839606155759739447)
                      ·
                        rfl

theorem cell23_2663249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_2663249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663249 prefixEnd_2663249 := by exact prefixLift 2663249
  have htrace : WordTrace (prefixWord ++ tailWord_2663249) baseStart_2663249 baseEnd_2663249 := by
    simpa [prefixWord, tailWord_2663249, baseEnd_2663249] using wordTrace_append hprefix tailTrace_2663249
  have hstable : (prefixWord ++ tailWord_2663249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663249).length < 2 ^ (prefixWord ++ tailWord_2663249).sum := by decide
  have hdescent : baseEnd_2663249 < baseStart_2663249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663289 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 4, 2, 2]
def baseStart_2663289 : Nat := 118140960795 + 2663289 * 2 ^ 59
def prefixEnd_2663289 : Nat := 4983230072969 + 3 ^ 40 * 2663289 * 2
def baseEnd_2663289 : Nat := 1367547378832335603239263

theorem tailTrace_2663289 : CollatzResearch.WordTrace tailWord_2663289 prefixEnd_2663289 1367547378832335603239263 := by
  unfold tailWord_2663289
  simp only [CollatzResearch.WordTrace]
  refine ⟨97138130048366281393568921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64758753365577520929045947 97138130048366281393568921)
  ·
    refine ⟨72853597536274711045176691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97138130048366281393568921 72853597536274711045176691)
    ·
      refine ⟨109280396304412066567765037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72853597536274711045176691 109280396304412066567765037)
      ·
        refine ⟨40980148614154524962911889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109280396304412066567765037 40980148614154524962911889)
        ·
          refine ⟨30735111460615893722183917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40980148614154524962911889 30735111460615893722183917)
          ·
            refine ⟨11525666797730960145818969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30735111460615893722183917 11525666797730960145818969)
            ·
              refine ⟨8644250098298220109364227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11525666797730960145818969 8644250098298220109364227)
              ·
                refine ⟨12966375147447330164046341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8644250098298220109364227 12966375147447330164046341)
                ·
                  refine ⟨2431195340146374405758689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12966375147447330164046341 2431195340146374405758689)
                  ·
                    refine ⟨1823396505109780804319017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2431195340146374405758689 1823396505109780804319017)
                    ·
                      refine ⟨1367547378832335603239263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823396505109780804319017 1367547378832335603239263)
                      ·
                        rfl

theorem cell23_2663289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_2663289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663289 prefixEnd_2663289 := by exact prefixLift 2663289
  have htrace : WordTrace (prefixWord ++ tailWord_2663289) baseStart_2663289 baseEnd_2663289 := by
    simpa [prefixWord, tailWord_2663289, baseEnd_2663289] using wordTrace_append hprefix tailTrace_2663289
  have hstable : (prefixWord ++ tailWord_2663289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663289).length < 2 ^ (prefixWord ++ tailWord_2663289).sum := by decide
  have hdescent : baseEnd_2663289 < baseStart_2663289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663295 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 7]
def baseStart_2663295 : Nat := 118140960795 + 2663295 * 2 ^ 59
def prefixEnd_2663295 : Nat := 4983230072969 + 3 ^ 40 * 2663295 * 2
def baseEnd_2663295 : Nat := 151950051079584731084915

theorem tailTrace_2663295 : CollatzResearch.WordTrace tailWord_2663295 prefixEnd_2663295 151950051079584731084915 := by
  unfold tailWord_2663295
  simp only [CollatzResearch.WordTrace]
  refine ⟨97138348886344544418287339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64758899257563029612191559 97138348886344544418287339)
  ·
    refine ⟨145707523329516816627431009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97138348886344544418287339 145707523329516816627431009)
    ·
      refine ⟨109280642497137612470573257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145707523329516816627431009 109280642497137612470573257)
      ·
        refine ⟨81960481872853209352929943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109280642497137612470573257 81960481872853209352929943)
        ·
          refine ⟨122940722809279814029394915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81960481872853209352929943 122940722809279814029394915)
          ·
            refine ⟨184411084213919721044092373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122940722809279814029394915 184411084213919721044092373)
            ·
              refine ⟨4322134786263743461970915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 184411084213919721044092373 4322134786263743461970915)
              ·
                refine ⟨6483202179395615192956373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322134786263743461970915 6483202179395615192956373)
                ·
                  refine ⟨151950051079584731084915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6483202179395615192956373 151950051079584731084915)
                  ·
                    rfl

theorem cell23_2663295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 7].length) (baseStart_2663295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663295 prefixEnd_2663295 := by exact prefixLift 2663295
  have htrace : WordTrace (prefixWord ++ tailWord_2663295) baseStart_2663295 baseEnd_2663295 := by
    simpa [prefixWord, tailWord_2663295, baseEnd_2663295] using wordTrace_append hprefix tailTrace_2663295
  have hstable : (prefixWord ++ tailWord_2663295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663295).length < 2 ^ (prefixWord ++ tailWord_2663295).sum := by decide
  have hdescent : baseEnd_2663295 < baseStart_2663295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663402 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 8]
def baseStart_2663402 : Nat := 118140960795 + 2663402 * 2 ^ 59
def prefixEnd_2663402 : Nat := 4983230072969 + 3 ^ 40 * 2663402 * 2
def baseEnd_2663402 : Nat := 151956155794032629014027

theorem tailTrace_2663402 : CollatzResearch.WordTrace tailWord_2663402 prefixEnd_2663402 151956155794032629014027 := by
  unfold tailWord_2663402
  simp only [CollatzResearch.WordTrace]
  refine ⟨24285562874239225423108115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64761500997971267794954973 24285562874239225423108115)
  ·
    refine ⟨36428344311358838134662173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24285562874239225423108115 36428344311358838134662173)
    ·
      refine ⟨13660629116759564300498315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36428344311358838134662173 13660629116759564300498315)
      ·
        refine ⟨20490943675139346450747473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13660629116759564300498315 20490943675139346450747473)
        ·
          refine ⟨15368207756354509838060605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20490943675139346450747473 15368207756354509838060605)
          ·
            refine ⟨5763077908632941189272727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15368207756354509838060605 5763077908632941189272727)
            ·
              refine ⟨8644616862949411783909091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5763077908632941189272727 8644616862949411783909091)
              ·
                refine ⟨12966925294424117675863637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8644616862949411783909091 12966925294424117675863637)
                ·
                  refine ⟨151956155794032629014027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12966925294424117675863637 151956155794032629014027)
                  ·
                    rfl

theorem cell23_2663402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_2663402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663402 prefixEnd_2663402 := by exact prefixLift 2663402
  have htrace : WordTrace (prefixWord ++ tailWord_2663402) baseStart_2663402 baseEnd_2663402 := by
    simpa [prefixWord, tailWord_2663402, baseEnd_2663402] using wordTrace_append hprefix tailTrace_2663402
  have hstable : (prefixWord ++ tailWord_2663402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663402).length < 2 ^ (prefixWord ++ tailWord_2663402).sum := by decide
  have hdescent : baseEnd_2663402 < baseStart_2663402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663406 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2663406 : Nat := 118140960795 + 2663406 * 2 ^ 59
def prefixEnd_2663406 : Nat := 4983230072969 + 3 ^ 40 * 2663406 * 2
def baseEnd_2663406 : Nat := 455869152022970548492075

theorem tailTrace_2663406 : CollatzResearch.WordTrace tailWord_2663406 prefixEnd_2663406 455869152022970548492075 := by
  unfold tailWord_2663406
  simp only [CollatzResearch.WordTrace]
  refine ⟨12142799673617801296947259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64761598259294940250385381 12142799673617801296947259)
  ·
    refine ⟨18214199510426701945420889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12142799673617801296947259 18214199510426701945420889)
    ·
      refine ⟨13660649632820026459065667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18214199510426701945420889 13660649632820026459065667)
      ·
        refine ⟨20490974449230039688598501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13660649632820026459065667 20490974449230039688598501)
        ·
          refine ⟨3842057709230632441612219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20490974449230039688598501 3842057709230632441612219)
          ·
            refine ⟨5763086563845948662418329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3842057709230632441612219 5763086563845948662418329)
            ·
              refine ⟨4322314922884461496813747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5763086563845948662418329 4322314922884461496813747)
              ·
                refine ⟨6483472384326692245220621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322314922884461496813747 6483472384326692245220621)
                ·
                  refine ⟨2431302144122509591957733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6483472384326692245220621 2431302144122509591957733)
                  ·
                    refine ⟨455869152022970548492075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2431302144122509591957733 455869152022970548492075)
                    ·
                      rfl

theorem cell23_2663406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2663406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663406 prefixEnd_2663406 := by exact prefixLift 2663406
  have htrace : WordTrace (prefixWord ++ tailWord_2663406) baseStart_2663406 baseEnd_2663406 := by
    simpa [prefixWord, tailWord_2663406, baseEnd_2663406] using wordTrace_append hprefix tailTrace_2663406
  have hstable : (prefixWord ++ tailWord_2663406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663406).length < 2 ^ (prefixWord ++ tailWord_2663406).sum := by decide
  have hdescent : baseEnd_2663406 < baseStart_2663406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663429 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 3, 1, 3]
def baseStart_2663429 : Nat := 118140960795 + 2663429 * 2 ^ 59
def prefixEnd_2663429 : Nat := 4983230072969 + 3 ^ 40 * 2663429 * 2
def baseEnd_2663429 : Nat := 1367619266123965055488619

theorem tailTrace_2663429 : CollatzResearch.WordTrace tailWord_2663429 prefixEnd_2663429 1367619266123965055488619 := by
  unfold tailWord_2663429
  simp only [CollatzResearch.WordTrace]
  refine ⟨97143236267859085303665341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64762157511906056869110227 97143236267859085303665341)
  ·
    refine ⟨36428713600447156988874503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97143236267859085303665341 36428713600447156988874503)
    ·
      refine ⟨54643070400670735483311755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36428713600447156988874503 54643070400670735483311755)
      ·
        refine ⟨81964605601006103224967633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54643070400670735483311755 81964605601006103224967633)
        ·
          refine ⟨61473454200754577418725725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81964605601006103224967633 61473454200754577418725725)
          ·
            refine ⟨23052545325282966532022147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61473454200754577418725725 23052545325282966532022147)
            ·
              refine ⟨34578817987924449798033221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23052545325282966532022147 34578817987924449798033221)
              ·
                refine ⟨6483528372735834337131229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34578817987924449798033221 6483528372735834337131229)
                ·
                  refine ⟨2431323139775937876424211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6483528372735834337131229 2431323139775937876424211)
                  ·
                    refine ⟨3646984709663906814636317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2431323139775937876424211 3646984709663906814636317)
                    ·
                      refine ⟨1367619266123965055488619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3646984709663906814636317 1367619266123965055488619)
                      ·
                        rfl

theorem cell23_2663429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_2663429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663429 prefixEnd_2663429 := by exact prefixLift 2663429
  have htrace : WordTrace (prefixWord ++ tailWord_2663429) baseStart_2663429 baseEnd_2663429 := by
    simpa [prefixWord, tailWord_2663429, baseEnd_2663429] using wordTrace_append hprefix tailTrace_2663429
  have hstable : (prefixWord ++ tailWord_2663429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663429).length < 2 ^ (prefixWord ++ tailWord_2663429).sum := by decide
  have hdescent : baseEnd_2663429 < baseStart_2663429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663463 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2663463 : Nat := 118140960795 + 2663463 * 2 ^ 59
def prefixEnd_2663463 : Nat := 4983230072969 + 3 ^ 40 * 2663463 * 2
def baseEnd_2663463 : Nat := 1367636724466217922463463

theorem tailTrace_2663463 : CollatzResearch.WordTrace tailWord_2663463 prefixEnd_2663463 1367636724466217922463463 := by
  unfold tailWord_2663463
  simp only [CollatzResearch.WordTrace]
  refine ⟨97144476349735909110403043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64762984233157272740268695 97144476349735909110403043)
  ·
    refine ⟨145716714524603863665604565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97144476349735909110403043 145716714524603863665604565)
    ·
      refine ⟨3415235496670403054662607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 145716714524603863665604565 3415235496670403054662607)
      ·
        refine ⟨5122853245005604581993911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3415235496670403054662607 5122853245005604581993911)
        ·
          refine ⟨7684279867508406872990867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122853245005604581993911 7684279867508406872990867)
          ·
            refine ⟨11526419801262610309486301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7684279867508406872990867 11526419801262610309486301)
            ·
              refine ⟨4322407425473478866057363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11526419801262610309486301 4322407425473478866057363)
              ·
                refine ⟨6483611138210218299086045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322407425473478866057363 6483611138210218299086045)
                ·
                  refine ⟨2431354176828831862157267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6483611138210218299086045 2431354176828831862157267)
                  ·
                    refine ⟨3647031265243247793235901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2431354176828831862157267 3647031265243247793235901)
                    ·
                      refine ⟨1367636724466217922463463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3647031265243247793235901 1367636724466217922463463)
                      ·
                        rfl

theorem cell23_2663463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2663463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663463 prefixEnd_2663463 := by exact prefixLift 2663463
  have htrace : WordTrace (prefixWord ++ tailWord_2663463) baseStart_2663463 baseEnd_2663463 := by
    simpa [prefixWord, tailWord_2663463, baseEnd_2663463] using wordTrace_append hprefix tailTrace_2663463
  have hstable : (prefixWord ++ tailWord_2663463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663463).length < 2 ^ (prefixWord ++ tailWord_2663463).sum := by decide
  have hdescent : baseEnd_2663463 < baseStart_2663463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663472 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 5]
def baseStart_2663472 : Nat := 118140960795 + 2663472 * 2 ^ 59
def prefixEnd_2663472 : Nat := 4983230072969 + 3 ^ 40 * 2663472 * 2
def baseEnd_2663472 : Nat := 1367641345792108387250921

theorem tailTrace_2663472 : CollatzResearch.WordTrace tailWord_2663472 prefixEnd_2663472 1367641345792108387250921 := by
  unfold tailWord_2663472
  simp only [CollatzResearch.WordTrace]
  refine ⟨48572402303351651823740335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64763203071135535764987113 48572402303351651823740335)
  ·
    refine ⟨72858603455027477735610503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48572402303351651823740335 72858603455027477735610503)
    ·
      refine ⟨109287905182541216603415755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72858603455027477735610503 109287905182541216603415755)
      ·
        refine ⟨163931857773811824905123633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109287905182541216603415755 163931857773811824905123633)
        ·
          refine ⟨122948893330358868678842725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163931857773811824905123633 122948893330358868678842725)
          ·
            refine ⟨23052917499442287877283011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122948893330358868678842725 23052917499442287877283011)
            ·
              refine ⟨34579376249163431815924517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23052917499442287877283011 34579376249163431815924517)
              ·
                refine ⟨6483633046718143465485847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34579376249163431815924517 6483633046718143465485847)
                ·
                  refine ⟨9725449570077215198228771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6483633046718143465485847 9725449570077215198228771)
                  ·
                    refine ⟨14588174355115822797343157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9725449570077215198228771 14588174355115822797343157)
                    ·
                      refine ⟨1367641345792108387250921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14588174355115822797343157 1367641345792108387250921)
                      ·
                        rfl

theorem cell23_2663472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_2663472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663472 prefixEnd_2663472 := by exact prefixLift 2663472
  have htrace : WordTrace (prefixWord ++ tailWord_2663472) baseStart_2663472 baseEnd_2663472 := by
    simpa [prefixWord, tailWord_2663472, baseEnd_2663472] using wordTrace_append hprefix tailTrace_2663472
  have hstable : (prefixWord ++ tailWord_2663472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663472).length < 2 ^ (prefixWord ++ tailWord_2663472).sum := by decide
  have hdescent : baseEnd_2663472 < baseStart_2663472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663482 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_2663482 : Nat := 118140960795 + 2663482 * 2 ^ 59
def prefixEnd_2663482 : Nat := 4983230072969 + 3 ^ 40 * 2663482 * 2
def baseEnd_2663482 : Nat := 1367646480598653348125875

theorem tailTrace_2663482 : CollatzResearch.WordTrace tailWord_2663482 prefixEnd_2663482 1367646480598653348125875 := by
  unfold tailWord_2663482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24286292334166768838836175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64763446224444716903563133 24286292334166768838836175)
  ·
    refine ⟨36429438501250153258254263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24286292334166768838836175 36429438501250153258254263)
    ·
      refine ⟨54644157751875229887381395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36429438501250153258254263 54644157751875229887381395)
      ·
        refine ⟨81966236627812844831072093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54644157751875229887381395 81966236627812844831072093)
        ·
          refine ⟨30737338735429816811652035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81966236627812844831072093 30737338735429816811652035)
          ·
            refine ⟨46106008103144725217478053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30737338735429816811652035 46106008103144725217478053)
            ·
              refine ⟨8644876519339635978277135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46106008103144725217478053 8644876519339635978277135)
              ·
                refine ⟨12967314779009453967415703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8644876519339635978277135 12967314779009453967415703)
                ·
                  refine ⟨19450972168514180951123555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12967314779009453967415703 19450972168514180951123555)
                  ·
                    refine ⟨29176458252771271426685333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19450972168514180951123555 29176458252771271426685333)
                    ·
                      refine ⟨1367646480598653348125875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29176458252771271426685333 1367646480598653348125875)
                      ·
                        rfl

theorem cell23_2663482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_2663482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663482 prefixEnd_2663482 := by exact prefixLift 2663482
  have htrace : WordTrace (prefixWord ++ tailWord_2663482) baseStart_2663482 baseEnd_2663482 := by
    simpa [prefixWord, tailWord_2663482, baseEnd_2663482] using wordTrace_append hprefix tailTrace_2663482
  have hstable : (prefixWord ++ tailWord_2663482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663482).length < 2 ^ (prefixWord ++ tailWord_2663482).sum := by decide
  have hdescent : baseEnd_2663482 < baseStart_2663482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663486 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2663486 : Nat := 118140960795 + 2663486 * 2 ^ 59
def prefixEnd_2663486 : Nat := 4983230072969 + 3 ^ 40 * 2663486 * 2
def baseEnd_2663486 : Nat := 1367648534521271332475857

theorem tailTrace_2663486 : CollatzResearch.WordTrace tailWord_2663486 prefixEnd_2663486 1367648534521271332475857 := by
  unfold tailWord_2663486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12143164403581573004811289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64763543485768389358993541 12143164403581573004811289)
  ·
    refine ⟨9107373302686179753608467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12143164403581573004811289 9107373302686179753608467)
    ·
      refine ⟨13661059954029269630412701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9107373302686179753608467 13661059954029269630412701)
      ·
        refine ⟨5122897482760976111404763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13661059954029269630412701 5122897482760976111404763)
        ·
          refine ⟨7684346224141464167107145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122897482760976111404763 7684346224141464167107145)
          ·
            refine ⟨5763259668106098125330359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7684346224141464167107145 5763259668106098125330359)
            ·
              refine ⟨8644889502159147187995539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5763259668106098125330359 8644889502159147187995539)
              ·
                refine ⟨12967334253238720781993309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8644889502159147187995539 12967334253238720781993309)
                ·
                  refine ⟨4862750344964520293247491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12967334253238720781993309 4862750344964520293247491)
                  ·
                    refine ⟨7294125517446780439871237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4862750344964520293247491 7294125517446780439871237)
                    ·
                      refine ⟨1367648534521271332475857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7294125517446780439871237 1367648534521271332475857)
                      ·
                        rfl

theorem cell23_2663486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2663486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663486 prefixEnd_2663486 := by exact prefixLift 2663486
  have htrace : WordTrace (prefixWord ++ tailWord_2663486) baseStart_2663486 baseEnd_2663486 := by
    simpa [prefixWord, tailWord_2663486, baseEnd_2663486] using wordTrace_append hprefix tailTrace_2663486
  have hstable : (prefixWord ++ tailWord_2663486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663486).length < 2 ^ (prefixWord ++ tailWord_2663486).sum := by decide
  have hdescent : baseEnd_2663486 < baseStart_2663486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663506 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_2663506 : Nat := 118140960795 + 2663506 * 2 ^ 59
def prefixEnd_2663506 : Nat := 4983230072969 + 3 ^ 40 * 2663506 * 2
def baseEnd_2663506 : Nat := 1367658804134361254225765

theorem tailTrace_2663506 : CollatzResearch.WordTrace tailWord_2663506 prefixEnd_2663506 1367658804134361254225765 := by
  unfold tailWord_2663506
  simp only [CollatzResearch.WordTrace]
  refine ⟨24286511172145031863554593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64764029792386751636145581 24286511172145031863554593)
  ·
    refine ⟨18214883379108773897665945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24286511172145031863554593 18214883379108773897665945)
    ·
      refine ⟨13661162534331580423249459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18214883379108773897665945 13661162534331580423249459)
      ·
        refine ⟨20491743801497370634874189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13661162534331580423249459 20491743801497370634874189)
        ·
          refine ⟨7684403925561513988077821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20491743801497370634874189 7684403925561513988077821)
          ·
            refine ⟨2881651472085567745529183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7684403925561513988077821 2881651472085567745529183)
            ·
              refine ⟨4322477208128351618293775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881651472085567745529183 4322477208128351618293775)
              ·
                refine ⟨6483715812192527427440663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322477208128351618293775 6483715812192527427440663)
                ·
                  refine ⟨9725573718288791141160995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6483715812192527427440663 9725573718288791141160995)
                  ·
                    refine ⟨14588360577433186711741493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9725573718288791141160995 14588360577433186711741493)
                    ·
                      refine ⟨1367658804134361254225765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14588360577433186711741493 1367658804134361254225765)
                      ·
                        rfl

theorem cell23_2663506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_2663506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663506 prefixEnd_2663506 := by exact prefixLift 2663506
  have htrace : WordTrace (prefixWord ++ tailWord_2663506) baseStart_2663506 baseEnd_2663506 := by
    simpa [prefixWord, tailWord_2663506, baseEnd_2663506] using wordTrace_append hprefix tailTrace_2663506
  have hstable : (prefixWord ++ tailWord_2663506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663506).length < 2 ^ (prefixWord ++ tailWord_2663506).sum := by decide
  have hdescent : baseEnd_2663506 < baseStart_2663506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663536 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 2, 1, 3]
def baseStart_2663536 : Nat := 118140960795 + 2663536 * 2 ^ 59
def prefixEnd_2663536 : Nat := 4983230072969 + 3 ^ 40 * 2663536 * 2
def baseEnd_2663536 : Nat := 1367674208553996136850627

theorem tailTrace_2663536 : CollatzResearch.WordTrace tailWord_2663536 prefixEnd_2663536 1367674208553996136850627 := by
  unfold tailWord_2663536
  simp only [CollatzResearch.WordTrace]
  refine ⟨48573569439235721288905231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64764759252314295051873641 48573569439235721288905231)
  ·
    refine ⟨72860354158853581933357847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48573569439235721288905231 72860354158853581933357847)
    ·
      refine ⟨109290531238280372900036771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72860354158853581933357847 109290531238280372900036771)
      ·
        refine ⟨163935796857420559350055157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109290531238280372900036771 163935796857420559350055157)
        ·
          refine ⟨15368980955383177439067671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163935796857420559350055157 15368980955383177439067671)
          ·
            refine ⟨23053471433074766158601507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15368980955383177439067671 23053471433074766158601507)
            ·
              refine ⟨34580207149612149237902261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23053471433074766158601507 34580207149612149237902261)
              ·
                refine ⟨3241894420276138991053337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34580207149612149237902261 3241894420276138991053337)
                ·
                  refine ⟨2431420815207104243290003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3241894420276138991053337 2431420815207104243290003)
                  ·
                    refine ⟨3647131222810656364935005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2431420815207104243290003 3647131222810656364935005)
                    ·
                      refine ⟨1367674208553996136850627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3647131222810656364935005 1367674208553996136850627)
                      ·
                        rfl

theorem cell23_2663536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2, 1, 3].length) (baseStart_2663536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663536 prefixEnd_2663536 := by exact prefixLift 2663536
  have htrace : WordTrace (prefixWord ++ tailWord_2663536) baseStart_2663536 baseEnd_2663536 := by
    simpa [prefixWord, tailWord_2663536, baseEnd_2663536] using wordTrace_append hprefix tailTrace_2663536
  have hstable : (prefixWord ++ tailWord_2663536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663536).length < 2 ^ (prefixWord ++ tailWord_2663536).sum := by decide
  have hdescent : baseEnd_2663536 < baseStart_2663536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663570 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2663570 : Nat := 118140960795 + 2663570 * 2 ^ 59
def prefixEnd_2663570 : Nat := 4983230072969 + 3 ^ 40 * 2663570 * 2
def baseEnd_2663570 : Nat := 1367691666896249003825471

theorem tailTrace_2663570 : CollatzResearch.WordTrace tailWord_2663570 prefixEnd_2663570 1367691666896249003825471 := by
  unfold tailWord_2663570
  simp only [CollatzResearch.WordTrace]
  refine ⟨24287094740087066596137041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64765585973565510923032109 24287094740087066596137041)
  ·
    refine ⟨18215321055065299947102781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24287094740087066596137041 18215321055065299947102781)
    ·
      refine ⟨6830745395649487480163543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18215321055065299947102781 6830745395649487480163543)
      ·
        refine ⟨10246118093474231220245315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6830745395649487480163543 10246118093474231220245315)
        ·
          refine ⟨15369177140211346830367973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10246118093474231220245315 15369177140211346830367973)
          ·
            refine ⟨2881720713789627530693995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15369177140211346830367973 2881720713789627530693995)
            ·
              refine ⟨4322581070684441296040993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881720713789627530693995 4322581070684441296040993)
              ·
                refine ⟨3241935803013330972030745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4322581070684441296040993 3241935803013330972030745)
                ·
                  refine ⟨2431451852259998229023059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3241935803013330972030745 2431451852259998229023059)
                  ·
                    refine ⟨3647177778389997343534589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2431451852259998229023059 3647177778389997343534589)
                    ·
                      refine ⟨1367691666896249003825471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3647177778389997343534589 1367691666896249003825471)
                      ·
                        rfl

theorem cell23_2663570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2663570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663570 prefixEnd_2663570 := by exact prefixLift 2663570
  have htrace : WordTrace (prefixWord ++ tailWord_2663570) baseStart_2663570 baseEnd_2663570 := by
    simpa [prefixWord, tailWord_2663570, baseEnd_2663570] using wordTrace_append hprefix tailTrace_2663570
  have hstable : (prefixWord ++ tailWord_2663570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663570).length < 2 ^ (prefixWord ++ tailWord_2663570).sum := by decide
  have hdescent : baseEnd_2663570 < baseStart_2663570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663589 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_2663589 : Nat := 118140960795 + 2663589 * 2 ^ 59
def prefixEnd_2663589 : Nat := 4983230072969 + 3 ^ 40 * 2663589 * 2
def baseEnd_2663589 : Nat := 1367701423028684429487883

theorem tailTrace_2663589 : CollatzResearch.WordTrace tailWord_2663589 prefixEnd_2663589 1367701423028684429487883 := by
  unfold tailWord_2663589
  simp only [CollatzResearch.WordTrace]
  refine ⟨97149071947279432629489821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64766047964852955086326547 97149071947279432629489821)
  ·
    refine ⟨36430901980229787236058683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97149071947279432629489821 36430901980229787236058683)
    ·
      refine ⟨54646352970344680854088025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36430901980229787236058683 54646352970344680854088025)
      ·
        refine ⟨40984764727758510640566019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54646352970344680854088025 40984764727758510640566019)
        ·
          refine ⟨61477147091637765960849029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40984764727758510640566019 61477147091637765960849029)
          ·
            refine ⟨11526965079682081117659193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61477147091637765960849029 11526965079682081117659193)
            ·
              refine ⟨8645223809761560838244395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11526965079682081117659193 8645223809761560838244395)
              ·
                refine ⟨12967835714642341257366593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8645223809761560838244395 12967835714642341257366593)
                ·
                  refine ⟨9725876785981755943024945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12967835714642341257366593 9725876785981755943024945)
                  ·
                    refine ⟨7294407589486316957268709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9725876785981755943024945 7294407589486316957268709)
                    ·
                      refine ⟨1367701423028684429487883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7294407589486316957268709 1367701423028684429487883)
                      ·
                        rfl

theorem cell23_2663589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_2663589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663589 prefixEnd_2663589 := by exact prefixLift 2663589
  have htrace : WordTrace (prefixWord ++ tailWord_2663589) baseStart_2663589 baseEnd_2663589 := by
    simpa [prefixWord, tailWord_2663589, baseEnd_2663589] using wordTrace_append hprefix tailTrace_2663589
  have hstable : (prefixWord ++ tailWord_2663589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663589).length < 2 ^ (prefixWord ++ tailWord_2663589).sum := by decide
  have hdescent : baseEnd_2663589 < baseStart_2663589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663632 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_2663632 : Nat := 118140960795 + 2663632 * 2 ^ 59
def prefixEnd_2663632 : Nat := 4983230072969 + 3 ^ 40 * 2663632 * 2
def baseEnd_2663632 : Nat := 1367723502696827761250185

theorem tailTrace_2663632 : CollatzResearch.WordTrace tailWord_2663632 prefixEnd_2663632 1367723502696827761250185 := by
  unfold tailWord_2663632
  simp only [CollatzResearch.WordTrace]
  refine ⟨48575320143061825486652575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64767093524082433982203433 48575320143061825486652575)
  ·
    refine ⟨72862980214592738229978863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48575320143061825486652575 72862980214592738229978863)
    ·
      refine ⟨109294470321889107344968295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72862980214592738229978863 109294470321889107344968295)
      ·
        refine ⟨163941705482833661017452443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109294470321889107344968295 163941705482833661017452443)
        ·
          refine ⟨245912558224250491526178665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163941705482833661017452443 245912558224250491526178665)
          ·
            refine ⟨184434418668187868644633999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245912558224250491526178665 184434418668187868644633999)
            ·
              refine ⟨276651628002281802966950999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184434418668187868644633999 276651628002281802966950999)
              ·
                refine ⟨414977442003422704450426499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276651628002281802966950999 414977442003422704450426499)
                ·
                  refine ⟨622466163005134056675639749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414977442003422704450426499 622466163005134056675639749)
                  ·
                    refine ⟨116712405563462635626682453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 622466163005134056675639749 116712405563462635626682453)
                    ·
                      refine ⟨1367723502696827761250185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 116712405563462635626682453 1367723502696827761250185)
                      ·
                        rfl

theorem cell23_2663632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_2663632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663632 prefixEnd_2663632 := by exact prefixLift 2663632
  have htrace : WordTrace (prefixWord ++ tailWord_2663632) baseStart_2663632 baseEnd_2663632 := by
    simpa [prefixWord, tailWord_2663632, baseEnd_2663632] using wordTrace_append hprefix tailTrace_2663632
  have hstable : (prefixWord ++ tailWord_2663632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663632).length < 2 ^ (prefixWord ++ tailWord_2663632).sum := by decide
  have hdescent : baseEnd_2663632 < baseStart_2663632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663699 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 3]
def baseStart_2663699 : Nat := 118140960795 + 2663699 * 2 ^ 59
def prefixEnd_2663699 : Nat := 4983230072969 + 3 ^ 40 * 2663699 * 2
def baseEnd_2663699 : Nat := 1367757905900678999112377

theorem tailTrace_2663699 : CollatzResearch.WordTrace tailWord_2663699 prefixEnd_2663699 1367757905900678999112377 := by
  unfold tailWord_2663699
  simp only [CollatzResearch.WordTrace]
  refine ⟨97153083976880921415994151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64768722651253947610662767 97153083976880921415994151)
  ·
    refine ⟨145729625965321382123991227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97153083976880921415994151 145729625965321382123991227)
    ·
      refine ⟨218594438947982073185986841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145729625965321382123991227 218594438947982073185986841)
      ·
        refine ⟨163945829210986554889490131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218594438947982073185986841 163945829210986554889490131)
        ·
          refine ⟨245918743816479832334235197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163945829210986554889490131 245918743816479832334235197)
          ·
            refine ⟨92219528931179937125338199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245918743816479832334235197 92219528931179937125338199)
            ·
              refine ⟨138329293396769905688007299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92219528931179937125338199 138329293396769905688007299)
              ·
                refine ⟨207493940095154858532010949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138329293396769905688007299 207493940095154858532010949)
                ·
                  refine ⟨38905113767841535974752053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 207493940095154858532010949 38905113767841535974752053)
                  ·
                    refine ⟨3647354415735143997633005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38905113767841535974752053 3647354415735143997633005)
                    ·
                      refine ⟨1367757905900678999112377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3647354415735143997633005 1367757905900678999112377)
                      ·
                        rfl

theorem cell23_2663699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 3].length) (baseStart_2663699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663699 prefixEnd_2663699 := by exact prefixLift 2663699
  have htrace : WordTrace (prefixWord ++ tailWord_2663699) baseStart_2663699 baseEnd_2663699 := by
    simpa [prefixWord, tailWord_2663699, baseEnd_2663699] using wordTrace_append hprefix tailTrace_2663699
  have hstable : (prefixWord ++ tailWord_2663699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663699).length < 2 ^ (prefixWord ++ tailWord_2663699).sum := by decide
  have hdescent : baseEnd_2663699 < baseStart_2663699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663706 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 6]
def baseStart_2663706 : Nat := 118140960795 + 2663706 * 2 ^ 59
def prefixEnd_2663706 : Nat := 4983230072969 + 3 ^ 40 * 2663706 * 2
def baseEnd_2663706 : Nat := 151973500029473385747205

theorem tailTrace_2663706 : CollatzResearch.WordTrace tailWord_2663706 prefixEnd_2663706 151973500029473385747205 := by
  unfold tailWord_2663706
  simp only [CollatzResearch.WordTrace]
  refine ⟨24288334821963890402874743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64768892858570374407665981 24288334821963890402874743)
  ·
    refine ⟨36432502232945835604312115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24288334821963890402874743 36432502232945835604312115)
    ·
      refine ⟨54648753349418753406468173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36432502232945835604312115 54648753349418753406468173)
      ·
        refine ⟨20493282506032032527425565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54648753349418753406468173 20493282506032032527425565)
        ·
          refine ⟨7684980939762012197784587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20493282506032032527425565 7684980939762012197784587)
          ·
            refine ⟨11527471409643018296676881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7684980939762012197784587 11527471409643018296676881)
            ·
              refine ⟨8645603557232263722507661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11527471409643018296676881 8645603557232263722507661)
              ·
                refine ⟨3242101333962098895940373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8645603557232263722507661 3242101333962098895940373)
                ·
                  refine ⟨151973500029473385747205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3242101333962098895940373 151973500029473385747205)
                  ·
                    rfl

theorem cell23_2663706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_2663706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663706 prefixEnd_2663706 := by exact prefixLift 2663706
  have htrace : WordTrace (prefixWord ++ tailWord_2663706) baseStart_2663706 baseEnd_2663706 := by
    simpa [prefixWord, tailWord_2663706, baseEnd_2663706] using wordTrace_append hprefix tailTrace_2663706
  have hstable : (prefixWord ++ tailWord_2663706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663706).length < 2 ^ (prefixWord ++ tailWord_2663706).sum := by decide
  have hdescent : baseEnd_2663706 < baseStart_2663706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663720 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2663720 : Nat := 118140960795 + 2663720 * 2 ^ 59
def prefixEnd_2663720 : Nat := 4983230072969 + 3 ^ 40 * 2663720 * 2
def baseEnd_2663720 : Nat := 1367768688994423416949781

theorem tailTrace_2663720 : CollatzResearch.WordTrace tailWord_2663720 prefixEnd_2663720 1367768688994423416949781 := by
  unfold tailWord_2663720
  simp only [CollatzResearch.WordTrace]
  refine ⟨48576924954902421001254307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64769233273203228001672409 48576924954902421001254307)
  ·
    refine ⟨72865387432353631501881461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48576924954902421001254307 72865387432353631501881461)
    ·
      refine ⟨6831130071783152953301387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72865387432353631501881461 6831130071783152953301387)
      ·
        refine ⟨10246695107674729429952081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6831130071783152953301387 10246695107674729429952081)
        ·
          refine ⟨7685021330756047072464061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10246695107674729429952081 7685021330756047072464061)
          ·
            refine ⟨2881882999033517652174023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7685021330756047072464061 2881882999033517652174023)
            ·
              refine ⟨4322824498550276478261035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881882999033517652174023 4322824498550276478261035)
              ·
                refine ⟨6484236747825414717391553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322824498550276478261035 6484236747825414717391553)
                ·
                  refine ⟨4863177560869061038043665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6484236747825414717391553 4863177560869061038043665)
                  ·
                    refine ⟨3647383170651795778532749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4863177560869061038043665 3647383170651795778532749)
                    ·
                      refine ⟨1367768688994423416949781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3647383170651795778532749 1367768688994423416949781)
                      ·
                        rfl

theorem cell23_2663720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2663720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663720 prefixEnd_2663720 := by exact prefixLift 2663720
  have htrace : WordTrace (prefixWord ++ tailWord_2663720) baseStart_2663720 baseEnd_2663720 := by
    simpa [prefixWord, tailWord_2663720, baseEnd_2663720] using wordTrace_append hprefix tailTrace_2663720
  have hstable : (prefixWord ++ tailWord_2663720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663720).length < 2 ^ (prefixWord ++ tailWord_2663720).sum := by decide
  have hdescent : baseEnd_2663720 < baseStart_2663720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663749 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_2663749 : Nat := 118140960795 + 2663749 * 2 ^ 59
def prefixEnd_2663749 : Nat := 4983230072969 + 3 ^ 40 * 2663749 * 2
def baseEnd_2663749 : Nat := 455927859977801267829049

theorem tailTrace_2663749 : CollatzResearch.WordTrace tailWord_2663749 prefixEnd_2663749 455927859977801267829049 := by
  unfold tailWord_2663749
  simp only [CollatzResearch.WordTrace]
  refine ⟨97154907626699779955314301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64769938417799853303542867 97154907626699779955314301)
  ·
    refine ⟨36433090360012417483242863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97154907626699779955314301 36433090360012417483242863)
    ·
      refine ⟨54649635540018626224864295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36433090360012417483242863 54649635540018626224864295)
      ·
        refine ⟨81974453310027939337296443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54649635540018626224864295 81974453310027939337296443)
        ·
          refine ⟨122961679965041909005944665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81974453310027939337296443 122961679965041909005944665)
          ·
            refine ⟨92221259973781431754458499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122961679965041909005944665 92221259973781431754458499)
            ·
              refine ⟨138331889960672147631687749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92221259973781431754458499 138331889960672147631687749)
              ·
                refine ⟨25937229367626027680941453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138331889960672147631687749 25937229367626027680941453)
                ·
                  refine ⟨9726461012859760380353045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25937229367626027680941453 9726461012859760380353045)
                  ·
                    refine ⟨455927859977801267829049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9726461012859760380353045 455927859977801267829049)
                    ·
                      rfl

theorem cell23_2663749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_2663749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663749 prefixEnd_2663749 := by exact prefixLift 2663749
  have htrace : WordTrace (prefixWord ++ tailWord_2663749) baseStart_2663749 baseEnd_2663749 := by
    simpa [prefixWord, tailWord_2663749, baseEnd_2663749] using wordTrace_append hprefix tailTrace_2663749
  have hstable : (prefixWord ++ tailWord_2663749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663749).length < 2 ^ (prefixWord ++ tailWord_2663749).sum := by decide
  have hdescent : baseEnd_2663749 < baseStart_2663749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663757 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 6]
def baseStart_2663757 : Nat := 118140960795 + 2663757 * 2 ^ 59
def prefixEnd_2663757 : Nat := 4983230072969 + 3 ^ 40 * 2663757 * 2
def baseEnd_2663757 : Nat := 151976409753182196909679

theorem tailTrace_2663757 : CollatzResearch.WordTrace tailWord_2663757 prefixEnd_2663757 151976409753182196909679 := by
  unfold tailWord_2663757
  simp only [CollatzResearch.WordTrace]
  refine ⟨97155199410670797321605525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64770132940447198214403683 97155199410670797321605525)
  ·
    refine ⟨4554149972375193624450259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97155199410670797321605525 4554149972375193624450259)
    ·
      refine ⟨6831224958562790436675389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4554149972375193624450259 6831224958562790436675389)
      ·
        refine ⟨2561709359461046413753271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6831224958562790436675389 2561709359461046413753271)
        ·
          refine ⟨3842564039191569620629907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561709359461046413753271 3842564039191569620629907)
          ·
            refine ⟨5763846058787354430944861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3842564039191569620629907 5763846058787354430944861)
            ·
              refine ⟨2161442272045257911604323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5763846058787354430944861 2161442272045257911604323)
              ·
                refine ⟨3242163408067886867406485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161442272045257911604323 3242163408067886867406485)
                ·
                  refine ⟨151976409753182196909679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3242163408067886867406485 151976409753182196909679)
                  ·
                    rfl

theorem cell23_2663757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_2663757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663757 prefixEnd_2663757 := by exact prefixLift 2663757
  have htrace : WordTrace (prefixWord ++ tailWord_2663757) baseStart_2663757 baseEnd_2663757 := by
    simpa [prefixWord, tailWord_2663757, baseEnd_2663757] using wordTrace_append hprefix tailTrace_2663757
  have hstable : (prefixWord ++ tailWord_2663757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663757).length < 2 ^ (prefixWord ++ tailWord_2663757).sum := by decide
  have hdescent : baseEnd_2663757 < baseStart_2663757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663784 : List Nat := [2, 1, 4, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_2663784 : Nat := 118140960795 + 2663784 * 2 ^ 59
def prefixEnd_2663784 : Nat := 4983230072969 + 3 ^ 40 * 2663784 * 2
def baseEnd_2663784 : Nat := 1367801551756311166549487

theorem tailTrace_2663784 : CollatzResearch.WordTrace tailWord_2663784 prefixEnd_2663784 1367801551756311166549487 := by
  unfold tailWord_2663784
  simp only [CollatzResearch.WordTrace]
  refine ⟨48578092090786490466419203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64770789454381987288558937 48578092090786490466419203)
  ·
    refine ⟨72867138136179735699628805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48578092090786490466419203 72867138136179735699628805)
    ·
      refine ⟨13662588400533700443680401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72867138136179735699628805 13662588400533700443680401)
      ·
        refine ⟨10246941300400275332760301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13662588400533700443680401 10246941300400275332760301)
        ·
          refine ⟨3842602987650103249785113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10246941300400275332760301 3842602987650103249785113)
          ·
            refine ⟨2881952240737577437338835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3842602987650103249785113 2881952240737577437338835)
            ·
              refine ⟨4322928361106366156008253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881952240737577437338835 4322928361106366156008253)
              ·
                refine ⟨1621098135414887308503095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4322928361106366156008253 1621098135414887308503095)
                ·
                  refine ⟨2431647203122330962754643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621098135414887308503095 2431647203122330962754643)
                  ·
                    refine ⟨3647470804683496444131965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2431647203122330962754643 3647470804683496444131965)
                    ·
                      refine ⟨1367801551756311166549487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3647470804683496444131965 1367801551756311166549487)
                      ·
                        rfl

theorem cell23_2663784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_2663784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663784 prefixEnd_2663784 := by exact prefixLift 2663784
  have htrace : WordTrace (prefixWord ++ tailWord_2663784) baseStart_2663784 baseEnd_2663784 := by
    simpa [prefixWord, tailWord_2663784, baseEnd_2663784] using wordTrace_append hprefix tailTrace_2663784
  have hstable : (prefixWord ++ tailWord_2663784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663784).length < 2 ^ (prefixWord ++ tailWord_2663784).sum := by decide
  have hdescent : baseEnd_2663784 < baseStart_2663784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663793 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 1, 2, 3]
def baseStart_2663793 : Nat := 118140960795 + 2663793 * 2 ^ 59
def prefixEnd_2663793 : Nat := 4983230072969 + 3 ^ 40 * 2663793 * 2
def baseEnd_2663793 : Nat := 1367806173082201631336945

theorem tailTrace_2663793 : CollatzResearch.WordTrace tailWord_2663793 prefixEnd_2663793 1367806173082201631336945 := by
  unfold tailWord_2663793
  simp only [CollatzResearch.WordTrace]
  refine ⟨97156512438540375469916033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64771008292360250313277355 97156512438540375469916033)
  ·
    refine ⟨72867384328905281602437025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97156512438540375469916033 72867384328905281602437025)
    ·
      refine ⟨54650538246678961201827769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72867384328905281602437025 54650538246678961201827769)
      ·
        refine ⟨40987903685009220901370827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54650538246678961201827769 40987903685009220901370827)
        ·
          refine ⟨61481855527513831352056241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40987903685009220901370827 61481855527513831352056241)
          ·
            refine ⟨46111391645635373514042181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61481855527513831352056241 46111391645635373514042181)
            ·
              refine ⟨8645885933556632533882909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46111391645635373514042181 8645885933556632533882909)
              ·
                refine ⟨3242207225083737200206091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8645885933556632533882909 3242207225083737200206091)
                ·
                  refine ⟨4863310837625605800309137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242207225083737200206091 4863310837625605800309137)
                  ·
                    refine ⟨3647483128219204350231853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4863310837625605800309137 3647483128219204350231853)
                    ·
                      refine ⟨1367806173082201631336945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3647483128219204350231853 1367806173082201631336945)
                      ·
                        rfl

theorem cell23_2663793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_2663793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663793 prefixEnd_2663793 := by exact prefixLift 2663793
  have htrace : WordTrace (prefixWord ++ tailWord_2663793) baseStart_2663793 baseEnd_2663793 := by
    simpa [prefixWord, tailWord_2663793, baseEnd_2663793] using wordTrace_append hprefix tailTrace_2663793
  have hstable : (prefixWord ++ tailWord_2663793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663793).length < 2 ^ (prefixWord ++ tailWord_2663793).sum := by decide
  have hdescent : baseEnd_2663793 < baseStart_2663793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663810 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2663810 : Nat := 118140960795 + 2663810 * 2 ^ 59
def prefixEnd_2663810 : Nat := 4983230072969 + 3 ^ 40 * 2663810 * 2
def baseEnd_2663810 : Nat := 1367814902253328064824367

theorem tailTrace_2663810 : CollatzResearch.WordTrace tailWord_2663810 prefixEnd_2663810 1367814902253328064824367 := by
  unfold tailWord_2663810
  simp only [CollatzResearch.WordTrace]
  refine ⟨24289283119869696843321221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64771421652985858248856589 24289283119869696843321221)
  ·
    refine ⟨4554240584975568158122729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24289283119869696843321221 4554240584975568158122729)
    ·
      refine ⟨3415680438731676118592047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4554240584975568158122729 3415680438731676118592047)
      ·
        refine ⟨5123520658097514177888071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3415680438731676118592047 5123520658097514177888071)
        ·
          refine ⟨7685280987146271266832107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5123520658097514177888071 7685280987146271266832107)
          ·
            refine ⟨11527921480719406900248161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7685280987146271266832107 11527921480719406900248161)
            ·
              refine ⟨8645941110539555175186121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11527921480719406900248161 8645941110539555175186121)
              ·
                refine ⟨6484455832904666381389591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8645941110539555175186121 6484455832904666381389591)
                ·
                  refine ⟨9726683749356999572084387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6484455832904666381389591 9726683749356999572084387)
                  ·
                    refine ⟨14590025624035499358126581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9726683749356999572084387 14590025624035499358126581)
                    ·
                      refine ⟨1367814902253328064824367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14590025624035499358126581 1367814902253328064824367)
                      ·
                        rfl

theorem cell23_2663810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2663810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663810 prefixEnd_2663810 := by exact prefixLift 2663810
  have htrace : WordTrace (prefixWord ++ tailWord_2663810) baseStart_2663810 baseEnd_2663810 := by
    simpa [prefixWord, tailWord_2663810, baseEnd_2663810] using wordTrace_append hprefix tailTrace_2663810
  have hstable : (prefixWord ++ tailWord_2663810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663810).length < 2 ^ (prefixWord ++ tailWord_2663810).sum := by decide
  have hdescent : baseEnd_2663810 < baseStart_2663810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663817 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 2, 4]
def baseStart_2663817 : Nat := 118140960795 + 2663817 * 2 ^ 59
def prefixEnd_2663817 : Nat := 4983230072969 + 3 ^ 40 * 2663817 * 2
def baseEnd_2663817 : Nat := 455939498872636512478945

theorem tailTrace_2663817 : CollatzResearch.WordTrace tailWord_2663817 prefixEnd_2663817 455939498872636512478945 := by
  unfold tailWord_2663817
  simp only [CollatzResearch.WordTrace]
  refine ⟨97157387790453427568789705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64771591860302285045859803 97157387790453427568789705)
  ·
    refine ⟨72868040842840070676592279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97157387790453427568789705 72868040842840070676592279)
    ·
      refine ⟨109302061264260106014888419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72868040842840070676592279 109302061264260106014888419)
      ·
        refine ⟨163953091896390159022332629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109302061264260106014888419 163953091896390159022332629)
        ·
          refine ⟨3842650591321644352085921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 163953091896390159022332629 3842650591321644352085921)
          ·
            refine ⟨2881987943491233264064441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3842650591321644352085921 2881987943491233264064441)
            ·
              refine ⟨2161490957618424948048331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2881987943491233264064441 2161490957618424948048331)
              ·
                refine ⟨3242236436427637422072497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161490957618424948048331 3242236436427637422072497)
                ·
                  refine ⟨2431677327320728066554373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3242236436427637422072497 2431677327320728066554373)
                  ·
                    refine ⟨455939498872636512478945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2431677327320728066554373 455939498872636512478945)
                    ·
                      rfl

theorem cell23_2663817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 2, 4].length) (baseStart_2663817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663817 prefixEnd_2663817 := by exact prefixLift 2663817
  have htrace : WordTrace (prefixWord ++ tailWord_2663817) baseStart_2663817 baseEnd_2663817 := by
    simpa [prefixWord, tailWord_2663817, baseEnd_2663817] using wordTrace_append hprefix tailTrace_2663817
  have hstable : (prefixWord ++ tailWord_2663817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663817).length < 2 ^ (prefixWord ++ tailWord_2663817).sum := by decide
  have hdescent : baseEnd_2663817 < baseStart_2663817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663863 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 3, 4, 2]
def baseStart_2663863 : Nat := 118140960795 + 2663863 * 2 ^ 59
def prefixEnd_2663863 : Nat := 4983230072969 + 3 ^ 40 * 2663863 * 2
def baseEnd_2663863 : Nat := 1367842116728016357461623

theorem tailTrace_2663863 : CollatzResearch.WordTrace tailWord_2663863 prefixEnd_2663863 1367842116728016357461623 := by
  unfold tailWord_2663863
  simp only [CollatzResearch.WordTrace]
  refine ⟨97159065548286777424964243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64772710365524518283309495 97159065548286777424964243)
  ·
    refine ⟨145738598322430166137446365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97159065548286777424964243 145738598322430166137446365)
    ·
      refine ⟨54651974370911312301542387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145738598322430166137446365 54651974370911312301542387)
      ·
        refine ⟨81977961556366968452313581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54651974370911312301542387 81977961556366968452313581)
        ·
          refine ⟨30741735583637613169617593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81977961556366968452313581 30741735583637613169617593)
          ·
            refine ⟨23056301687728209877213195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30741735583637613169617593 23056301687728209877213195)
            ·
              refine ⟨34584452531592314815819793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23056301687728209877213195 34584452531592314815819793)
              ·
                refine ⟨25938339398694236111864845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34584452531592314815819793 25938339398694236111864845)
                ·
                  refine ⟨9726877274510338541949317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25938339398694236111864845 9726877274510338541949317)
                  ·
                    refine ⟨1823789488970688476615497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9726877274510338541949317 1823789488970688476615497)
                    ·
                      refine ⟨1367842116728016357461623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823789488970688476615497 1367842116728016357461623)
                      ·
                        rfl

theorem cell23_2663863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_2663863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663863 prefixEnd_2663863 := by exact prefixLift 2663863
  have htrace : WordTrace (prefixWord ++ tailWord_2663863) baseStart_2663863 baseEnd_2663863 := by
    simpa [prefixWord, tailWord_2663863, baseEnd_2663863] using wordTrace_append hprefix tailTrace_2663863
  have hstable : (prefixWord ++ tailWord_2663863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663863).length < 2 ^ (prefixWord ++ tailWord_2663863).sum := by decide
  have hdescent : baseEnd_2663863 < baseStart_2663863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663880 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 1, 4, 2]
def baseStart_2663880 : Nat := 118140960795 + 2663880 * 2 ^ 59
def prefixEnd_2663880 : Nat := 4983230072969 + 3 ^ 40 * 2663880 * 2
def baseEnd_2663880 : Nat := 1367850845899142790949045

theorem tailTrace_2663880 : CollatzResearch.WordTrace tailWord_2663880 prefixEnd_2663880 1367850845899142790949045 := by
  unfold tailWord_2663880
  simp only [CollatzResearch.WordTrace]
  refine ⟨48579842794612594664166547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64773123726150126218888729 48579842794612594664166547)
  ·
    refine ⟨72869764191918891996249821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48579842794612594664166547 72869764191918891996249821)
    ·
      refine ⟨27326161571969584498593683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72869764191918891996249821 27326161571969584498593683)
      ·
        refine ⟨40989242357954376747890525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27326161571969584498593683 40989242357954376747890525)
        ·
          refine ⟨15370965884232891280458947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40989242357954376747890525 15370965884232891280458947)
          ·
            refine ⟨23056448826349336920688421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15370965884232891280458947 23056448826349336920688421)
            ·
              refine ⟨4323084154940500672629079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23056448826349336920688421 4323084154940500672629079)
              ·
                refine ⟨6484626232410751008943619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4323084154940500672629079 6484626232410751008943619)
                ·
                  refine ⟨9726939348616126513415429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6484626232410751008943619 9726939348616126513415429)
                  ·
                    refine ⟨1823801127865523721265393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9726939348616126513415429 1823801127865523721265393)
                    ·
                      refine ⟨1367850845899142790949045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823801127865523721265393 1367850845899142790949045)
                      ·
                        rfl

theorem cell23_2663880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_2663880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663880 prefixEnd_2663880 := by exact prefixLift 2663880
  have htrace : WordTrace (prefixWord ++ tailWord_2663880) baseStart_2663880 baseEnd_2663880 := by
    simpa [prefixWord, tailWord_2663880, baseEnd_2663880] using wordTrace_append hprefix tailTrace_2663880
  have hstable : (prefixWord ++ tailWord_2663880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663880).length < 2 ^ (prefixWord ++ tailWord_2663880).sum := by decide
  have hdescent : baseEnd_2663880 < baseStart_2663880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663886 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_2663886 : Nat := 118140960795 + 2663886 * 2 ^ 59
def prefixEnd_2663886 : Nat := 4983230072969 + 3 ^ 40 * 2663886 * 2
def baseEnd_2663886 : Nat := 151983769642563307497113

theorem tailTrace_2663886 : CollatzResearch.WordTrace tailWord_2663886 prefixEnd_2663886 151983769642563307497113 := by
  unfold tailWord_2663886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12144988053400431544131439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64773269618135634902034341 12144988053400431544131439)
  ·
    refine ⟨18217482080100647316197159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12144988053400431544131439 18217482080100647316197159)
    ·
      refine ⟨27326223120150970974295739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18217482080100647316197159 27326223120150970974295739)
      ·
        refine ⟨40989334680226456461443609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27326223120150970974295739 40989334680226456461443609)
        ·
          refine ⟨30742001010169842346082707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40989334680226456461443609 30742001010169842346082707)
          ·
            refine ⟨46113001515254763519124061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30742001010169842346082707 46113001515254763519124061)
            ·
              refine ⟨17292375568220536319671523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46113001515254763519124061 17292375568220536319671523)
              ·
                refine ⟨25938563352330804479507285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17292375568220536319671523 25938563352330804479507285)
                ·
                  refine ⟨151983769642563307497113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25938563352330804479507285 151983769642563307497113)
                  ·
                    rfl

theorem cell23_2663886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_2663886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663886 prefixEnd_2663886 := by exact prefixLift 2663886
  have htrace : WordTrace (prefixWord ++ tailWord_2663886) baseStart_2663886 baseEnd_2663886 := by
    simpa [prefixWord, tailWord_2663886, baseEnd_2663886] using wordTrace_append hprefix tailTrace_2663886
  have hstable : (prefixWord ++ tailWord_2663886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663886).length < 2 ^ (prefixWord ++ tailWord_2663886).sum := by decide
  have hdescent : baseEnd_2663886 < baseStart_2663886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663923 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 2, 5, 2]
def baseStart_2663923 : Nat := 118140960795 + 2663923 * 2 ^ 59
def prefixEnd_2663923 : Nat := 4983230072969 + 3 ^ 40 * 2663923 * 2
def baseEnd_2663923 : Nat := 1367872925567286122711347

theorem tailTrace_2663923 : CollatzResearch.WordTrace tailWord_2663923 prefixEnd_2663923 1367872925567286122711347 := by
  unfold tailWord_2663923
  simp only [CollatzResearch.WordTrace]
  refine ⟨97161253928069407672148423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64774169285379605114765615 97161253928069407672148423)
  ·
    refine ⟨145741880892104111508222635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97161253928069407672148423 145741880892104111508222635)
    ·
      refine ⟨218612821338156167262333953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145741880892104111508222635 218612821338156167262333953)
      ·
        refine ⟨163959616003617125446750465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218612821338156167262333953 163959616003617125446750465)
        ·
          refine ⟨122969712002712844085062849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163959616003617125446750465 122969712002712844085062849)
          ·
            refine ⟨92227284002034633063797137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122969712002712844085062849 92227284002034633063797137)
            ·
              refine ⟨69170463001525974797847853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92227284002034633063797137 69170463001525974797847853)
              ·
                refine ⟨25938923625572240549192945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69170463001525974797847853 25938923625572240549192945)
                ·
                  refine ⟨19454192719179180411894709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25938923625572240549192945 19454192719179180411894709)
                  ·
                    refine ⟨1823830567423048163615129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19454192719179180411894709 1823830567423048163615129)
                    ·
                      refine ⟨1367872925567286122711347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823830567423048163615129 1367872925567286122711347)
                      ·
                        rfl

theorem cell23_2663923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 5, 2].length) (baseStart_2663923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663923 prefixEnd_2663923 := by exact prefixLift 2663923
  have htrace : WordTrace (prefixWord ++ tailWord_2663923) baseStart_2663923 baseEnd_2663923 := by
    simpa [prefixWord, tailWord_2663923, baseEnd_2663923] using wordTrace_append hprefix tailTrace_2663923
  have hstable : (prefixWord ++ tailWord_2663923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663923).length < 2 ^ (prefixWord ++ tailWord_2663923).sum := by decide
  have hdescent : baseEnd_2663923 < baseStart_2663923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663953 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_2663953 : Nat := 118140960795 + 2663953 * 2 ^ 59
def prefixEnd_2663953 : Nat := 4983230072969 + 3 ^ 40 * 2663953 * 2
def baseEnd_2663953 : Nat := 1367888329986921005336209

theorem tailTrace_2663953 : CollatzResearch.WordTrace tailWord_2663953 prefixEnd_2663953 1367888329986921005336209 := by
  unfold tailWord_2663953
  simp only [CollatzResearch.WordTrace]
  refine ⟨97162348117960722795740513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64774898745307148530493675 97162348117960722795740513)
  ·
    refine ⟨72871761088470542096805385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97162348117960722795740513 72871761088470542096805385)
    ·
      refine ⟨54653820816352906572604039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72871761088470542096805385 54653820816352906572604039)
      ·
        refine ⟨81980731224529359858906059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54653820816352906572604039 81980731224529359858906059)
        ·
          refine ⟨122971096836794039788359089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81980731224529359858906059 122971096836794039788359089)
          ·
            refine ⟨92228322627595529841269317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122971096836794039788359089 92228322627595529841269317)
            ·
              refine ⟨17292810492674161845237997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92228322627595529841269317 17292810492674161845237997)
              ·
                refine ⟨6484803934752810691964249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17292810492674161845237997 6484803934752810691964249)
                ·
                  refine ⟨4863602951064608018973187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6484803934752810691964249 4863602951064608018973187)
                  ·
                    refine ⟨7295404426596912028459781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4863602951064608018973187 7295404426596912028459781)
                    ·
                      refine ⟨1367888329986921005336209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7295404426596912028459781 1367888329986921005336209)
                      ·
                        rfl

theorem cell23_2663953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_2663953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663953 prefixEnd_2663953 := by exact prefixLift 2663953
  have htrace : WordTrace (prefixWord ++ tailWord_2663953) baseStart_2663953 baseEnd_2663953 := by
    simpa [prefixWord, tailWord_2663953, baseEnd_2663953] using wordTrace_append hprefix tailTrace_2663953
  have hstable : (prefixWord ++ tailWord_2663953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663953).length < 2 ^ (prefixWord ++ tailWord_2663953).sum := by decide
  have hdescent : baseEnd_2663953 < baseStart_2663953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2663970 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_2663970 : Nat := 118140960795 + 2663970 * 2 ^ 59
def prefixEnd_2663970 : Nat := 4983230072969 + 3 ^ 40 * 2663970 * 2
def baseEnd_2663970 : Nat := 1367897059158047438823631

theorem tailTrace_2663970 : CollatzResearch.WordTrace tailWord_2663970 prefixEnd_2663970 1367897059158047438823631 := by
  unfold tailWord_2663970
  simp only [CollatzResearch.WordTrace]
  refine ⟨24290742039724783674777341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64775312105932756466072909 24290742039724783674777341)
  ·
    refine ⟨9109028264896793878041503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24290742039724783674777341 9109028264896793878041503)
    ·
      refine ⟨13663542397345190817062255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9109028264896793878041503 13663542397345190817062255)
      ·
        refine ⟨20495313596017786225593383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13663542397345190817062255 20495313596017786225593383)
        ·
          refine ⟨30742970394026679338390075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20495313596017786225593383 30742970394026679338390075)
          ·
            refine ⟨46114455591040019007585113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30742970394026679338390075 46114455591040019007585113)
            ·
              refine ⟨34585841693280014255688835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46114455591040019007585113 34585841693280014255688835)
              ·
                refine ⟨51878762539920021383533253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34585841693280014255688835 51878762539920021383533253)
                ·
                  refine ⟨9727267976235004009412485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51878762539920021383533253 9727267976235004009412485)
                  ·
                    refine ⟨1823862745544063251764841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9727267976235004009412485 1823862745544063251764841)
                    ·
                      refine ⟨1367897059158047438823631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823862745544063251764841 1367897059158047438823631)
                      ·
                        rfl

theorem cell23_2663970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_2663970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2663970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2663970 prefixEnd_2663970 := by exact prefixLift 2663970
  have htrace : WordTrace (prefixWord ++ tailWord_2663970) baseStart_2663970 baseEnd_2663970 := by
    simpa [prefixWord, tailWord_2663970, baseEnd_2663970] using wordTrace_append hprefix tailTrace_2663970
  have hstable : (prefixWord ++ tailWord_2663970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2663970).length < 2 ^ (prefixWord ++ tailWord_2663970).sum := by decide
  have hdescent : baseEnd_2663970 < baseStart_2663970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2663970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664007 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_2664007 : Nat := 118140960795 + 2664007 * 2 ^ 59
def prefixEnd_2664007 : Nat := 4983230072969 + 3 ^ 40 * 2664007 * 2
def baseEnd_2664007 : Nat := 1367916057942263794060961

theorem tailTrace_2664007 : CollatzResearch.WordTrace tailWord_2664007 prefixEnd_2664007 1367916057942263794060961 := by
  unfold tailWord_2664007
  simp only [CollatzResearch.WordTrace]
  refine ⟨97164317659765090018206275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64776211773176726678804183 97164317659765090018206275)
  ·
    refine ⟨145746476489647635027309413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97164317659765090018206275 145746476489647635027309413)
    ·
      refine ⟨27327464341808931567620515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145746476489647635027309413 27327464341808931567620515)
      ·
        refine ⟨40991196512713397351430773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27327464341808931567620515 40991196512713397351430773)
        ·
          refine ⟨3842924673066881001696635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40991196512713397351430773 3842924673066881001696635)
          ·
            refine ⟨5764387009600321502544953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3842924673066881001696635 5764387009600321502544953)
            ·
              refine ⟨4323290257200241126908715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5764387009600321502544953 4323290257200241126908715)
              ·
                refine ⟨6484935385800361690363073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4323290257200241126908715 6484935385800361690363073)
                ·
                  refine ⟨4863701539350271267772305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6484935385800361690363073 4863701539350271267772305)
                  ·
                    refine ⟨3647776154512703450829229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4863701539350271267772305 3647776154512703450829229)
                    ·
                      refine ⟨1367916057942263794060961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3647776154512703450829229 1367916057942263794060961)
                      ·
                        rfl

theorem cell23_2664007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_2664007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664007 prefixEnd_2664007 := by exact prefixLift 2664007
  have htrace : WordTrace (prefixWord ++ tailWord_2664007) baseStart_2664007 baseEnd_2664007 := by
    simpa [prefixWord, tailWord_2664007, baseEnd_2664007] using wordTrace_append hprefix tailTrace_2664007
  have hstable : (prefixWord ++ tailWord_2664007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664007).length < 2 ^ (prefixWord ++ tailWord_2664007).sum := by decide
  have hdescent : baseEnd_2664007 < baseStart_2664007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664040 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2664040 : Nat := 118140960795 + 2664040 * 2 ^ 59
def prefixEnd_2664040 : Nat := 4983230072969 + 3 ^ 40 * 2664040 * 2
def baseEnd_2664040 : Nat := 455977667601287388316103

theorem tailTrace_2664040 : CollatzResearch.WordTrace tailWord_2664040 prefixEnd_2664040 455977667601287388316103 := by
  unfold tailWord_2664040
  simp only [CollatzResearch.WordTrace]
  refine ⟨48582760634322768327078787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64777014179097024436105049 48582760634322768327078787)
  ·
    refine ⟨72874140951484152490618181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48582760634322768327078787 72874140951484152490618181)
    ·
      refine ⟨13663901428403278591990909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72874140951484152490618181 13663901428403278591990909)
      ·
        refine ⟨5123963035651229471996591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13663901428403278591990909 5123963035651229471996591)
        ·
          refine ⟨7685944553476844207994887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5123963035651229471996591 7685944553476844207994887)
          ·
            refine ⟨11528916830215266311992331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7685944553476844207994887 11528916830215266311992331)
            ·
              refine ⟨17293375245322899467988497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11528916830215266311992331 17293375245322899467988497)
              ·
                refine ⟨12970031433992174600991373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17293375245322899467988497 12970031433992174600991373)
                ·
                  refine ⟨4863761787747065475371765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12970031433992174600991373 4863761787747065475371765)
                  ·
                    refine ⟨455977667601287388316103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4863761787747065475371765 455977667601287388316103)
                    ·
                      rfl

theorem cell23_2664040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2664040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664040 prefixEnd_2664040 := by exact prefixLift 2664040
  have htrace : WordTrace (prefixWord ++ tailWord_2664040) baseStart_2664040 baseEnd_2664040 := by
    simpa [prefixWord, tailWord_2664040, baseEnd_2664040] using wordTrace_append hprefix tailTrace_2664040
  have hstable : (prefixWord ++ tailWord_2664040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664040).length < 2 ^ (prefixWord ++ tailWord_2664040).sum := by decide
  have hdescent : baseEnd_2664040 < baseStart_2664040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664054 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2664054 : Nat := 118140960795 + 2664054 * 2 ^ 59
def prefixEnd_2664054 : Nat := 4983230072969 + 3 ^ 40 * 2664054 * 2
def baseEnd_2664054 : Nat := 1367940191533025110173245

theorem tailTrace_2664054 : CollatzResearch.WordTrace tailWord_2664054 prefixEnd_2664054 1367940191533025110173245 := by
  unfold tailWord_2664054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6072876993162176065322951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64777354593729878030111477 6072876993162176065322951)
  ·
    refine ⟨9109315489743264097984427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6072876993162176065322951 9109315489743264097984427)
    ·
      refine ⟨13663973234614896146976641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9109315489743264097984427 13663973234614896146976641)
      ·
        refine ⟨10247979925961172110232481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13663973234614896146976641 10247979925961172110232481)
        ·
          refine ⟨7685984944470879082674361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10247979925961172110232481 7685984944470879082674361)
          ·
            refine ⟨5764488708353159312005771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7685984944470879082674361 5764488708353159312005771)
            ·
              refine ⟨8646733062529738968008657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5764488708353159312005771 8646733062529738968008657)
              ·
                refine ⟨6485049796897304226006493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8646733062529738968008657 6485049796897304226006493)
                ·
                  refine ⟨2431893673836489084752435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6485049796897304226006493 2431893673836489084752435)
                  ·
                    refine ⟨3647840510754733627128653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2431893673836489084752435 3647840510754733627128653)
                    ·
                      refine ⟨1367940191533025110173245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3647840510754733627128653 1367940191533025110173245)
                      ·
                        rfl

theorem cell23_2664054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2664054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664054 prefixEnd_2664054 := by exact prefixLift 2664054
  have htrace : WordTrace (prefixWord ++ tailWord_2664054) baseStart_2664054 baseEnd_2664054 := by
    simpa [prefixWord, tailWord_2664054, baseEnd_2664054] using wordTrace_append hprefix tailTrace_2664054
  have hstable : (prefixWord ++ tailWord_2664054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664054).length < 2 ^ (prefixWord ++ tailWord_2664054).sum := by decide
  have hdescent : baseEnd_2664054 < baseStart_2664054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664060 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_2664060 : Nat := 118140960795 + 2664060 * 2 ^ 59
def prefixEnd_2664060 : Nat := 4983230072969 + 3 ^ 40 * 2664060 * 2
def baseEnd_2664060 : Nat := 1367943272416952086698217

theorem tailTrace_2664060 : CollatzResearch.WordTrace tailWord_2664060 prefixEnd_2664060 1367943272416952086698217 := by
  unfold tailWord_2664060
  simp only [CollatzResearch.WordTrace]
  refine ⟨48583125364286540034942817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64777500485715386713257089 48583125364286540034942817)
  ·
    refine ⟨36437344023214905026207113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48583125364286540034942817 36437344023214905026207113)
    ·
      refine ⟨27328008017411178769655335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36437344023214905026207113 27328008017411178769655335)
      ·
        refine ⟨40992012026116768154483003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27328008017411178769655335 40992012026116768154483003)
        ·
          refine ⟨61488018039175152231724505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40992012026116768154483003 61488018039175152231724505)
          ·
            refine ⟨46116013529381364173793379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61488018039175152231724505 46116013529381364173793379)
            ·
              refine ⟨69174020294072046260690069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46116013529381364173793379 69174020294072046260690069)
              ·
                refine ⟨3242532201284627168469847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69174020294072046260690069 3242532201284627168469847)
                ·
                  refine ⟨4863798301926940752704771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242532201284627168469847 4863798301926940752704771)
                  ·
                    refine ⟨7295697452890411129057157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4863798301926940752704771 7295697452890411129057157)
                    ·
                      refine ⟨1367943272416952086698217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7295697452890411129057157 1367943272416952086698217)
                      ·
                        rfl

theorem cell23_2664060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_2664060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664060 prefixEnd_2664060 := by exact prefixLift 2664060
  have htrace : WordTrace (prefixWord ++ tailWord_2664060) baseStart_2664060 baseEnd_2664060 := by
    simpa [prefixWord, tailWord_2664060, baseEnd_2664060] using wordTrace_append hprefix tailTrace_2664060
  have hstable : (prefixWord ++ tailWord_2664060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664060).length < 2 ^ (prefixWord ++ tailWord_2664060).sum := by decide
  have hdescent : baseEnd_2664060 < baseStart_2664060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664074 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 1, 5]
def baseStart_2664074 : Nat := 118140960795 + 2664074 * 2 ^ 59
def prefixEnd_2664074 : Nat := 4983230072969 + 3 ^ 40 * 2664074 * 2
def baseEnd_2664074 : Nat := 455983487048705010641051

theorem tailTrace_2664074 : CollatzResearch.WordTrace tailWord_2664074 prefixEnd_2664074 455983487048705010641051 := by
  unfold tailWord_2664074
  simp only [CollatzResearch.WordTrace]
  refine ⟨24291690337630590115223819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64777840900348240307263517 24291690337630590115223819)
  ·
    refine ⟨36437535506445885172835729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24291690337630590115223819 36437535506445885172835729)
    ·
      refine ⟨27328151629834413879626797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36437535506445885172835729 27328151629834413879626797)
      ·
        refine ⟨10248056861187905204860049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27328151629834413879626797 10248056861187905204860049)
        ·
          refine ⟨7686042645890928903645037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10248056861187905204860049 7686042645890928903645037)
          ·
            refine ⟨2882265992209098338866889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7686042645890928903645037 2882265992209098338866889)
            ·
              refine ⟨2161699494156823754150167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2882265992209098338866889 2161699494156823754150167)
              ·
                refine ⟨3242549241235235631225251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161699494156823754150167 3242549241235235631225251)
                ·
                  refine ⟨4863823861852853446837877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242549241235235631225251 4863823861852853446837877)
                  ·
                    refine ⟨455983487048705010641051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4863823861852853446837877 455983487048705010641051)
                    ·
                      rfl

theorem cell23_2664074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_2664074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664074 prefixEnd_2664074 := by exact prefixLift 2664074
  have htrace : WordTrace (prefixWord ++ tailWord_2664074) baseStart_2664074 baseEnd_2664074 := by
    simpa [prefixWord, tailWord_2664074, baseEnd_2664074] using wordTrace_append hprefix tailTrace_2664074
  have hstable : (prefixWord ++ tailWord_2664074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664074).length < 2 ^ (prefixWord ++ tailWord_2664074).sum := by decide
  have hdescent : baseEnd_2664074 < baseStart_2664074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664087 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 2, 4]
def baseStart_2664087 : Nat := 118140960795 + 2664087 * 2 ^ 59
def prefixEnd_2664087 : Nat := 4983230072969 + 3 ^ 40 * 2664087 * 2
def baseEnd_2664087 : Nat := 455985712131541160353531

theorem tailTrace_2664087 : CollatzResearch.WordTrace tailWord_2664087 prefixEnd_2664087 455985712131541160353531 := by
  unfold tailWord_2664087
  simp only [CollatzResearch.WordTrace]
  refine ⟨97167235499475263681118515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64778156999650175787412343 97167235499475263681118515)
  ·
    refine ⟨145750853249212895521677773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97167235499475263681118515 145750853249212895521677773)
    ·
      refine ⟨54656569968454835820629165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145750853249212895521677773 54656569968454835820629165)
      ·
        refine ⟨20496213738170563432735937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54656569968454835820629165 20496213738170563432735937)
        ·
          refine ⟨15372160303627922574551953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20496213738170563432735937 15372160303627922574551953)
          ·
            refine ⟨11529120227720941930913965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15372160303627922574551953 11529120227720941930913965)
            ·
              refine ⟨4323420085395353224092737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11529120227720941930913965 4323420085395353224092737)
              ·
                refine ⟨3242565064046514918069553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4323420085395353224092737 3242565064046514918069553)
                ·
                  refine ⟨2431923798034886188552165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3242565064046514918069553 2431923798034886188552165)
                  ·
                    refine ⟨455985712131541160353531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2431923798034886188552165 455985712131541160353531)
                    ·
                      rfl

theorem cell23_2664087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_2664087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664087 prefixEnd_2664087 := by exact prefixLift 2664087
  have htrace : WordTrace (prefixWord ++ tailWord_2664087) baseStart_2664087 baseEnd_2664087 := by
    simpa [prefixWord, tailWord_2664087, baseEnd_2664087] using wordTrace_append hprefix tailTrace_2664087
  have hstable : (prefixWord ++ tailWord_2664087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664087).length < 2 ^ (prefixWord ++ tailWord_2664087).sum := by decide
  have hdescent : baseEnd_2664087 < baseStart_2664087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664093 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2664093 : Nat := 118140960795 + 2664093 * 2 ^ 59
def prefixEnd_2664093 : Nat := 4983230072969 + 3 ^ 40 * 2664093 * 2
def baseEnd_2664093 : Nat := 1367960217278550457585565

theorem tailTrace_2664093 : CollatzResearch.WordTrace tailWord_2664093 prefixEnd_2664093 1367960217278550457585565 := by
  unfold tailWord_2664093
  simp only [CollatzResearch.WordTrace]
  refine ⟨97167454337453526705836933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64778302891635684470557955 97167454337453526705836933)
  ·
    refine ⟨18218897688272536257344425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97167454337453526705836933 18218897688272536257344425)
    ·
      refine ⟨13664173266204402193008319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18218897688272536257344425 13664173266204402193008319)
      ·
        refine ⟨20496259899306603289512479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13664173266204402193008319 20496259899306603289512479)
        ·
          refine ⟨30744389848959904934268719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20496259899306603289512479 30744389848959904934268719)
          ·
            refine ⟨46116584773439857401403079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30744389848959904934268719 46116584773439857401403079)
            ·
              refine ⟨69174877160159786102104619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46116584773439857401403079 69174877160159786102104619)
              ·
                refine ⟨103762315740239679153156929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69174877160159786102104619 103762315740239679153156929)
                ·
                  refine ⟨77821736805179759364867697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103762315740239679153156929 77821736805179759364867697)
                  ·
                    refine ⟨58366302603884819523650773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77821736805179759364867697 58366302603884819523650773)
                    ·
                      refine ⟨1367960217278550457585565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58366302603884819523650773 1367960217278550457585565)
                      ·
                        rfl

theorem cell23_2664093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2664093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664093 prefixEnd_2664093 := by exact prefixLift 2664093
  have htrace : WordTrace (prefixWord ++ tailWord_2664093) baseStart_2664093 baseEnd_2664093 := by
    simpa [prefixWord, tailWord_2664093, baseEnd_2664093] using wordTrace_append hprefix tailTrace_2664093
  have hstable : (prefixWord ++ tailWord_2664093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664093).length < 2 ^ (prefixWord ++ tailWord_2664093).sum := by decide
  have hdescent : baseEnd_2664093 < baseStart_2664093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664120 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 2, 7, 2]
def baseStart_2664120 : Nat := 118140960795 + 2664120 * 2 ^ 59
def prefixEnd_2664120 : Nat := 4983230072969 + 3 ^ 40 * 2664120 * 2
def baseEnd_2664120 : Nat := 1367974081256221851947941

theorem tailTrace_2664120 : CollatzResearch.WordTrace tailWord_2664120 prefixEnd_2664120 1367974081256221851947941 := by
  unfold tailWord_2664120
  simp only [CollatzResearch.WordTrace]
  refine ⟨48584219554177855158534907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64778959405570473544713209 48584219554177855158534907)
  ·
    refine ⟨72876329331266782737802361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48584219554177855158534907 72876329331266782737802361)
    ·
      refine ⟨54657246998450087053351771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72876329331266782737802361 54657246998450087053351771)
      ·
        refine ⟨81985870497675130580027657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54657246998450087053351771 81985870497675130580027657)
        ·
          refine ⟨61489402873256347935020743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81985870497675130580027657 61489402873256347935020743)
          ·
            refine ⟨92234104309884521902531115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61489402873256347935020743 92234104309884521902531115)
            ·
              refine ⟨138351156464826782853796673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92234104309884521902531115 138351156464826782853796673)
              ·
                refine ⟨103763367348620087140347505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138351156464826782853796673 103763367348620087140347505)
                ·
                  refine ⟨77822525511465065355260629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103763367348620087140347505 77822525511465065355260629)
                  ·
                    refine ⟨1823965441674962469263921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 77822525511465065355260629 1823965441674962469263921)
                    ·
                      refine ⟨1367974081256221851947941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1823965441674962469263921 1367974081256221851947941)
                      ·
                        rfl

theorem cell23_2664120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_2664120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664120 prefixEnd_2664120 := by exact prefixLift 2664120
  have htrace : WordTrace (prefixWord ++ tailWord_2664120) baseStart_2664120 baseEnd_2664120 := by
    simpa [prefixWord, tailWord_2664120, baseEnd_2664120] using wordTrace_append hprefix tailTrace_2664120
  have hstable : (prefixWord ++ tailWord_2664120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664120).length < 2 ^ (prefixWord ++ tailWord_2664120).sum := by decide
  have hdescent : baseEnd_2664120 < baseStart_2664120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664134 : List Nat := [6, 1, 2, 1, 1, 3, 9]
def baseStart_2664134 : Nat := 118140960795 + 2664134 * 2 ^ 59
def prefixEnd_2664134 : Nat := 4983230072969 + 3 ^ 40 * 2664134 * 2
def baseEnd_2664134 : Nat := 16888657654140553051517

theorem tailTrace_2664134 : CollatzResearch.WordTrace tailWord_2664134 prefixEnd_2664134 16888657654140553051517 := by
  unfold tailWord_2664134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036529679072030959627483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64779299820203327138719637 3036529679072030959627483)
  ·
    refine ⟨4554794518608046439441225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3036529679072030959627483 4554794518608046439441225)
    ·
      refine ⟨3416095888956034829580919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4554794518608046439441225 3416095888956034829580919)
      ·
        refine ⟨5124143833434052244371379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3416095888956034829580919 5124143833434052244371379)
        ·
          refine ⟨7686215750151078366557069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124143833434052244371379 7686215750151078366557069)
          ·
            refine ⟨2882330906306654387458901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7686215750151078366557069 2882330906306654387458901)
            ·
              refine ⟨16888657654140553051517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2882330906306654387458901 16888657654140553051517)
              ·
                rfl

theorem cell23_2664134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 9].length) (baseStart_2664134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664134 prefixEnd_2664134 := by exact prefixLift 2664134
  have htrace : WordTrace (prefixWord ++ tailWord_2664134) baseStart_2664134 baseEnd_2664134 := by
    simpa [prefixWord, tailWord_2664134, baseEnd_2664134] using wordTrace_append hprefix tailTrace_2664134
  have hstable : (prefixWord ++ tailWord_2664134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664134).length < 2 ^ (prefixWord ++ tailWord_2664134).sum := by decide
  have hdescent : baseEnd_2664134 < baseStart_2664134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664143 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 4, 6]
def baseStart_2664143 : Nat := 118140960795 + 2664143 * 2 ^ 59
def prefixEnd_2664143 : Nat := 4983230072969 + 3 ^ 40 * 2664143 * 2
def baseEnd_2664143 : Nat := 455995297103758420653445

theorem tailTrace_2664143 : CollatzResearch.WordTrace tailWord_2664143 prefixEnd_2664143 455995297103758420653445 := by
  unfold tailWord_2664143
  simp only [CollatzResearch.WordTrace]
  refine ⟨97169277987272385245157083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64779518658181590163438055 97169277987272385245157083)
  ·
    refine ⟨145753916980908577867735625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97169277987272385245157083 145753916980908577867735625)
    ·
      refine ⟨109315437735681433400801719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145753916980908577867735625 109315437735681433400801719)
      ·
        refine ⟨163973156603522150101202579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109315437735681433400801719 163973156603522150101202579)
        ·
          refine ⟨245959734905283225151803869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163973156603522150101202579 245959734905283225151803869)
          ·
            refine ⟨92234900589481209431926451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245959734905283225151803869 92234900589481209431926451)
            ·
              refine ⟨138352350884221814147889677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92234900589481209431926451 138352350884221814147889677)
              ·
                refine ⟨51882131581583180305458629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138352350884221814147889677 51882131581583180305458629)
                ·
                  refine ⟨9727899671546846307273493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51882131581583180305458629 9727899671546846307273493)
                  ·
                    refine ⟨455995297103758420653445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9727899671546846307273493 455995297103758420653445)
                    ·
                      rfl

theorem cell23_2664143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_2664143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664143 prefixEnd_2664143 := by exact prefixLift 2664143
  have htrace : WordTrace (prefixWord ++ tailWord_2664143) baseStart_2664143 baseEnd_2664143 := by
    simpa [prefixWord, tailWord_2664143, baseEnd_2664143] using wordTrace_append hprefix tailTrace_2664143
  have hstable : (prefixWord ++ tailWord_2664143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664143).length < 2 ^ (prefixWord ++ tailWord_2664143).sum := by decide
  have hdescent : baseEnd_2664143 < baseStart_2664143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664170 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_2664170 : Nat := 118140960795 + 2664170 * 2 ^ 59
def prefixEnd_2664170 : Nat := 4983230072969 + 3 ^ 40 * 2664170 * 2
def baseEnd_2664170 : Nat := 1367999755288946656322711

theorem tailTrace_2664170 : CollatzResearch.WordTrace tailWord_2664170 prefixEnd_2664170 1367999755288946656322711 := by
  unfold tailWord_2664170
  simp only [CollatzResearch.WordTrace]
  refine ⟨24292565689543642214097491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64780175172116379237593309 24292565689543642214097491)
  ·
    refine ⟨36438848534315463321146237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24292565689543642214097491 36438848534315463321146237)
    ·
      refine ⟨13664568200368298745429839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36438848534315463321146237 13664568200368298745429839)
      ·
        refine ⟨20496852300552448118144759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13664568200368298745429839 20496852300552448118144759)
        ·
          refine ⟨30745278450828672177217139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20496852300552448118144759 30745278450828672177217139)
          ·
            refine ⟨46117917676243008265825709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30745278450828672177217139 46117917676243008265825709)
            ·
              refine ⟨17294219128591128099684641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46117917676243008265825709 17294219128591128099684641)
              ·
                refine ⟨12970664346443346074763481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17294219128591128099684641 12970664346443346074763481)
                ·
                  refine ⟨9727998259832509556072611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12970664346443346074763481 9727998259832509556072611)
                  ·
                    refine ⟨14591997389748764334108917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9727998259832509556072611 14591997389748764334108917)
                    ·
                      refine ⟨1367999755288946656322711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14591997389748764334108917 1367999755288946656322711)
                      ·
                        rfl

theorem cell23_2664170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_2664170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664170 prefixEnd_2664170 := by exact prefixLift 2664170
  have htrace : WordTrace (prefixWord ++ tailWord_2664170) baseStart_2664170 baseEnd_2664170 := by
    simpa [prefixWord, tailWord_2664170, baseEnd_2664170] using wordTrace_append hprefix tailTrace_2664170
  have hstable : (prefixWord ++ tailWord_2664170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664170).length < 2 ^ (prefixWord ++ tailWord_2664170).sum := by decide
  have hdescent : baseEnd_2664170 < baseStart_2664170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664220 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_2664220 : Nat := 118140960795 + 2664220 * 2 ^ 59
def prefixEnd_2664220 : Nat := 4983230072969 + 3 ^ 40 * 2664220 * 2
def baseEnd_2664220 : Nat := 456008476440557153565827

theorem tailTrace_2664220 : CollatzResearch.WordTrace tailWord_2664220 prefixEnd_2664220 456008476440557153565827 := by
  unfold tailWord_2664220
  simp only [CollatzResearch.WordTrace]
  refine ⟨48586043203996713697855057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64781390938662284930473409 48586043203996713697855057)
  ·
    refine ⟨36439532402997535273391293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48586043203996713697855057 36439532402997535273391293)
    ·
      refine ⟨13664824651124075727521735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36439532402997535273391293 13664824651124075727521735)
      ·
        refine ⟨20497236976686113591282603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13664824651124075727521735 20497236976686113591282603)
        ·
          refine ⟨30745855465029170386923905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20497236976686113591282603 30745855465029170386923905)
          ·
            refine ⟨23059391598771877790192929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30745855465029170386923905 23059391598771877790192929)
            ·
              refine ⟨17294543699078908342644697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23059391598771877790192929 17294543699078908342644697)
              ·
                refine ⟨12970907774309181256983523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17294543699078908342644697 12970907774309181256983523)
                ·
                  refine ⟨19456361661463771885475285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12970907774309181256983523 19456361661463771885475285)
                  ·
                    refine ⟨456008476440557153565827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19456361661463771885475285 456008476440557153565827)
                    ·
                      rfl

theorem cell23_2664220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_2664220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664220 prefixEnd_2664220 := by exact prefixLift 2664220
  have htrace : WordTrace (prefixWord ++ tailWord_2664220) baseStart_2664220 baseEnd_2664220 := by
    simpa [prefixWord, tailWord_2664220, baseEnd_2664220] using wordTrace_append hprefix tailTrace_2664220
  have hstable : (prefixWord ++ tailWord_2664220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664220).length < 2 ^ (prefixWord ++ tailWord_2664220).sum := by decide
  have hdescent : baseEnd_2664220 < baseStart_2664220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664274 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_2664274 : Nat := 118140960795 + 2664274 * 2 ^ 59
def prefixEnd_2664274 : Nat := 4983230072969 + 3 ^ 40 * 2664274 * 2
def baseEnd_2664274 : Nat := 1368053157277014249422233

theorem tailTrace_2664274 : CollatzResearch.WordTrace tailWord_2664274 prefixEnd_2664274 1368053157277014249422233 := by
  unfold tailWord_2664274
  simp only [CollatzResearch.WordTrace]
  refine ⟨24293513987449448654543969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64782703966531863078783917 24293513987449448654543969)
  ·
    refine ⟨18220135490587086490907977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24293513987449448654543969 18220135490587086490907977)
    ·
      refine ⟨13665101617940314868180983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18220135490587086490907977 13665101617940314868180983)
      ·
        refine ⟨20497652426910472302271475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13665101617940314868180983 20497652426910472302271475)
        ·
          refine ⟨30746478640365708453407213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20497652426910472302271475 30746478640365708453407213)
          ·
            refine ⟨11529929490137140670027705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30746478640365708453407213 11529929490137140670027705)
            ·
              refine ⟨8647447117602855502520779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11529929490137140670027705 8647447117602855502520779)
              ·
                refine ⟨12971170676404283253781169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8647447117602855502520779 12971170676404283253781169)
                ·
                  refine ⟨9728378007303212440335877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12971170676404283253781169 9728378007303212440335877)
                  ·
                    refine ⟨1824070876369352332562977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9728378007303212440335877 1824070876369352332562977)
                    ·
                      refine ⟨1368053157277014249422233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824070876369352332562977 1368053157277014249422233)
                      ·
                        rfl

theorem cell23_2664274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_2664274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664274 prefixEnd_2664274 := by exact prefixLift 2664274
  have htrace : WordTrace (prefixWord ++ tailWord_2664274) baseStart_2664274 baseEnd_2664274 := by
    simpa [prefixWord, tailWord_2664274, baseEnd_2664274] using wordTrace_append hprefix tailTrace_2664274
  have hstable : (prefixWord ++ tailWord_2664274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664274).length < 2 ^ (prefixWord ++ tailWord_2664274).sum := by decide
  have hdescent : baseEnd_2664274 < baseStart_2664274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664277 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_2664277 : Nat := 118140960795 + 2664277 * 2 ^ 59
def prefixEnd_2664277 : Nat := 4983230072969 + 3 ^ 40 * 2664277 * 2
def baseEnd_2664277 : Nat := 1368054697718977737684719

theorem tailTrace_2664277 : CollatzResearch.WordTrace tailWord_2664277 prefixEnd_2664277 1368054697718977737684719 := by
  unfold tailWord_2664277
  simp only [CollatzResearch.WordTrace]
  refine ⟨97174165368786926130535085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64782776912524617420356723 97174165368786926130535085)
  ·
    refine ⟨36440312013295097298950657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97174165368786926130535085 36440312013295097298950657)
    ·
      refine ⟨27330234009971322974212993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36440312013295097298950657 27330234009971322974212993)
      ·
        refine ⟨20497675507478492230659745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27330234009971322974212993 20497675507478492230659745)
        ·
          refine ⟨15373256630608869172994809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20497675507478492230659745 15373256630608869172994809)
          ·
            refine ⟨11529942472956651879746107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15373256630608869172994809 11529942472956651879746107)
            ·
              refine ⟨17294913709434977819619161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11529942472956651879746107 17294913709434977819619161)
              ·
                refine ⟨12971185282076233364714371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17294913709434977819619161 12971185282076233364714371)
                ·
                  refine ⟨19456777923114350047071557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12971185282076233364714371 19456777923114350047071557)
                  ·
                    refine ⟨3648145860583940633825917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19456777923114350047071557 3648145860583940633825917)
                    ·
                      refine ⟨1368054697718977737684719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3648145860583940633825917 1368054697718977737684719)
                      ·
                        rfl

theorem cell23_2664277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_2664277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664277 prefixEnd_2664277 := by exact prefixLift 2664277
  have htrace : WordTrace (prefixWord ++ tailWord_2664277) baseStart_2664277 baseEnd_2664277 := by
    simpa [prefixWord, tailWord_2664277, baseEnd_2664277] using wordTrace_append hprefix tailTrace_2664277
  have hstable : (prefixWord ++ tailWord_2664277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664277).length < 2 ^ (prefixWord ++ tailWord_2664277).sum := by decide
  have hdescent : baseEnd_2664277 < baseStart_2664277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664301 : List Nat := [1, 5, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_2664301 : Nat := 118140960795 + 2664301 * 2 ^ 59
def prefixEnd_2664301 : Nat := 4983230072969 + 3 ^ 40 * 2664301 * 2
def baseEnd_2664301 : Nat := 456022340418228547928203

theorem tailTrace_2664301 : CollatzResearch.WordTrace tailWord_2664301 prefixEnd_2664301 456022340418228547928203 := by
  unfold tailWord_2664301
  simp only [CollatzResearch.WordTrace]
  refine ⟨97175040720699978229408757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64783360480466652152939171 97175040720699978229408757)
  ·
    refine ⟨9110160067565622959007071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97175040720699978229408757 9110160067565622959007071)
    ·
      refine ⟨13665240101348434438510607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9110160067565622959007071 13665240101348434438510607)
      ·
        refine ⟨20497860152022651657765911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13665240101348434438510607 20497860152022651657765911)
        ·
          refine ⟨30746790228033977486648867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20497860152022651657765911 30746790228033977486648867)
          ·
            refine ⟨46120185342050966229973301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30746790228033977486648867 46120185342050966229973301)
            ·
              refine ⟨4323767375817278084059997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46120185342050966229973301 4323767375817278084059997)
              ·
                refine ⟨1621412765931479281522499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4323767375817278084059997 1621412765931479281522499)
                ·
                  refine ⟨2432119148897218922283749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621412765931479281522499 2432119148897218922283749)
                  ·
                    refine ⟨456022340418228547928203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2432119148897218922283749 456022340418228547928203)
                    ·
                      rfl

theorem cell23_2664301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_2664301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664301 prefixEnd_2664301 := by exact prefixLift 2664301
  have htrace : WordTrace (prefixWord ++ tailWord_2664301) baseStart_2664301 baseEnd_2664301 := by
    simpa [prefixWord, tailWord_2664301, baseEnd_2664301] using wordTrace_append hprefix tailTrace_2664301
  have hstable : (prefixWord ++ tailWord_2664301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664301).length < 2 ^ (prefixWord ++ tailWord_2664301).sum := by decide
  have hdescent : baseEnd_2664301 < baseStart_2664301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664318 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2664318 : Nat := 118140960795 + 2664318 * 2 ^ 59
def prefixEnd_2664318 : Nat := 4983230072969 + 3 ^ 40 * 2664318 * 2
def baseEnd_2664318 : Nat := 456025250141937359090677

theorem tailTrace_2664318 : CollatzResearch.WordTrace tailWord_2664318 prefixEnd_2664318 456025250141937359090677 := by
  unfold tailWord_2664318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12146957595204798766597201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64783773841092260088518405 12146957595204798766597201)
  ·
    refine ⟨9110218196403599074947901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12146957595204798766597201 9110218196403599074947901)
    ·
      refine ⟨3416331823651349653105463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9110218196403599074947901 3416331823651349653105463)
      ·
        refine ⟨5124497735477024479658195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3416331823651349653105463 5124497735477024479658195)
        ·
          refine ⟨7686746603215536719487293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124497735477024479658195 7686746603215536719487293)
          ·
            refine ⟨2882529976205826269807735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7686746603215536719487293 2882529976205826269807735)
            ·
              refine ⟨4323794964308739404711603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882529976205826269807735 4323794964308739404711603)
              ·
                refine ⟨6485692446463109107067405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4323794964308739404711603 6485692446463109107067405)
                ·
                  refine ⟨2432134667423665915150277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6485692446463109107067405 2432134667423665915150277)
                  ·
                    refine ⟨456025250141937359090677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2432134667423665915150277 456025250141937359090677)
                    ·
                      rfl

theorem cell23_2664318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2664318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664318 prefixEnd_2664318 := by exact prefixLift 2664318
  have htrace : WordTrace (prefixWord ++ tailWord_2664318) baseStart_2664318 baseEnd_2664318 := by
    simpa [prefixWord, tailWord_2664318, baseEnd_2664318] using wordTrace_append hprefix tailTrace_2664318
  have hstable : (prefixWord ++ tailWord_2664318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664318).length < 2 ^ (prefixWord ++ tailWord_2664318).sum := by decide
  have hdescent : baseEnd_2664318 < baseStart_2664318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664357 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_2664357 : Nat := 118140960795 + 2664357 * 2 ^ 59
def prefixEnd_2664357 : Nat := 4983230072969 + 3 ^ 40 * 2664357 * 2
def baseEnd_2664357 : Nat := 456031925390445808228117

theorem tailTrace_2664357 : CollatzResearch.WordTrace tailWord_2664357 prefixEnd_2664357 456031925390445808228117 := by
  unfold tailWord_2664357
  simp only [CollatzResearch.WordTrace]
  refine ⟨97177083208497099793447325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64784722138998066528964883 97177083208497099793447325)
  ·
    refine ⟨36441406203186412422542747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97177083208497099793447325 36441406203186412422542747)
    ·
      refine ⟨54662109304779618633814121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36441406203186412422542747 54662109304779618633814121)
      ·
        refine ⟨40996581978584713975360591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54662109304779618633814121 40996581978584713975360591)
        ·
          refine ⟨61494872967877070963040887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40996581978584713975360591 61494872967877070963040887)
          ·
            refine ⟨92242309451815606444561331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61494872967877070963040887 92242309451815606444561331)
            ·
              refine ⟨138363464177723409666841997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92242309451815606444561331 138363464177723409666841997)
              ·
                refine ⟨51886299066646278625065749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138363464177723409666841997 51886299066646278625065749)
                ·
                  refine ⟨2432170268749044310549957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51886299066646278625065749 2432170268749044310549957)
                  ·
                    refine ⟨456031925390445808228117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2432170268749044310549957 456031925390445808228117)
                    ·
                      rfl

theorem cell23_2664357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_2664357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664357 prefixEnd_2664357 := by exact prefixLift 2664357
  have htrace : WordTrace (prefixWord ++ tailWord_2664357) baseStart_2664357 baseEnd_2664357 := by
    simpa [prefixWord, tailWord_2664357, baseEnd_2664357] using wordTrace_append hprefix tailTrace_2664357
  have hstable : (prefixWord ++ tailWord_2664357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664357).length < 2 ^ (prefixWord ++ tailWord_2664357).sum := by decide
  have hdescent : baseEnd_2664357 < baseStart_2664357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664377 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2664377 : Nat := 118140960795 + 2664377 * 2 ^ 59
def prefixEnd_2664377 : Nat := 4983230072969 + 3 ^ 40 * 2664377 * 2
def baseEnd_2664377 : Nat := 1368106045784427346434259

theorem tailTrace_2664377 : CollatzResearch.WordTrace tailWord_2664377 prefixEnd_2664377 1368106045784427346434259 := by
  unfold tailWord_2664377
  simp only [CollatzResearch.WordTrace]
  refine ⟨97177812668424643209175385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64785208445616428806116923 97177812668424643209175385)
  ·
    refine ⟨72883359501318482406881539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97177812668424643209175385 72883359501318482406881539)
    ·
      refine ⟨109325039251977723610322309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72883359501318482406881539 109325039251977723610322309)
      ·
        refine ⟨20498444859745823176935433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109325039251977723610322309 20498444859745823176935433)
        ·
          refine ⟨15373833644809367382701575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20498444859745823176935433 15373833644809367382701575)
          ·
            refine ⟨23060750467214051074052363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15373833644809367382701575 23060750467214051074052363)
            ·
              refine ⟨34591125700821076611078545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23060750467214051074052363 34591125700821076611078545)
              ·
                refine ⟨25943344275615807458308909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34591125700821076611078545 25943344275615807458308909)
                ·
                  refine ⟨9728754103355927796865841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25943344275615807458308909 9728754103355927796865841)
                  ·
                    refine ⟨7296565577516945847649381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9728754103355927796865841 7296565577516945847649381)
                    ·
                      refine ⟨1368106045784427346434259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7296565577516945847649381 1368106045784427346434259)
                      ·
                        rfl

theorem cell23_2664377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2664377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664377 prefixEnd_2664377 := by exact prefixLift 2664377
  have htrace : WordTrace (prefixWord ++ tailWord_2664377) baseStart_2664377 baseEnd_2664377 := by
    simpa [prefixWord, tailWord_2664377, baseEnd_2664377] using wordTrace_append hprefix tailTrace_2664377
  have hstable : (prefixWord ++ tailWord_2664377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664377).length < 2 ^ (prefixWord ++ tailWord_2664377).sum := by decide
  have hdescent : baseEnd_2664377 < baseStart_2664377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664404 : List Nat := [2, 4, 1, 2, 1, 1, 5, 7]
def baseStart_2664404 : Nat := 118140960795 + 2664404 * 2 ^ 59
def prefixEnd_2664404 : Nat := 4983230072969 + 3 ^ 40 * 2664404 * 2
def baseEnd_2664404 : Nat := 50671107768966620029505

theorem tailTrace_2664404 : CollatzResearch.WordTrace tailWord_2664404 prefixEnd_2664404 50671107768966620029505 := by
  unfold tailWord_2664404
  simp only [CollatzResearch.WordTrace]
  refine ⟨48589398719663413410204133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64785864959551217880272177 48589398719663413410204133)
  ·
    refine ⟨9110512259936890014413275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48589398719663413410204133 9110512259936890014413275)
    ·
      refine ⟨13665768389905335021619913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9110512259936890014413275 13665768389905335021619913)
      ·
        refine ⟨10249326292429001266214935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13665768389905335021619913 10249326292429001266214935)
        ·
          refine ⟨15373989438643501899322403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10249326292429001266214935 15373989438643501899322403)
          ·
            refine ⟨23060984157965252848983605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15373989438643501899322403 23060984157965252848983605)
            ·
              refine ⟨2161967264809242454592213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23060984157965252848983605 2161967264809242454592213)
              ·
                refine ⟨50671107768966620029505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2161967264809242454592213 50671107768966620029505)
                ·
                  rfl

theorem cell23_2664404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 7].length) (baseStart_2664404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664404 prefixEnd_2664404 := by exact prefixLift 2664404
  have htrace : WordTrace (prefixWord ++ tailWord_2664404) baseStart_2664404 baseEnd_2664404 := by
    simpa [prefixWord, tailWord_2664404, baseEnd_2664404] using wordTrace_append hprefix tailTrace_2664404
  have hstable : (prefixWord ++ tailWord_2664404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664404).length < 2 ^ (prefixWord ++ tailWord_2664404).sum := by decide
  have hdescent : baseEnd_2664404 < baseStart_2664404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664412 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2664412 : Nat := 118140960795 + 2664412 * 2 ^ 59
def prefixEnd_2664412 : Nat := 4983230072969 + 3 ^ 40 * 2664412 * 2
def baseEnd_2664412 : Nat := 456041339202444903165533

theorem tailTrace_2664412 : CollatzResearch.WordTrace tailWord_2664412 prefixEnd_2664412 456041339202444903165533 := by
  unfold tailWord_2664412
  simp only [CollatzResearch.WordTrace]
  refine ⟨48589544611648922093349745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64786059482198562791132993 48589544611648922093349745)
  ·
    refine ⟨36442158458736691570012309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48589544611648922093349745 36442158458736691570012309)
    ·
      refine ⟨1708226177753282417344327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36442158458736691570012309 1708226177753282417344327)
      ·
        refine ⟨2562339266629923626016491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1708226177753282417344327 2562339266629923626016491)
        ·
          refine ⟨3843508899944885439024737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562339266629923626016491 3843508899944885439024737)
          ·
            refine ⟨2882631674958664079268553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3843508899944885439024737 2882631674958664079268553)
            ·
              refine ⟨2161973756218998059451415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2882631674958664079268553 2161973756218998059451415)
              ·
                refine ⟨3242960634328497089177123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161973756218998059451415 3242960634328497089177123)
                ·
                  refine ⟨4864440951492745633765685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242960634328497089177123 4864440951492745633765685)
                  ·
                    refine ⟨456041339202444903165533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4864440951492745633765685 456041339202444903165533)
                    ·
                      rfl

theorem cell23_2664412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2664412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664412 prefixEnd_2664412 := by exact prefixLift 2664412
  have htrace : WordTrace (prefixWord ++ tailWord_2664412) baseStart_2664412 baseEnd_2664412 := by
    simpa [prefixWord, tailWord_2664412, baseEnd_2664412] using wordTrace_append hprefix tailTrace_2664412
  have hstable : (prefixWord ++ tailWord_2664412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664412).length < 2 ^ (prefixWord ++ tailWord_2664412).sum := by decide
  have hdescent : baseEnd_2664412 < baseStart_2664412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664415 : List Nat := [1, 1, 2, 3, 4, 2, 2, 3, 1, 2, 2]
def baseStart_2664415 : Nat := 118140960795 + 2664415 * 2 ^ 59
def prefixEnd_2664415 : Nat := 4983230072969 + 3 ^ 40 * 2664415 * 2
def baseEnd_2664415 : Nat := 1368125558049298197759085

theorem tailTrace_2664415 : CollatzResearch.WordTrace tailWord_2664415 prefixEnd_2664415 1368125558049298197759085 := by
  unfold tailWord_2664415
  simp only [CollatzResearch.WordTrace]
  refine ⟨97179198642286975699058699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64786132428191317132705799 97179198642286975699058699)
  ·
    refine ⟨145768797963430463548588049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97179198642286975699058699 145768797963430463548588049)
    ·
      refine ⟨109326598472572847661441037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145768797963430463548588049 109326598472572847661441037)
      ·
        refine ⟨40997474427214817873040389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109326598472572847661441037 40997474427214817873040389)
        ·
          refine ⟨7687026455102778351195073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40997474427214817873040389 7687026455102778351195073)
          ·
            refine ⟨5765269841327083763396305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7687026455102778351195073 5765269841327083763396305)
            ·
              refine ⟨4323952380995312822547229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5765269841327083763396305 4323952380995312822547229)
              ·
                refine ⟨1621482142873242308455211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4323952380995312822547229 1621482142873242308455211)
                ·
                  refine ⟨2432223214309863462682817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621482142873242308455211 2432223214309863462682817)
                  ·
                    refine ⟨1824167410732397597012113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2432223214309863462682817 1824167410732397597012113)
                    ·
                      refine ⟨1368125558049298197759085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824167410732397597012113 1368125558049298197759085)
                      ·
                        rfl

theorem cell23_2664415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_2664415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664415 prefixEnd_2664415 := by exact prefixLift 2664415
  have htrace : WordTrace (prefixWord ++ tailWord_2664415) baseStart_2664415 baseEnd_2664415 := by
    simpa [prefixWord, tailWord_2664415, baseEnd_2664415] using wordTrace_append hprefix tailTrace_2664415
  have hstable : (prefixWord ++ tailWord_2664415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664415).length < 2 ^ (prefixWord ++ tailWord_2664415).sum := by decide
  have hdescent : baseEnd_2664415 < baseStart_2664415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664467 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 4]
def baseStart_2664467 : Nat := 118140960795 + 2664467 * 2 ^ 59
def prefixEnd_2664467 : Nat := 4983230072969 + 3 ^ 40 * 2664467 * 2
def baseEnd_2664467 : Nat := 1368152259043331994308845

theorem tailTrace_2664467 : CollatzResearch.WordTrace tailWord_2664467 prefixEnd_2664467 1368152259043331994308845 := by
  unfold tailWord_2664467
  simp only [CollatzResearch.WordTrace]
  refine ⟨97181095238098588579951655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64787396825399059053301103 97181095238098588579951655)
  ·
    refine ⟨145771642857147882869927483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97181095238098588579951655 145771642857147882869927483)
    ·
      refine ⟨218657464285721824304891225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145771642857147882869927483 218657464285721824304891225)
      ·
        refine ⟨163993098214291368228668419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218657464285721824304891225 163993098214291368228668419)
        ·
          refine ⟨245989647321437052343002629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163993098214291368228668419 245989647321437052343002629)
          ·
            refine ⟨46123058872769447314312993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245989647321437052343002629 46123058872769447314312993)
            ·
              refine ⟨34592294154577085485734745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46123058872769447314312993 34592294154577085485734745)
              ·
                refine ⟨25944220615932814114301059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34592294154577085485734745 25944220615932814114301059)
                ·
                  refine ⟨38916330923899221171451589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25944220615932814114301059 38916330923899221171451589)
                  ·
                    refine ⟨7296812048231103969647173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38916330923899221171451589 7296812048231103969647173)
                    ·
                      refine ⟨1368152259043331994308845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7296812048231103969647173 1368152259043331994308845)
                      ·
                        rfl

theorem cell23_2664467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_2664467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664467 prefixEnd_2664467 := by exact prefixLift 2664467
  have htrace : WordTrace (prefixWord ++ tailWord_2664467) baseStart_2664467 baseEnd_2664467 := by
    simpa [prefixWord, tailWord_2664467, baseEnd_2664467] using wordTrace_append hprefix tailTrace_2664467
  have hstable : (prefixWord ++ tailWord_2664467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664467).length < 2 ^ (prefixWord ++ tailWord_2664467).sum := by decide
  have hdescent : baseEnd_2664467 < baseStart_2664467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664474 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_2664474 : Nat := 118140960795 + 2664474 * 2 ^ 59
def prefixEnd_2664474 : Nat := 4983230072969 + 3 ^ 40 * 2664474 * 2
def baseEnd_2664474 : Nat := 1368155853407913466921313

theorem tailTrace_2664474 : CollatzResearch.WordTrace tailWord_2664474 prefixEnd_2664474 1368155853407913466921313 := by
  unfold tailWord_2664474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24295337637268307193864119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64787567032715485850304317 24295337637268307193864119)
  ·
    refine ⟨36443006455902460790796179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24295337637268307193864119 36443006455902460790796179)
    ·
      refine ⟨54664509683853691186194269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36443006455902460790796179 54664509683853691186194269)
      ·
        refine ⟨20499191131445134194822851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54664509683853691186194269 20499191131445134194822851)
        ·
          refine ⟨30748786697167701292234277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20499191131445134194822851 30748786697167701292234277)
          ·
            refine ⟨5765397505718943992293927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30748786697167701292234277 5765397505718943992293927)
            ·
              refine ⟨8648096258578415988440891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765397505718943992293927 8648096258578415988440891)
              ·
                refine ⟨12972144387867623982661337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8648096258578415988440891 12972144387867623982661337)
                ·
                  refine ⟨9729108290900717986996003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12972144387867623982661337 9729108290900717986996003)
                  ·
                    refine ⟨14593662436351076980494005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9729108290900717986996003 14593662436351076980494005)
                    ·
                      refine ⟨1368155853407913466921313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14593662436351076980494005 1368155853407913466921313)
                      ·
                        rfl

theorem cell23_2664474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_2664474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664474 prefixEnd_2664474 := by exact prefixLift 2664474
  have htrace : WordTrace (prefixWord ++ tailWord_2664474) baseStart_2664474 baseEnd_2664474 := by
    simpa [prefixWord, tailWord_2664474, baseEnd_2664474] using wordTrace_append hprefix tailTrace_2664474
  have hstable : (prefixWord ++ tailWord_2664474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664474).length < 2 ^ (prefixWord ++ tailWord_2664474).sum := by decide
  have hdescent : baseEnd_2664474 < baseStart_2664474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664505 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 2, 2, 2]
def baseStart_2664505 : Nat := 118140960795 + 2664505 * 2 ^ 59
def prefixEnd_2664505 : Nat := 4983230072969 + 3 ^ 40 * 2664505 * 2
def baseEnd_2664505 : Nat := 1368171771308202845633671

theorem tailTrace_2664505 : CollatzResearch.WordTrace tailWord_2664505 prefixEnd_2664505 1368171771308202845633671 := by
  unfold tailWord_2664505
  simp only [CollatzResearch.WordTrace]
  refine ⟨97182481211960921069834969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64788320807973947379889979 97182481211960921069834969)
  ·
    refine ⟨72886860908970690802376227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97182481211960921069834969 72886860908970690802376227)
    ·
      refine ⟨109330291363456036203564341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72886860908970690802376227 109330291363456036203564341)
      ·
        refine ⟨10249714815324003394084157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109330291363456036203564341 10249714815324003394084157)
        ·
          refine ⟨3843643055746501272781559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10249714815324003394084157 3843643055746501272781559)
          ·
            refine ⟨5765464583619751909172339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3843643055746501272781559 5765464583619751909172339)
            ·
              refine ⟨8648196875429627863758509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765464583619751909172339 8648196875429627863758509)
              ·
                refine ⟨3243073828286110448909441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8648196875429627863758509 3243073828286110448909441)
                ·
                  refine ⟨2432305371214582836682081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3243073828286110448909441 2432305371214582836682081)
                  ·
                    refine ⟨1824229028410937127511561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2432305371214582836682081 1824229028410937127511561)
                    ·
                      refine ⟨1368171771308202845633671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824229028410937127511561 1368171771308202845633671)
                      ·
                        rfl

theorem cell23_2664505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_2664505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664505 prefixEnd_2664505 := by exact prefixLift 2664505
  have htrace : WordTrace (prefixWord ++ tailWord_2664505) baseStart_2664505 baseEnd_2664505 := by
    simpa [prefixWord, tailWord_2664505, baseEnd_2664505] using wordTrace_append hprefix tailTrace_2664505
  have hstable : (prefixWord ++ tailWord_2664505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664505).length < 2 ^ (prefixWord ++ tailWord_2664505).sum := by decide
  have hdescent : baseEnd_2664505 < baseStart_2664505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664517 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_2664517 : Nat := 118140960795 + 2664517 * 2 ^ 59
def prefixEnd_2664517 : Nat := 4983230072969 + 3 ^ 40 * 2664517 * 2
def baseEnd_2664517 : Nat := 1368177933076056798683615

theorem tailTrace_2664517 : CollatzResearch.WordTrace tailWord_2664517 prefixEnd_2664517 1368177933076056798683615 := by
  unfold tailWord_2664517
  simp only [CollatzResearch.WordTrace]
  refine ⟨97182918887917447119271805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64788612591944964746181203 97182918887917447119271805)
  ·
    refine ⟨36443594582969042669726927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97182918887917447119271805 36443594582969042669726927)
    ·
      refine ⟨54665391874453564004590391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36443594582969042669726927 54665391874453564004590391)
      ·
        refine ⟨81998087811680346006885587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54665391874453564004590391 81998087811680346006885587)
        ·
          refine ⟨122997131717520519010328381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81998087811680346006885587 122997131717520519010328381)
          ·
            refine ⟨46123924394070194628873143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122997131717520519010328381 46123924394070194628873143)
            ·
              refine ⟨69185886591105291943309715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46123924394070194628873143 69185886591105291943309715)
              ·
                refine ⟨103778829886657937914964573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69185886591105291943309715 103778829886657937914964573)
                ·
                  refine ⟨38917061207496726718111715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103778829886657937914964573 38917061207496726718111715)
                  ·
                    refine ⟨58375591811245090077167573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38917061207496726718111715 58375591811245090077167573)
                    ·
                      refine ⟨1368177933076056798683615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58375591811245090077167573 1368177933076056798683615)
                      ·
                        rfl

theorem cell23_2664517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_2664517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664517 prefixEnd_2664517 := by exact prefixLift 2664517
  have htrace : WordTrace (prefixWord ++ tailWord_2664517) baseStart_2664517 baseEnd_2664517 := by
    simpa [prefixWord, tailWord_2664517, baseEnd_2664517] using wordTrace_append hprefix tailTrace_2664517
  have hstable : (prefixWord ++ tailWord_2664517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664517).length < 2 ^ (prefixWord ++ tailWord_2664517).sum := by decide
  have hdescent : baseEnd_2664517 < baseStart_2664517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664524 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_2664524 : Nat := 118140960795 + 2664524 * 2 ^ 59
def prefixEnd_2664524 : Nat := 4983230072969 + 3 ^ 40 * 2664524 * 2
def baseEnd_2664524 : Nat := 456060509146879423765361

theorem tailTrace_2664524 : CollatzResearch.WordTrace tailWord_2664524 prefixEnd_2664524 456060509146879423765361 := by
  unfold tailWord_2664524
  simp only [CollatzResearch.WordTrace]
  refine ⟨48591587099446043657388313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64788782799261391543184417 48591587099446043657388313)
  ·
    refine ⟨36443690324584532743041235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48591587099446043657388313 36443690324584532743041235)
    ·
      refine ⟨54665535486876799114561853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36443690324584532743041235 54665535486876799114561853)
      ·
        refine ⟨20499575807578799667960695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54665535486876799114561853 20499575807578799667960695)
        ·
          refine ⟨30749363711368199501941043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20499575807578799667960695 30749363711368199501941043)
          ·
            refine ⟨46124045567052299252911565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30749363711368199501941043 46124045567052299252911565)
            ·
              refine ⟨17296517087644612219841837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46124045567052299252911565 17296517087644612219841837)
              ·
                refine ⟨6486193907866729582440689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17296517087644612219841837 6486193907866729582440689)
                ·
                  refine ⟨4864645430900047186830517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6486193907866729582440689 4864645430900047186830517)
                  ·
                    refine ⟨456060509146879423765361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4864645430900047186830517 456060509146879423765361)
                    ·
                      rfl

theorem cell23_2664524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_2664524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664524 prefixEnd_2664524 := by exact prefixLift 2664524
  have htrace : WordTrace (prefixWord ++ tailWord_2664524) baseStart_2664524 baseEnd_2664524 := by
    simpa [prefixWord, tailWord_2664524, baseEnd_2664524] using wordTrace_append hprefix tailTrace_2664524
  have hstable : (prefixWord ++ tailWord_2664524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664524).length < 2 ^ (prefixWord ++ tailWord_2664524).sum := by decide
  have hdescent : baseEnd_2664524 < baseStart_2664524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664561 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 2, 4, 2]
def baseStart_2664561 : Nat := 118140960795 + 2664561 * 2 ^ 59
def prefixEnd_2664561 : Nat := 4983230072969 + 3 ^ 40 * 2664561 * 2
def baseEnd_2664561 : Nat := 1368200526224854626533413

theorem tailTrace_2664561 : CollatzResearch.WordTrace tailWord_2664561 prefixEnd_2664561 1368200526224854626533413 := by
  unfold tailWord_2664561
  simp only [CollatzResearch.WordTrace]
  refine ⟨97184523699758042633873537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64789682466505361755915691 97184523699758042633873537)
  ·
    refine ⟨72888392774818531975405153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97184523699758042633873537 72888392774818531975405153)
    ·
      refine ⟨54666294581113898981553865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72888392774818531975405153 54666294581113898981553865)
      ·
        refine ⟨40999720935835424236165399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54666294581113898981553865 40999720935835424236165399)
        ·
          refine ⟨61499581403753136354248099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40999720935835424236165399 61499581403753136354248099)
          ·
            refine ⟨92249372105629704531372149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61499581403753136354248099 92249372105629704531372149)
            ·
              refine ⟨8648378634902784799816139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92249372105629704531372149 8648378634902784799816139)
              ·
                refine ⟨12972567952354177199724209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8648378634902784799816139 12972567952354177199724209)
                ·
                  refine ⟨9729425964265632899793157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12972567952354177199724209 9729425964265632899793157)
                  ·
                    refine ⟨1824267368299806168711217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9729425964265632899793157 1824267368299806168711217)
                    ·
                      refine ⟨1368200526224854626533413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824267368299806168711217 1368200526224854626533413)
                      ·
                        rfl

theorem cell23_2664561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_2664561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664561 prefixEnd_2664561 := by exact prefixLift 2664561
  have htrace : WordTrace (prefixWord ++ tailWord_2664561) baseStart_2664561 baseEnd_2664561 := by
    simpa [prefixWord, tailWord_2664561, baseEnd_2664561] using wordTrace_append hprefix tailTrace_2664561
  have hstable : (prefixWord ++ tailWord_2664561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664561).length < 2 ^ (prefixWord ++ tailWord_2664561).sum := by decide
  have hdescent : baseEnd_2664561 < baseStart_2664561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664581 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 1, 4, 3]
def baseStart_2664581 : Nat := 118140960795 + 2664581 * 2 ^ 59
def prefixEnd_2664581 : Nat := 4983230072969 + 3 ^ 40 * 2664581 * 2
def baseEnd_2664581 : Nat := 1368210795837944548283321

theorem tailTrace_2664581 : CollatzResearch.WordTrace tailWord_2664581 prefixEnd_2664581 1368210795837944548283321 := by
  unfold tailWord_2664581
  simp only [CollatzResearch.WordTrace]
  refine ⟨97185253159685586049601597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64790168773123724033067731 97185253159685586049601597)
  ·
    refine ⟨36444469934882094768600599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97185253159685586049601597 36444469934882094768600599)
    ·
      refine ⟨54666704902323142152900899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36444469934882094768600599 54666704902323142152900899)
      ·
        refine ⟨82000057353484713229351349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54666704902323142152900899 82000057353484713229351349)
        ·
          refine ⟨7687505376889191865251689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82000057353484713229351349 7687505376889191865251689)
          ·
            refine ⟨5765629032666893898938767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7687505376889191865251689 5765629032666893898938767)
            ·
              refine ⟨8648443549000340848408151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765629032666893898938767 8648443549000340848408151)
              ·
                refine ⟨12972665323500511272612227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8648443549000340848408151 12972665323500511272612227)
                ·
                  refine ⟨19458997985250766908918341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12972665323500511272612227 19458997985250766908918341)
                  ·
                    refine ⟨3648562122234518795422189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19458997985250766908918341 3648562122234518795422189)
                    ·
                      refine ⟨1368210795837944548283321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3648562122234518795422189 1368210795837944548283321)
                      ·
                        rfl

theorem cell23_2664581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_2664581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664581 prefixEnd_2664581 := by exact prefixLift 2664581
  have htrace : WordTrace (prefixWord ++ tailWord_2664581) baseStart_2664581 baseEnd_2664581 := by
    simpa [prefixWord, tailWord_2664581, baseEnd_2664581] using wordTrace_append hprefix tailTrace_2664581
  have hstable : (prefixWord ++ tailWord_2664581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664581).length < 2 ^ (prefixWord ++ tailWord_2664581).sum := by decide
  have hdescent : baseEnd_2664581 < baseStart_2664581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664604 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2664604 : Nat := 118140960795 + 2664604 * 2 ^ 59
def prefixEnd_2664604 : Nat := 4983230072969 + 3 ^ 40 * 2664604 * 2
def baseEnd_2664604 : Nat := 1368222605892997958295715

theorem tailTrace_2664604 : CollatzResearch.WordTrace tailWord_2664604 prefixEnd_2664604 1368222605892997958295715 := by
  unfold tailWord_2664604
  simp only [CollatzResearch.WordTrace]
  refine ⟨48593046019301130488844433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64790728025734840651792577 48593046019301130488844433)
  ·
    refine ⟨36444784514475847866633325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48593046019301130488844433 36444784514475847866633325)
    ·
      refine ⟨13666794192928442949987497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36444784514475847866633325 13666794192928442949987497)
      ·
        refine ⟨10250095644696332212490623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13666794192928442949987497 10250095644696332212490623)
        ·
          refine ⟨15375143467044498318735935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10250095644696332212490623 15375143467044498318735935)
          ·
            refine ⟨23062715200566747478103903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15375143467044498318735935 23062715200566747478103903)
            ·
              refine ⟨34594072800850121217155855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23062715200566747478103903 34594072800850121217155855)
              ·
                refine ⟨51891109201275181825733783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34594072800850121217155855 51891109201275181825733783)
                ·
                  refine ⟨77836663801912772738600675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51891109201275181825733783 77836663801912772738600675)
                  ·
                    refine ⟨116754995702869159107901013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77836663801912772738600675 116754995702869159107901013)
                    ·
                      refine ⟨1368222605892997958295715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 116754995702869159107901013 1368222605892997958295715)
                      ·
                        rfl

theorem cell23_2664604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2664604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664604 prefixEnd_2664604 := by exact prefixLift 2664604
  have htrace : WordTrace (prefixWord ++ tailWord_2664604) baseStart_2664604 baseEnd_2664604 := by
    simpa [prefixWord, tailWord_2664604, baseEnd_2664604] using wordTrace_append hprefix tailTrace_2664604
  have hstable : (prefixWord ++ tailWord_2664604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664604).length < 2 ^ (prefixWord ++ tailWord_2664604).sum := by decide
  have hdescent : baseEnd_2664604 < baseStart_2664604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664631 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 1, 5]
def baseStart_2664631 : Nat := 118140960795 + 2664631 * 2 ^ 59
def prefixEnd_2664631 : Nat := 4983230072969 + 3 ^ 40 * 2664631 * 2
def baseEnd_2664631 : Nat := 456078823290223117552697

theorem tailTrace_2664631 : CollatzResearch.WordTrace tailWord_2664631 prefixEnd_2664631 456078823290223117552697 := by
  unfold tailWord_2664631
  simp only [CollatzResearch.WordTrace]
  refine ⟨97187076809504444588921747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64791384539669629725947831 97187076809504444588921747)
  ·
    refine ⟨145780615214256666883382621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97187076809504444588921747 145780615214256666883382621)
    ·
      refine ⟨54667730705346250081268483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145780615214256666883382621 54667730705346250081268483)
      ·
        refine ⟨82001596058019375121902725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54667730705346250081268483 82001596058019375121902725)
        ·
          refine ⟨15375299260878632835356761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82001596058019375121902725 15375299260878632835356761)
          ·
            refine ⟨11531474445658974626517571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15375299260878632835356761 11531474445658974626517571)
            ·
              refine ⟨17297211668488461939776357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11531474445658974626517571 17297211668488461939776357)
              ·
                refine ⟨3243227187841586613708067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17297211668488461939776357 3243227187841586613708067)
                ·
                  refine ⟨4864840781762379920562101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243227187841586613708067 4864840781762379920562101)
                  ·
                    refine ⟨456078823290223117552697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4864840781762379920562101 456078823290223117552697)
                    ·
                      rfl

theorem cell23_2664631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_2664631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664631 prefixEnd_2664631 := by exact prefixLift 2664631
  have htrace : WordTrace (prefixWord ++ tailWord_2664631) baseStart_2664631 baseEnd_2664631 := by
    simpa [prefixWord, tailWord_2664631, baseEnd_2664631] using wordTrace_append hprefix tailTrace_2664631
  have hstable : (prefixWord ++ tailWord_2664631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664631).length < 2 ^ (prefixWord ++ tailWord_2664631).sum := by decide
  have hdescent : baseEnd_2664631 < baseStart_2664631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664645 : List Nat := [1, 3, 1, 1, 1, 1, 7, 3, 1, 1, 3]
def baseStart_2664645 : Nat := 118140960795 + 2664645 * 2 ^ 59
def prefixEnd_2664645 : Nat := 4983230072969 + 3 ^ 40 * 2664645 * 2
def baseEnd_2664645 : Nat := 1368243658599832297883027

theorem tailTrace_2664645 : CollatzResearch.WordTrace tailWord_2664645 prefixEnd_2664645 1368243658599832297883027 := by
  unfold tailWord_2664645
  simp only [CollatzResearch.WordTrace]
  refine ⟨97187587431453724979931389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64791724954302483319954259 97187587431453724979931389)
  ·
    refine ⟨36445345286795146867474271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97187587431453724979931389 36445345286795146867474271)
    ·
      refine ⟨54668017930192720301211407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36445345286795146867474271 54668017930192720301211407)
      ·
        refine ⟨82002026895289080451817111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54668017930192720301211407 82002026895289080451817111)
        ·
          refine ⟨123003040342933620677725667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82002026895289080451817111 123003040342933620677725667)
          ·
            refine ⟨184504560514400431016588501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123003040342933620677725667 184504560514400431016588501)
            ·
              refine ⟨4324325637056260101951293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 184504560514400431016588501 4324325637056260101951293)
              ·
                refine ⟨1621622113896097538231735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4324325637056260101951293 1621622113896097538231735)
                ·
                  refine ⟨2432433170844146307347603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621622113896097538231735 2432433170844146307347603)
                  ·
                    refine ⟨3648649756266219461021405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2432433170844146307347603 3648649756266219461021405)
                    ·
                      refine ⟨1368243658599832297883027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3648649756266219461021405 1368243658599832297883027)
                      ·
                        rfl

theorem cell23_2664645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 1, 1, 3].length) (baseStart_2664645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664645 prefixEnd_2664645 := by exact prefixLift 2664645
  have htrace : WordTrace (prefixWord ++ tailWord_2664645) baseStart_2664645 baseEnd_2664645 := by
    simpa [prefixWord, tailWord_2664645, baseEnd_2664645] using wordTrace_append hprefix tailTrace_2664645
  have hstable : (prefixWord ++ tailWord_2664645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664645).length < 2 ^ (prefixWord ++ tailWord_2664645).sum := by decide
  have hdescent : baseEnd_2664645 < baseStart_2664645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664651 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 4]
def baseStart_2664651 : Nat := 118140960795 + 2664651 * 2 ^ 59
def prefixEnd_2664651 : Nat := 4983230072969 + 3 ^ 40 * 2664651 * 2
def baseEnd_2664651 : Nat := 1368246739483759274407999

theorem tailTrace_2664651 : CollatzResearch.WordTrace tailWord_2664651 prefixEnd_2664651 1368246739483759274407999 := by
  unfold tailWord_2664651
  simp only [CollatzResearch.WordTrace]
  refine ⟨97187806269431988004649807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64791870846287992003099871 97187806269431988004649807)
  ·
    refine ⟨145781709404147982006974711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97187806269431988004649807 145781709404147982006974711)
    ·
      refine ⟨218672564106221973010462067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145781709404147982006974711 218672564106221973010462067)
      ·
        refine ⟨328008846159332959515693101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218672564106221973010462067 328008846159332959515693101)
        ·
          refine ⟨123003317309749859818384913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328008846159332959515693101 123003317309749859818384913)
          ·
            refine ⟨92252487982312394863788685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123003317309749859818384913 92252487982312394863788685)
            ·
              refine ⟨34594682993367148073920757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92252487982312394863788685 34594682993367148073920757)
              ·
                refine ⟨3243251530628170131930071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34594682993367148073920757 3243251530628170131930071)
                ·
                  refine ⟨4864877295942255197895107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243251530628170131930071 4864877295942255197895107)
                  ·
                    refine ⟨7297315943913382796842661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4864877295942255197895107 7297315943913382796842661)
                    ·
                      refine ⟨1368246739483759274407999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7297315943913382796842661 1368246739483759274407999)
                      ·
                        rfl

theorem cell23_2664651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 4].length) (baseStart_2664651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664651 prefixEnd_2664651 := by exact prefixLift 2664651
  have htrace : WordTrace (prefixWord ++ tailWord_2664651) baseStart_2664651 baseEnd_2664651 := by
    simpa [prefixWord, tailWord_2664651, baseEnd_2664651] using wordTrace_append hprefix tailTrace_2664651
  have hstable : (prefixWord ++ tailWord_2664651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664651).length < 2 ^ (prefixWord ++ tailWord_2664651).sum := by decide
  have hdescent : baseEnd_2664651 < baseStart_2664651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664662 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2664662 : Nat := 118140960795 + 2664662 * 2 ^ 59
def prefixEnd_2664662 : Nat := 4983230072969 + 3 ^ 40 * 2664662 * 2
def baseEnd_2664662 : Nat := 1368252387770958731370449

theorem tailTrace_2664662 : CollatzResearch.WordTrace tailWord_2664662 prefixEnd_2664662 1368252387770958731370449 := by
  unfold tailWord_2664662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6074262967024508555206265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64792138314928091255533493 6074262967024508555206265)
  ·
    refine ⟨4555697225268381416404699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6074262967024508555206265 4555697225268381416404699)
    ·
      refine ⟨6833545837902572124607049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4555697225268381416404699 6833545837902572124607049)
      ·
        refine ⟨5125159378426929093455287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6833545837902572124607049 5125159378426929093455287)
        ·
          refine ⟨7687739067640393640182931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125159378426929093455287 7687739067640393640182931)
          ·
            refine ⟨11531608601460590460274397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7687739067640393640182931 11531608601460590460274397)
            ·
              refine ⟨4324353225547721422602899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11531608601460590460274397 4324353225547721422602899)
              ·
                refine ⟨6486529838321582133904349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4324353225547721422602899 6486529838321582133904349)
                ·
                  refine ⟨2432448689370593300214131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6486529838321582133904349 2432448689370593300214131)
                  ·
                    refine ⟨3648673034055889950321197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2432448689370593300214131 3648673034055889950321197)
                    ·
                      refine ⟨1368252387770958731370449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3648673034055889950321197 1368252387770958731370449)
                      ·
                        rfl

theorem cell23_2664662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2664662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664662 prefixEnd_2664662 := by exact prefixLift 2664662
  have htrace : WordTrace (prefixWord ++ tailWord_2664662) baseStart_2664662 baseEnd_2664662 := by
    simpa [prefixWord, tailWord_2664662, baseEnd_2664662] using wordTrace_append hprefix tailTrace_2664662
  have hstable : (prefixWord ++ tailWord_2664662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664662).length < 2 ^ (prefixWord ++ tailWord_2664662).sum := by decide
  have hdescent : baseEnd_2664662 < baseStart_2664662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664671 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 3]
def baseStart_2664671 : Nat := 118140960795 + 2664671 * 2 ^ 59
def prefixEnd_2664671 : Nat := 4983230072969 + 3 ^ 40 * 2664671 * 2
def baseEnd_2664671 : Nat := 1368257009096849196157907

theorem tailTrace_2664671 : CollatzResearch.WordTrace tailWord_2664671 prefixEnd_2664671 1368257009096849196157907 := by
  unfold tailWord_2664671
  simp only [CollatzResearch.WordTrace]
  refine ⟨97188535729359531420377867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64792357152906354280251911 97188535729359531420377867)
  ·
    refine ⟨145782803594039297130566801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97188535729359531420377867 145782803594039297130566801)
    ·
      refine ⟨109337102695529472847925101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145782803594039297130566801 109337102695529472847925101)
      ·
        refine ⟨41001413510823552317971913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109337102695529472847925101 41001413510823552317971913)
        ·
          refine ⟨30751060133117664238478935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41001413510823552317971913 30751060133117664238478935)
          ·
            refine ⟨46126590199676496357718403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30751060133117664238478935 46126590199676496357718403)
            ·
              refine ⟨69189885299514744536577605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46126590199676496357718403 69189885299514744536577605)
              ·
                refine ⟨12973103493659014600608301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69189885299514744536577605 12973103493659014600608301)
                ·
                  refine ⟨4864913810122130475228113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12973103493659014600608301 4864913810122130475228113)
                  ·
                    refine ⟨3648685357591597856421085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4864913810122130475228113 3648685357591597856421085)
                    ·
                      refine ⟨1368257009096849196157907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3648685357591597856421085 1368257009096849196157907)
                      ·
                        rfl

theorem cell23_2664671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_2664671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664671 prefixEnd_2664671 := by exact prefixLift 2664671
  have htrace : WordTrace (prefixWord ++ tailWord_2664671) baseStart_2664671 baseEnd_2664671 := by
    simpa [prefixWord, tailWord_2664671, baseEnd_2664671] using wordTrace_append hprefix tailTrace_2664671
  have hstable : (prefixWord ++ tailWord_2664671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664671).length < 2 ^ (prefixWord ++ tailWord_2664671).sum := by decide
  have hdescent : baseEnd_2664671 < baseStart_2664671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664705 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_2664705 : Nat := 118140960795 + 2664705 * 2 ^ 59
def prefixEnd_2664705 : Nat := 4983230072969 + 3 ^ 40 * 2664705 * 2
def baseEnd_2664705 : Nat := 1368274467439102063132751

theorem tailTrace_2664705 : CollatzResearch.WordTrace tailWord_2664705 prefixEnd_2664705 1368274467439102063132751 := by
  unfold tailWord_2664705
  simp only [CollatzResearch.WordTrace]
  refine ⟨97189775811236355227115569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64793183874157570151410379 97189775811236355227115569)
  ·
    refine ⟨72892331858427266420336677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97189775811236355227115569 72892331858427266420336677)
    ·
      refine ⟨13667312223455112453813127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72892331858427266420336677 13667312223455112453813127)
      ·
        refine ⟨20500968335182668680719691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13667312223455112453813127 20500968335182668680719691)
        ·
          refine ⟨30751452502774003021079537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20500968335182668680719691 30751452502774003021079537)
          ·
            refine ⟨23063589377080502265809653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30751452502774003021079537 23063589377080502265809653)
            ·
              refine ⟨2162211504101297087419655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23063589377080502265809653 2162211504101297087419655)
              ·
                refine ⟨3243317256151945631129483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162211504101297087419655 3243317256151945631129483)
                ·
                  refine ⟨4864975884227918446694225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243317256151945631129483 4864975884227918446694225)
                  ·
                    refine ⟨3648731913170938835020669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4864975884227918446694225 3648731913170938835020669)
                    ·
                      refine ⟨1368274467439102063132751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3648731913170938835020669 1368274467439102063132751)
                      ·
                        rfl

theorem cell23_2664705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_2664705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664705 prefixEnd_2664705 := by exact prefixLift 2664705
  have htrace : WordTrace (prefixWord ++ tailWord_2664705) baseStart_2664705 baseEnd_2664705 := by
    simpa [prefixWord, tailWord_2664705, baseEnd_2664705] using wordTrace_append hprefix tailTrace_2664705
  have hstable : (prefixWord ++ tailWord_2664705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664705).length < 2 ^ (prefixWord ++ tailWord_2664705).sum := by decide
  have hdescent : baseEnd_2664705 < baseStart_2664705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664728 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 5, 3, 2]
def baseStart_2664728 : Nat := 118140960795 + 2664728 * 2 ^ 59
def prefixEnd_2664728 : Nat := 4983230072969 + 3 ^ 40 * 2664728 * 2
def baseEnd_2664728 : Nat := 1368286277494155473145145

theorem tailTrace_2664728 : CollatzResearch.WordTrace tailWord_2664728 prefixEnd_2664728 1368286277494155473145145 := by
  unfold tailWord_2664728
  simp only [CollatzResearch.WordTrace]
  refine ⟨48595307345076515077601419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64793743126768686770135225 48595307345076515077601419)
  ·
    refine ⟨72892961017614772616402129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48595307345076515077601419 72892961017614772616402129)
    ·
      refine ⟨54669720763211079462301597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72892961017614772616402129 54669720763211079462301597)
      ·
        refine ⟨20501145286204154798363099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54669720763211079462301597 20501145286204154798363099)
        ·
          refine ⟨30751717929306232197544649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20501145286204154798363099 30751717929306232197544649)
          ·
            refine ⟨23063788446979674148158487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30751717929306232197544649 23063788446979674148158487)
            ·
              refine ⟨34595682670469511222237731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23063788446979674148158487 34595682670469511222237731)
              ·
                refine ⟨51893524005704266833356597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34595682670469511222237731 51893524005704266833356597)
                ·
                  refine ⟨4865017875534775015627181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51893524005704266833356597 4865017875534775015627181)
                  ·
                    refine ⟨1824381703325540630860193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4865017875534775015627181 1824381703325540630860193)
                    ·
                      refine ⟨1368286277494155473145145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824381703325540630860193 1368286277494155473145145)
                      ·
                        rfl

theorem cell23_2664728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_2664728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664728 prefixEnd_2664728 := by exact prefixLift 2664728
  have htrace : WordTrace (prefixWord ++ tailWord_2664728) baseStart_2664728 baseEnd_2664728 := by
    simpa [prefixWord, tailWord_2664728, baseEnd_2664728] using wordTrace_append hprefix tailTrace_2664728
  have hstable : (prefixWord ++ tailWord_2664728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664728).length < 2 ^ (prefixWord ++ tailWord_2664728).sum := by decide
  have hdescent : baseEnd_2664728 < baseStart_2664728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664735 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 2, 1, 3]
def baseStart_2664735 : Nat := 118140960795 + 2664735 * 2 ^ 59
def prefixEnd_2664735 : Nat := 4983230072969 + 3 ^ 40 * 2664735 * 2
def baseEnd_2664735 : Nat := 1368289871858736945757613

theorem tailTrace_2664735 : CollatzResearch.WordTrace tailWord_2664735 prefixEnd_2664735 1368289871858736945757613 := by
  unfold tailWord_2664735
  simp only [CollatzResearch.WordTrace]
  refine ⟨97190870001127670350707659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64793913334085113567138439 97190870001127670350707659)
  ·
    refine ⟨145786305001691505526061489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97190870001127670350707659 145786305001691505526061489)
    ·
      refine ⟨109339728751268629144546117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145786305001691505526061489 109339728751268629144546117)
      ·
        refine ⟨20501199140862867964602397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109339728751268629144546117 20501199140862867964602397)
        ·
          refine ⟨7687949677823575486725899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20501199140862867964602397 7687949677823575486725899)
          ·
            refine ⟨11531924516735363230088849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7687949677823575486725899 11531924516735363230088849)
            ·
              refine ⟨8648943387551522422566637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11531924516735363230088849 8648943387551522422566637)
              ·
                refine ⟨3243353770331820908462489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8648943387551522422566637 3243353770331820908462489)
                ·
                  refine ⟨2432515327748865681346867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3243353770331820908462489 2432515327748865681346867)
                  ·
                    refine ⟨3648772991623298522020301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2432515327748865681346867 3648772991623298522020301)
                    ·
                      refine ⟨1368289871858736945757613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3648772991623298522020301 1368289871858736945757613)
                      ·
                        rfl

theorem cell23_2664735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_2664735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664735 prefixEnd_2664735 := by exact prefixLift 2664735
  have htrace : WordTrace (prefixWord ++ tailWord_2664735) baseStart_2664735 baseEnd_2664735 := by
    simpa [prefixWord, tailWord_2664735, baseEnd_2664735] using wordTrace_append hprefix tailTrace_2664735
  have hstable : (prefixWord ++ tailWord_2664735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664735).length < 2 ^ (prefixWord ++ tailWord_2664735).sum := by decide
  have hdescent : baseEnd_2664735 < baseStart_2664735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664762 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2]
def baseStart_2664762 : Nat := 118140960795 + 2664762 * 2 ^ 59
def prefixEnd_2664762 : Nat := 4983230072969 + 3 ^ 40 * 2664762 * 2
def baseEnd_2664762 : Nat := 1368303735836408340119989

theorem tailTrace_2664762 : CollatzResearch.WordTrace tailWord_2664762 prefixEnd_2664762 1368303735836408340119989 := by
  unfold tailWord_2664762
  simp only [CollatzResearch.WordTrace]
  refine ⟨24297963693007463490485135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64794569848019902641293693 24297963693007463490485135)
  ·
    refine ⟨36446945539511195235727703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24297963693007463490485135 36446945539511195235727703)
    ·
      refine ⟨54670418309266792853591555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36446945539511195235727703 54670418309266792853591555)
      ·
        refine ⟨82005627463900189280387333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54670418309266792853591555 82005627463900189280387333)
        ·
          refine ⟨15376055149481285490072625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82005627463900189280387333 15376055149481285490072625)
          ·
            refine ⟨11532041362110964117554469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15376055149481285490072625 11532041362110964117554469)
            ·
              refine ⟨2162257755395805772041463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11532041362110964117554469 2162257755395805772041463)
              ·
                refine ⟨3243386633093708658062195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162257755395805772041463 3243386633093708658062195)
                ·
                  refine ⟨4865079949640562987093293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243386633093708658062195 4865079949640562987093293)
                  ·
                    refine ⟨1824404981115211120159985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4865079949640562987093293 1824404981115211120159985)
                    ·
                      refine ⟨1368303735836408340119989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824404981115211120159985 1368303735836408340119989)
                      ·
                        rfl

theorem cell23_2664762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_2664762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664762 prefixEnd_2664762 := by exact prefixLift 2664762
  have htrace : WordTrace (prefixWord ++ tailWord_2664762) baseStart_2664762 baseEnd_2664762 := by
    simpa [prefixWord, tailWord_2664762, baseEnd_2664762] using wordTrace_append hprefix tailTrace_2664762
  have hstable : (prefixWord ++ tailWord_2664762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664762).length < 2 ^ (prefixWord ++ tailWord_2664762).sum := by decide
  have hdescent : baseEnd_2664762 < baseStart_2664762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664769 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2664769 : Nat := 118140960795 + 2664769 * 2 ^ 59
def prefixEnd_2664769 : Nat := 4983230072969 + 3 ^ 40 * 2664769 * 2
def baseEnd_2664769 : Nat := 1368307330200989812732457

theorem tailTrace_2664769 : CollatzResearch.WordTrace tailWord_2664769 prefixEnd_2664769 1368307330200989812732457 := by
  unfold tailWord_2664769
  simp only [CollatzResearch.WordTrace]
  refine ⟨97192110083004494157445361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64794740055336329438296907 97192110083004494157445361)
  ·
    refine ⟨72894082562253370618084021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97192110083004494157445361 72894082562253370618084021)
    ·
      refine ⟨6833820240211253495445377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72894082562253370618084021 6833820240211253495445377)
      ·
        refine ⟨5125365180158440121584033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6833820240211253495445377 5125365180158440121584033)
        ·
          refine ⟨3844023885118830091188025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5125365180158440121584033 3844023885118830091188025)
          ·
            refine ⟨2883017913839122568391019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3844023885118830091188025 2883017913839122568391019)
            ·
              refine ⟨4324526870758683852586529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883017913839122568391019 4324526870758683852586529)
              ·
                refine ⟨3243395153069012889439897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4324526870758683852586529 3243395153069012889439897)
                ·
                  refine ⟨2432546364801759667079923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3243395153069012889439897 2432546364801759667079923)
                  ·
                    refine ⟨3648819547202639500619885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2432546364801759667079923 3648819547202639500619885)
                    ·
                      refine ⟨1368307330200989812732457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3648819547202639500619885 1368307330200989812732457)
                      ·
                        rfl

theorem cell23_2664769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2664769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664769 prefixEnd_2664769 := by exact prefixLift 2664769
  have htrace : WordTrace (prefixWord ++ tailWord_2664769) baseStart_2664769 baseEnd_2664769 := by
    simpa [prefixWord, tailWord_2664769, baseEnd_2664769] using wordTrace_append hprefix tailTrace_2664769
  have hstable : (prefixWord ++ tailWord_2664769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664769).length < 2 ^ (prefixWord ++ tailWord_2664769).sum := by decide
  have hdescent : baseEnd_2664769 < baseStart_2664769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664771 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 4]
def baseStart_2664771 : Nat := 118140960795 + 2664771 * 2 ^ 59
def prefixEnd_2664771 : Nat := 4983230072969 + 3 ^ 40 * 2664771 * 2
def baseEnd_2664771 : Nat := 1368308357162298804907447

theorem tailTrace_2664771 : CollatzResearch.WordTrace tailWord_2664771 prefixEnd_2664771 1368308357162298804907447 := by
  unfold tailWord_2664771
  simp only [CollatzResearch.WordTrace]
  refine ⟨97192183028997248499018167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64794788685998165666012111 97192183028997248499018167)
  ·
    refine ⟨145788274543495872748527251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97192183028997248499018167 145788274543495872748527251)
    ·
      refine ⟨218682411815243809122790877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145788274543495872748527251 218682411815243809122790877)
      ·
        refine ⟨82005904430716428421046579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218682411815243809122790877 82005904430716428421046579)
        ·
          refine ⟨123008856646074642631569869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82005904430716428421046579 123008856646074642631569869)
          ·
            refine ⟨46128321242277990986838701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123008856646074642631569869 46128321242277990986838701)
            ·
              refine ⟨17298120465854246620064513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46128321242277990986838701 17298120465854246620064513)
              ·
                refine ⟨12973590349390684965048385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17298120465854246620064513 12973590349390684965048385)
                ·
                  refine ⟨9730192762043013723786289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12973590349390684965048385 9730192762043013723786289)
                  ·
                    refine ⟨7297644571532260292839717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9730192762043013723786289 7297644571532260292839717)
                    ·
                      refine ⟨1368308357162298804907447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7297644571532260292839717 1368308357162298804907447)
                      ·
                        rfl

theorem cell23_2664771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_2664771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664771 prefixEnd_2664771 := by exact prefixLift 2664771
  have htrace : WordTrace (prefixWord ++ tailWord_2664771) baseStart_2664771 baseEnd_2664771 := by
    simpa [prefixWord, tailWord_2664771, baseEnd_2664771] using wordTrace_append hprefix tailTrace_2664771
  have hstable : (prefixWord ++ tailWord_2664771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664771).length < 2 ^ (prefixWord ++ tailWord_2664771).sum := by decide
  have hdescent : baseEnd_2664771 < baseStart_2664771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664775 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 4, 2, 2]
def baseStart_2664775 : Nat := 118140960795 + 2664775 * 2 ^ 59
def prefixEnd_2664775 : Nat := 4983230072969 + 3 ^ 40 * 2664775 * 2
def baseEnd_2664775 : Nat := 1368310411084916789257429

theorem tailTrace_2664775 : CollatzResearch.WordTrace tailWord_2664775 prefixEnd_2664775 1368310411084916789257429 := by
  unfold tailWord_2664775
  simp only [CollatzResearch.WordTrace]
  refine ⟨97192328920982757182163779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64794885947321838121442519 97192328920982757182163779)
  ·
    refine ⟨145788493381474135773245669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97192328920982757182163779 145788493381474135773245669)
    ·
      refine ⟨27335342509026400457483563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145788493381474135773245669 27335342509026400457483563)
      ·
        refine ⟨41003013763539600686225345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27335342509026400457483563 41003013763539600686225345)
        ·
          refine ⟨30752260322654700514669009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41003013763539600686225345 30752260322654700514669009)
          ·
            refine ⟨23064195241991025386001757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30752260322654700514669009 23064195241991025386001757)
            ·
              refine ⟨8649073215746634519750659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23064195241991025386001757 8649073215746634519750659)
              ·
                refine ⟨12973609823619951779625989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8649073215746634519750659 12973609823619951779625989)
                ·
                  refine ⟨2432551841928740958679873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12973609823619951779625989 2432551841928740958679873)
                  ·
                    refine ⟨1824413881446555719009905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2432551841928740958679873 1824413881446555719009905)
                    ·
                      refine ⟨1368310411084916789257429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824413881446555719009905 1368310411084916789257429)
                      ·
                        rfl

theorem cell23_2664775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_2664775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664775 prefixEnd_2664775 := by exact prefixLift 2664775
  have htrace : WordTrace (prefixWord ++ tailWord_2664775) baseStart_2664775 baseEnd_2664775 := by
    simpa [prefixWord, tailWord_2664775, baseEnd_2664775] using wordTrace_append hprefix tailTrace_2664775
  have hstable : (prefixWord ++ tailWord_2664775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664775).length < 2 ^ (prefixWord ++ tailWord_2664775).sum := by decide
  have hdescent : baseEnd_2664775 < baseStart_2664775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664788 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_2664788 : Nat := 118140960795 + 2664788 * 2 ^ 59
def prefixEnd_2664788 : Nat := 4983230072969 + 3 ^ 40 * 2664788 * 2
def baseEnd_2664788 : Nat := 1368317086333425238394869

theorem tailTrace_2664788 : CollatzResearch.WordTrace tailWord_2664788 prefixEnd_2664788 1368317086333425238394869 := by
  unfold tailWord_2664788
  simp only [CollatzResearch.WordTrace]
  refine ⟨48596401534967830201193509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64795202046623773601591345 48596401534967830201193509)
  ·
    refine ⟨9111825287806468162723783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48596401534967830201193509 9111825287806468162723783)
    ·
      refine ⟨13667737931709702244085675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9111825287806468162723783 13667737931709702244085675)
      ·
        refine ⟨20501606897564553366128513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13667737931709702244085675 20501606897564553366128513)
        ·
          refine ⟨15376205173173415024596385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20501606897564553366128513 15376205173173415024596385)
          ·
            refine ⟨11532153879880061268447289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15376205173173415024596385 11532153879880061268447289)
            ·
              refine ⟨8649115409910045951335467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11532153879880061268447289 8649115409910045951335467)
              ·
                refine ⟨12973673114865068927003201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8649115409910045951335467 12973673114865068927003201)
                ·
                  refine ⟨9730254836148801695252401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12973673114865068927003201 9730254836148801695252401)
                  ·
                    refine ⟨7297691127111601271439301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9730254836148801695252401 7297691127111601271439301)
                    ·
                      refine ⟨1368317086333425238394869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7297691127111601271439301 1368317086333425238394869)
                      ·
                        rfl

theorem cell23_2664788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_2664788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664788 prefixEnd_2664788 := by exact prefixLift 2664788
  have htrace : WordTrace (prefixWord ++ tailWord_2664788) baseStart_2664788 baseEnd_2664788 := by
    simpa [prefixWord, tailWord_2664788, baseEnd_2664788] using wordTrace_append hprefix tailTrace_2664788
  have hstable : (prefixWord ++ tailWord_2664788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664788).length < 2 ^ (prefixWord ++ tailWord_2664788).sum := by decide
  have hdescent : baseEnd_2664788 < baseStart_2664788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664862 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2664862 : Nat := 118140960795 + 2664862 * 2 ^ 59
def prefixEnd_2664862 : Nat := 4983230072969 + 3 ^ 40 * 2664862 * 2
def baseEnd_2664862 : Nat := 456118361300619316289843

theorem tailTrace_2664862 : CollatzResearch.WordTrace tailWord_2664862 prefixEnd_2664862 456118361300619316289843 := by
  unfold tailWord_2664862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12149437758958446380072605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64797001381111714027053893 12149437758958446380072605)
  ·
    refine ⟨4556039159609417392527227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12149437758958446380072605 4556039159609417392527227)
    ·
      refine ⟨6834058739414126088790841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4556039159609417392527227 6834058739414126088790841)
      ·
        refine ⟨5125544054560594566593131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6834058739414126088790841 5125544054560594566593131)
        ·
          refine ⟨7688316081840891849889697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125544054560594566593131 7688316081840891849889697)
          ·
            refine ⟨5766237061380668887417273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7688316081840891849889697 5766237061380668887417273)
            ·
              refine ⟨4324677796035501665562955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5766237061380668887417273 4324677796035501665562955)
              ·
                refine ⟨6487016694053252498344433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4324677796035501665562955 6487016694053252498344433)
                ·
                  refine ⟨4865262520539939373758325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6487016694053252498344433 4865262520539939373758325)
                  ·
                    refine ⟨456118361300619316289843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4865262520539939373758325 456118361300619316289843)
                    ·
                      rfl

theorem cell23_2664862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2664862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664862 prefixEnd_2664862 := by exact prefixLift 2664862
  have htrace : WordTrace (prefixWord ++ tailWord_2664862) baseStart_2664862 baseEnd_2664862 := by
    simpa [prefixWord, tailWord_2664862, baseEnd_2664862] using wordTrace_append hprefix tailTrace_2664862
  have hstable : (prefixWord ++ tailWord_2664862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664862).length < 2 ^ (prefixWord ++ tailWord_2664862).sum := by decide
  have hdescent : baseEnd_2664862 < baseStart_2664862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664868 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_2664868 : Nat := 118140960795 + 2664868 * 2 ^ 59
def prefixEnd_2664868 : Nat := 4983230072969 + 3 ^ 40 * 2664868 * 2
def baseEnd_2664868 : Nat := 1368358164785784925394501

theorem tailTrace_2664868 : CollatzResearch.WordTrace tailWord_2664868 prefixEnd_2664868 1368358164785784925394501 := by
  unfold tailWord_2664868
  simp only [CollatzResearch.WordTrace]
  refine ⟨48597860454822917032649629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64797147273097222710199505 48597860454822917032649629)
  ·
    refine ⟨18224197670558593887243611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48597860454822917032649629 18224197670558593887243611)
    ·
      refine ⟨27336296505837890830865417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18224197670558593887243611 27336296505837890830865417)
      ·
        refine ⟨20502222379378418123149063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27336296505837890830865417 20502222379378418123149063)
        ·
          refine ⟨30753333569067627184723595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20502222379378418123149063 30753333569067627184723595)
          ·
            refine ⟨46130000353601440777085393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30753333569067627184723595 46130000353601440777085393)
            ·
              refine ⟨34597500265201080582814045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46130000353601440777085393 34597500265201080582814045)
              ·
                refine ⟨12974062599450405218555267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34597500265201080582814045 12974062599450405218555267)
                ·
                  refine ⟨19461093899175607827832901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12974062599450405218555267 19461093899175607827832901)
                  ·
                    refine ⟨3648955106095426467718669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19461093899175607827832901 3648955106095426467718669)
                    ·
                      refine ⟨1368358164785784925394501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3648955106095426467718669 1368358164785784925394501)
                      ·
                        rfl

theorem cell23_2664868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_2664868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664868 prefixEnd_2664868 := by exact prefixLift 2664868
  have htrace : WordTrace (prefixWord ++ tailWord_2664868) baseStart_2664868 baseEnd_2664868 := by
    simpa [prefixWord, tailWord_2664868, baseEnd_2664868] using wordTrace_append hprefix tailTrace_2664868
  have hstable : (prefixWord ++ tailWord_2664868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664868).length < 2 ^ (prefixWord ++ tailWord_2664868).sum := by decide
  have hdescent : baseEnd_2664868 < baseStart_2664868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664911 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_2664911 : Nat := 118140960795 + 2664911 * 2 ^ 59
def prefixEnd_2664911 : Nat := 4983230072969 + 3 ^ 40 * 2664911 * 2
def baseEnd_2664911 : Nat := 1368380244453928257156803

theorem tailTrace_2664911 : CollatzResearch.WordTrace tailWord_2664911 prefixEnd_2664911 1368380244453928257156803 := by
  unfold tailWord_2664911
  simp only [CollatzResearch.WordTrace]
  refine ⟨97197289248490052409114587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64798192832326701606076391 97197289248490052409114587)
  ·
    refine ⟨145795933872735078613671881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97197289248490052409114587 145795933872735078613671881)
    ·
      refine ⟨109346950404551308960253911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145795933872735078613671881 109346950404551308960253911)
      ·
        refine ⟨164020425606826963440380867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109346950404551308960253911 164020425606826963440380867)
        ·
          refine ⟨246030638410240445160571301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164020425606826963440380867 246030638410240445160571301)
          ·
            refine ⟨46130744701920083467607119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246030638410240445160571301 46130744701920083467607119)
            ·
              refine ⟨69196117052880125201410679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46130744701920083467607119 69196117052880125201410679)
              ·
                refine ⟨103794175579320187802116019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69196117052880125201410679 103794175579320187802116019)
                ·
                  refine ⟨155691263368980281703174029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103794175579320187802116019 155691263368980281703174029)
                  ·
                    refine ⟨58384223763367605638690261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155691263368980281703174029 58384223763367605638690261)
                    ·
                      refine ⟨1368380244453928257156803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58384223763367605638690261 1368380244453928257156803)
                      ·
                        rfl

theorem cell23_2664911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_2664911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664911 prefixEnd_2664911 := by exact prefixLift 2664911
  have htrace : WordTrace (prefixWord ++ tailWord_2664911) baseStart_2664911 baseEnd_2664911 := by
    simpa [prefixWord, tailWord_2664911, baseEnd_2664911] using wordTrace_append hprefix tailTrace_2664911
  have hstable : (prefixWord ++ tailWord_2664911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664911).length < 2 ^ (prefixWord ++ tailWord_2664911).sum := by decide
  have hdescent : baseEnd_2664911 < baseStart_2664911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664935 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 1, 5]
def baseStart_2664935 : Nat := 118140960795 + 2664935 * 2 ^ 59
def prefixEnd_2664935 : Nat := 4983230072969 + 3 ^ 40 * 2664935 * 2
def baseEnd_2664935 : Nat := 456130855996545387752231

theorem tailTrace_2664935 : CollatzResearch.WordTrace tailWord_2664935 prefixEnd_2664935 456130855996545387752231 := by
  unfold tailWord_2664935
  simp only [CollatzResearch.WordTrace]
  refine ⟨97198164600403104507988259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64798776400268736338658839 97198164600403104507988259)
  ·
    refine ⟨145797246900604656761982389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97198164600403104507988259 145797246900604656761982389)
    ·
      refine ⟨13668491896931686571435849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145797246900604656761982389 13668491896931686571435849)
      ·
        refine ⟨10251368922698764928576887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13668491896931686571435849 10251368922698764928576887)
        ·
          refine ⟨15377053384048147392865331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10251368922698764928576887 15377053384048147392865331)
          ·
            refine ⟨23065580076072221089297997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15377053384048147392865331 23065580076072221089297997)
            ·
              refine ⟨8649592528527082908486749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23065580076072221089297997 8649592528527082908486749)
              ·
                refine ⟨3243597198197656090682531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8649592528527082908486749 3243597198197656090682531)
                ·
                  refine ⟨4865395797296484136023797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243597198197656090682531 4865395797296484136023797)
                  ·
                    refine ⟨456130855996545387752231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4865395797296484136023797 456130855996545387752231)
                    ·
                      rfl

theorem cell23_2664935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_2664935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664935 prefixEnd_2664935 := by exact prefixLift 2664935
  have htrace : WordTrace (prefixWord ++ tailWord_2664935) baseStart_2664935 baseEnd_2664935 := by
    simpa [prefixWord, tailWord_2664935, baseEnd_2664935] using wordTrace_append hprefix tailTrace_2664935
  have hstable : (prefixWord ++ tailWord_2664935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664935).length < 2 ^ (prefixWord ++ tailWord_2664935).sum := by decide
  have hdescent : baseEnd_2664935 < baseStart_2664935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664965 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_2664965 : Nat := 118140960795 + 2664965 * 2 ^ 59
def prefixEnd_2664965 : Nat := 4983230072969 + 3 ^ 40 * 2664965 * 2
def baseEnd_2664965 : Nat := 456135990803090348627185

theorem tailTrace_2664965 : CollatzResearch.WordTrace tailWord_2664965 prefixEnd_2664965 456135990803090348627185 := by
  unfold tailWord_2664965
  simp only [CollatzResearch.WordTrace]
  refine ⟨97199258790294419631580349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64799505860196279754386899 97199258790294419631580349)
  ·
    refine ⟨36449722046360407361842631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97199258790294419631580349 36449722046360407361842631)
    ·
      refine ⟨54674583069540611042763947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36449722046360407361842631 54674583069540611042763947)
      ·
        refine ⟨82011874604310916564145921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54674583069540611042763947 82011874604310916564145921)
        ·
          refine ⟨61508905953233187423109441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82011874604310916564145921 61508905953233187423109441)
          ·
            refine ⟨46131679464924890567332081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61508905953233187423109441 46131679464924890567332081)
            ·
              refine ⟨34598759598693667925499061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46131679464924890567332081 34598759598693667925499061)
              ·
                refine ⟨3243633712377531368015537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34598759598693667925499061 3243633712377531368015537)
                ·
                  refine ⟨2432725284283148526011653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3243633712377531368015537 2432725284283148526011653)
                  ·
                    refine ⟨456135990803090348627185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2432725284283148526011653 456135990803090348627185)
                    ·
                      rfl

theorem cell23_2664965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_2664965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664965 prefixEnd_2664965 := by exact prefixLift 2664965
  have htrace : WordTrace (prefixWord ++ tailWord_2664965) baseStart_2664965 baseEnd_2664965 := by
    simpa [prefixWord, tailWord_2664965, baseEnd_2664965] using wordTrace_append hprefix tailTrace_2664965
  have hstable : (prefixWord ++ tailWord_2664965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664965).length < 2 ^ (prefixWord ++ tailWord_2664965).sum := by decide
  have hdescent : baseEnd_2664965 < baseStart_2664965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664972 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 1, 1, 4]
def baseStart_2664972 : Nat := 118140960795 + 2664972 * 2 ^ 59
def prefixEnd_2664972 : Nat := 4983230072969 + 3 ^ 40 * 2664972 * 2
def baseEnd_2664972 : Nat := 1368411566773852518494023

theorem tailTrace_2664972 : CollatzResearch.WordTrace tailWord_2664972 prefixEnd_2664972 1368411566773852518494023 := by
  unfold tailWord_2664972
  simp only [CollatzResearch.WordTrace]
  refine ⟨48599757050634529913542585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64799676067512706551390113 48599757050634529913542585)
  ·
    refine ⟨36449817787975897435156939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48599757050634529913542585 36449817787975897435156939)
    ·
      refine ⟨54674726681963846152735409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36449817787975897435156939 54674726681963846152735409)
      ·
        refine ⟨41006045011472884614551557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54674726681963846152735409 41006045011472884614551557)
        ·
          refine ⟨7688633439651165865228417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41006045011472884614551557 7688633439651165865228417)
          ·
            refine ⟨5766475079738374398921313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7688633439651165865228417 5766475079738374398921313)
            ·
              refine ⟨4324856309803780799190985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5766475079738374398921313 4324856309803780799190985)
              ·
                refine ⟨3243642232352835599393239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4324856309803780799190985 3243642232352835599393239)
                ·
                  refine ⟨4865463348529253399089859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243642232352835599393239 4865463348529253399089859)
                  ·
                    refine ⟨7298195022793880098634789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4865463348529253399089859 7298195022793880098634789)
                    ·
                      refine ⟨1368411566773852518494023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7298195022793880098634789 1368411566773852518494023)
                      ·
                        rfl

theorem cell23_2664972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_2664972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664972 prefixEnd_2664972 := by exact prefixLift 2664972
  have htrace : WordTrace (prefixWord ++ tailWord_2664972) baseStart_2664972 baseEnd_2664972 := by
    simpa [prefixWord, tailWord_2664972, baseEnd_2664972] using wordTrace_append hprefix tailTrace_2664972
  have hstable : (prefixWord ++ tailWord_2664972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664972).length < 2 ^ (prefixWord ++ tailWord_2664972).sum := by decide
  have hdescent : baseEnd_2664972 < baseStart_2664972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664975 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 1, 2, 3]
def baseStart_2664975 : Nat := 118140960795 + 2664975 * 2 ^ 59
def prefixEnd_2664975 : Nat := 4983230072969 + 3 ^ 40 * 2664975 * 2
def baseEnd_2664975 : Nat := 1368413107215816006756509

theorem tailTrace_2664975 : CollatzResearch.WordTrace tailWord_2664975 prefixEnd_2664975 1368413107215816006756509 := by
  unfold tailWord_2664975
  simp only [CollatzResearch.WordTrace]
  refine ⟨97199623520258191339444379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64799749013505460892962919 97199623520258191339444379)
  ·
    refine ⟨145799435280387287009166569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97199623520258191339444379 145799435280387287009166569)
    ·
      refine ⟨109349576460290465256874927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145799435280387287009166569 109349576460290465256874927)
      ·
        refine ⟨164024364690435697885312391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109349576460290465256874927 164024364690435697885312391)
        ·
          refine ⟨246036547035653546827968587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164024364690435697885312391 246036547035653546827968587)
          ·
            refine ⟨369054820553480320241952881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246036547035653546827968587 369054820553480320241952881)
            ·
              refine ⟨276791115415110240181464661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369054820553480320241952881 276791115415110240181464661)
              ·
                refine ⟨3243645883770823127126539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 276791115415110240181464661 3243645883770823127126539)
                ·
                  refine ⟨4865468825656234690689809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243645883770823127126539 4865468825656234690689809)
                  ·
                    refine ⟨3649101619242176018017357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4865468825656234690689809 3649101619242176018017357)
                    ·
                      refine ⟨1368413107215816006756509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3649101619242176018017357 1368413107215816006756509)
                      ·
                        rfl

theorem cell23_2664975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 2, 3].length) (baseStart_2664975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664975 prefixEnd_2664975 := by exact prefixLift 2664975
  have htrace : WordTrace (prefixWord ++ tailWord_2664975) baseStart_2664975 baseEnd_2664975 := by
    simpa [prefixWord, tailWord_2664975, baseEnd_2664975] using wordTrace_append hprefix tailTrace_2664975
  have hstable : (prefixWord ++ tailWord_2664975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664975).length < 2 ^ (prefixWord ++ tailWord_2664975).sum := by decide
  have hdescent : baseEnd_2664975 < baseStart_2664975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664983 : List Nat := [1, 1, 3, 6, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2664983 : Nat := 118140960795 + 2664983 * 2 ^ 59
def prefixEnd_2664983 : Nat := 4983230072969 + 3 ^ 40 * 2664983 * 2
def baseEnd_2664983 : Nat := 1368417215061051975456473

theorem tailTrace_2664983 : CollatzResearch.WordTrace tailWord_2664983 prefixEnd_2664983 1368417215061051975456473 := by
  unfold tailWord_2664983
  simp only [CollatzResearch.WordTrace]
  refine ⟨97199915304229208705735603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64799943536152805803823735 97199915304229208705735603)
  ·
    refine ⟨145799872956343813058603405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97199915304229208705735603 145799872956343813058603405)
    ·
      refine ⟨54674952358628929896976277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145799872956343813058603405 54674952358628929896976277)
      ·
        refine ⟨2562888391810731088920763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54674952358628929896976277 2562888391810731088920763)
        ·
          refine ⟨3844332587716096633381145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562888391810731088920763 3844332587716096633381145)
          ·
            refine ⟨2883249440787072475035859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3844332587716096633381145 2883249440787072475035859)
            ·
              refine ⟨4324874161180608712553789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883249440787072475035859 4324874161180608712553789)
              ·
                refine ⟨1621827810442728267207671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4324874161180608712553789 1621827810442728267207671)
                ·
                  refine ⟨2432741715664092400811507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621827810442728267207671 2432741715664092400811507)
                  ·
                    refine ⟨3649112573496138601217261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2432741715664092400811507 3649112573496138601217261)
                    ·
                      refine ⟨1368417215061051975456473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3649112573496138601217261 1368417215061051975456473)
                      ·
                        rfl

theorem cell23_2664983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2664983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664983 prefixEnd_2664983 := by exact prefixLift 2664983
  have htrace : WordTrace (prefixWord ++ tailWord_2664983) baseStart_2664983 baseEnd_2664983 := by
    simpa [prefixWord, tailWord_2664983, baseEnd_2664983] using wordTrace_append hprefix tailTrace_2664983
  have hstable : (prefixWord ++ tailWord_2664983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664983).length < 2 ^ (prefixWord ++ tailWord_2664983).sum := by decide
  have hdescent : baseEnd_2664983 < baseStart_2664983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2664992 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2664992 : Nat := 118140960795 + 2664992 * 2 ^ 59
def prefixEnd_2664992 : Nat := 4983230072969 + 3 ^ 40 * 2664992 * 2
def baseEnd_2664992 : Nat := 1368421836386942440243931

theorem tailTrace_2664992 : CollatzResearch.WordTrace tailWord_2664992 prefixEnd_2664992 1368421836386942440243931 := by
  unfold tailWord_2664992
  simp only [CollatzResearch.WordTrace]
  refine ⟨48600121780598301621406615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64800162374131068828542153 48600121780598301621406615)
  ·
    refine ⟨72900182670897452432109923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48600121780598301621406615 72900182670897452432109923)
    ·
      refine ⟨109350274006346178648164885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72900182670897452432109923 109350274006346178648164885)
      ·
        refine ⟨5125794094047477124132729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109350274006346178648164885 5125794094047477124132729)
        ·
          refine ⟨3844345570535607843099547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5125794094047477124132729 3844345570535607843099547)
          ·
            refine ⟨5766518355803411764649321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844345570535607843099547 5766518355803411764649321)
            ·
              refine ⟨4324888766852558823486991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5766518355803411764649321 4324888766852558823486991)
              ·
                refine ⟨6487333150278838235230487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4324888766852558823486991 6487333150278838235230487)
                ·
                  refine ⟨9730999725418257352845731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6487333150278838235230487 9730999725418257352845731)
                  ·
                    refine ⟨14596499588127386029268597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9730999725418257352845731 14596499588127386029268597)
                    ·
                      refine ⟨1368421836386942440243931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14596499588127386029268597 1368421836386942440243931)
                      ·
                        rfl

theorem cell23_2664992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2664992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2664992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2664992 prefixEnd_2664992 := by exact prefixLift 2664992
  have htrace : WordTrace (prefixWord ++ tailWord_2664992) baseStart_2664992 baseEnd_2664992 := by
    simpa [prefixWord, tailWord_2664992, baseEnd_2664992] using wordTrace_append hprefix tailTrace_2664992
  have hstable : (prefixWord ++ tailWord_2664992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2664992).length < 2 ^ (prefixWord ++ tailWord_2664992).sum := by decide
  have hdescent : baseEnd_2664992 < baseStart_2664992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2664992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665079 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 2, 2, 2]
def baseStart_2665079 : Nat := 118140960795 + 2665079 * 2 ^ 59
def prefixEnd_2665079 : Nat := 4983230072969 + 3 ^ 40 * 2665079 * 2
def baseEnd_2665079 : Nat := 1368466509203883599856031

theorem tailTrace_2665079 : CollatzResearch.WordTrace tailWord_2665079 prefixEnd_2665079 1368466509203883599856031 := by
  unfold tailWord_2665079
  simp only [CollatzResearch.WordTrace]
  refine ⟨97203416711881417101230291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64802277807920944734153527 97203416711881417101230291)
  ·
    refine ⟨145805125067822125651845437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97203416711881417101230291 145805125067822125651845437)
    ·
      refine ⟨54676921900433297119442039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145805125067822125651845437 54676921900433297119442039)
      ·
        refine ⟨82015382850649945679163059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54676921900433297119442039 82015382850649945679163059)
        ·
          refine ⟨123023074275974918518744589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82015382850649945679163059 123023074275974918518744589)
          ·
            refine ⟨46133652853490594444529221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123023074275974918518744589 46133652853490594444529221)
            ·
              refine ⟨8650059910029486458349229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46133652853490594444529221 8650059910029486458349229)
              ·
                refine ⟨3243772466261057421880961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8650059910029486458349229 3243772466261057421880961)
                ·
                  refine ⟨2432829349695793066410721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3243772466261057421880961 2432829349695793066410721)
                  ·
                    refine ⟨1824622012271844799808041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2432829349695793066410721 1824622012271844799808041)
                    ·
                      refine ⟨1368466509203883599856031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824622012271844799808041 1368466509203883599856031)
                      ·
                        rfl

theorem cell23_2665079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_2665079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665079 prefixEnd_2665079 := by exact prefixLift 2665079
  have htrace : WordTrace (prefixWord ++ tailWord_2665079) baseStart_2665079 baseEnd_2665079 := by
    simpa [prefixWord, tailWord_2665079, baseEnd_2665079] using wordTrace_append hprefix tailTrace_2665079
  have hstable : (prefixWord ++ tailWord_2665079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665079).length < 2 ^ (prefixWord ++ tailWord_2665079).sum := by decide
  have hdescent : baseEnd_2665079 < baseStart_2665079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665095 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_2665095 : Nat := 118140960795 + 2665095 * 2 ^ 59
def prefixEnd_2665095 : Nat := 4983230072969 + 3 ^ 40 * 2665095 * 2
def baseEnd_2665095 : Nat := 1368474724894355537255957

theorem tailTrace_2665095 : CollatzResearch.WordTrace tailWord_2665095 prefixEnd_2665095 1368474724894355537255957 := by
  unfold tailWord_2665095
  simp only [CollatzResearch.WordTrace]
  refine ⟨97204000279823451833812739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64802666853215634555875159 97204000279823451833812739)
  ·
    refine ⟨145806000419735177750719109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97204000279823451833812739 145806000419735177750719109)
    ·
      refine ⟨27338625078700345828259833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145806000419735177750719109 27338625078700345828259833)
      ·
        refine ⟨20503968809025259371194875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27338625078700345828259833 20503968809025259371194875)
        ·
          refine ⟨30755953213537889056792313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20503968809025259371194875 30755953213537889056792313)
          ·
            refine ⟨23066964910153416792594235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30755953213537889056792313 23066964910153416792594235)
            ·
              refine ⟨34600447365230125188891353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23066964910153416792594235 34600447365230125188891353)
              ·
                refine ⟨25950335523922593891668515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34600447365230125188891353 25950335523922593891668515)
                ·
                  refine ⟨38925503285883890837502773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25950335523922593891668515 38925503285883890837502773)
                  ·
                    refine ⟨3649265933051614766015885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38925503285883890837502773 3649265933051614766015885)
                    ·
                      refine ⟨1368474724894355537255957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3649265933051614766015885 1368474724894355537255957)
                      ·
                        rfl

theorem cell23_2665095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_2665095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665095 prefixEnd_2665095 := by exact prefixLift 2665095
  have htrace : WordTrace (prefixWord ++ tailWord_2665095) baseStart_2665095 baseEnd_2665095 := by
    simpa [prefixWord, tailWord_2665095, baseEnd_2665095] using wordTrace_append hprefix tailTrace_2665095
  have hstable : (prefixWord ++ tailWord_2665095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665095).length < 2 ^ (prefixWord ++ tailWord_2665095).sum := by decide
  have hdescent : baseEnd_2665095 < baseStart_2665095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665130 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2665130 : Nat := 118140960795 + 2665130 * 2 ^ 59
def prefixEnd_2665130 : Nat := 4983230072969 + 3 ^ 40 * 2665130 * 2
def baseEnd_2665130 : Nat := 1368492696717262900318297

theorem tailTrace_2665130 : CollatzResearch.WordTrace tailWord_2665130 prefixEnd_2665130 1368492696717262900318297 := by
  unfold tailWord_2665130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24301319208674163202834211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64803517889797768540891229 24301319208674163202834211)
  ·
    refine ⟨36451978813011244804251317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24301319208674163202834211 36451978813011244804251317)
    ·
      refine ⟨3417373013719804200398561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36451978813011244804251317 3417373013719804200398561)
      ·
        refine ⟨2563029760289853150298921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3417373013719804200398561 2563029760289853150298921)
        ·
          refine ⟨1922272320217389862724191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2563029760289853150298921 1922272320217389862724191)
          ·
            refine ⟨2883408480326084794086287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922272320217389862724191 2883408480326084794086287)
            ·
              refine ⟨4325112720489127191129431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883408480326084794086287 4325112720489127191129431)
              ·
                refine ⟨6487669080733690786694147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4325112720489127191129431 6487669080733690786694147)
                ·
                  refine ⟨9731503621100536180041221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6487669080733690786694147 9731503621100536180041221)
                  ·
                    refine ⟨1824656928956350533757729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9731503621100536180041221 1824656928956350533757729)
                    ·
                      refine ⟨1368492696717262900318297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824656928956350533757729 1368492696717262900318297)
                      ·
                        rfl

theorem cell23_2665130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2665130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665130 prefixEnd_2665130 := by exact prefixLift 2665130
  have htrace : WordTrace (prefixWord ++ tailWord_2665130) baseStart_2665130 baseEnd_2665130 := by
    simpa [prefixWord, tailWord_2665130, baseEnd_2665130] using wordTrace_append hprefix tailTrace_2665130
  have hstable : (prefixWord ++ tailWord_2665130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665130).length < 2 ^ (prefixWord ++ tailWord_2665130).sum := by decide
  have hdescent : baseEnd_2665130 < baseStart_2665130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665135 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_2665135 : Nat := 118140960795 + 2665135 * 2 ^ 59
def prefixEnd_2665135 : Nat := 4983230072969 + 3 ^ 40 * 2665135 * 2
def baseEnd_2665135 : Nat := 1368495264120535380755773

theorem tailTrace_2665135 : CollatzResearch.WordTrace tailWord_2665135 prefixEnd_2665135 1368495264120535380755773 := by
  unfold tailWord_2665135
  simp only [CollatzResearch.WordTrace]
  refine ⟨97205459199678538665268859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64803639466452359110179239 97205459199678538665268859)
  ·
    refine ⟨145808188799517807997903289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97205459199678538665268859 145808188799517807997903289)
    ·
      refine ⟨109356141599638355998427467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145808188799517807997903289 109356141599638355998427467)
      ·
        refine ⟨164034212399457533997641201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109356141599638355998427467 164034212399457533997641201)
        ·
          refine ⟨123025659299593150498230901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164034212399457533997641201 123025659299593150498230901)
          ·
            refine ⟨11533655559336857859209147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123025659299593150498230901 11533655559336857859209147)
            ·
              refine ⟨17300483339005286788813721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11533655559336857859209147 17300483339005286788813721)
              ·
                refine ⟨12975362504253965091610291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17300483339005286788813721 12975362504253965091610291)
                ·
                  refine ⟨19463043756380947637415437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12975362504253965091610291 19463043756380947637415437)
                  ·
                    refine ⟨7298641408642855364030789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19463043756380947637415437 7298641408642855364030789)
                    ·
                      refine ⟨1368495264120535380755773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7298641408642855364030789 1368495264120535380755773)
                      ·
                        rfl

theorem cell23_2665135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_2665135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665135 prefixEnd_2665135 := by exact prefixLift 2665135
  have htrace : WordTrace (prefixWord ++ tailWord_2665135) baseStart_2665135 baseEnd_2665135 := by
    simpa [prefixWord, tailWord_2665135, baseEnd_2665135] using wordTrace_append hprefix tailTrace_2665135
  have hstable : (prefixWord ++ tailWord_2665135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665135).length < 2 ^ (prefixWord ++ tailWord_2665135).sum := by decide
  have hdescent : baseEnd_2665135 < baseStart_2665135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665153 : List Nat := [1, 2, 6, 2, 1, 2, 1, 3, 5]
def baseStart_2665153 : Nat := 118140960795 + 2665153 * 2 ^ 59
def prefixEnd_2665153 : Nat := 4983230072969 + 3 ^ 40 * 2665153 * 2
def baseEnd_2665153 : Nat := 152056056308035145592299

theorem tailTrace_2665153 : CollatzResearch.WordTrace tailWord_2665153 prefixEnd_2665153 152056056308035145592299 := by
  unfold tailWord_2665153
  simp only [CollatzResearch.WordTrace]
  refine ⟨97206115713613327739424113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64804077142408885159616075 97206115713613327739424113)
  ·
    refine ⟨72904586785209995804568085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97206115713613327739424113 72904586785209995804568085)
    ·
      refine ⟨3417402505556718553339129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72904586785209995804568085 3417402505556718553339129)
      ·
        refine ⟨2563051879167538915004347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3417402505556718553339129 2563051879167538915004347)
        ·
          refine ⟨3844577818751308372506521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2563051879167538915004347 3844577818751308372506521)
          ·
            refine ⟨2883433364063481279379891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3844577818751308372506521 2883433364063481279379891)
            ·
              refine ⟨4325150046095221919069837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883433364063481279379891 4325150046095221919069837)
              ·
                refine ⟨1621931267285708219651189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4325150046095221919069837 1621931267285708219651189)
                ·
                  refine ⟨152056056308035145592299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1621931267285708219651189 152056056308035145592299)
                  ·
                    rfl

theorem cell23_2665153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 5].length) (baseStart_2665153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665153 prefixEnd_2665153 := by exact prefixLift 2665153
  have htrace : WordTrace (prefixWord ++ tailWord_2665153) baseStart_2665153 baseEnd_2665153 := by
    simpa [prefixWord, tailWord_2665153, baseEnd_2665153] using wordTrace_append hprefix tailTrace_2665153
  have hstable : (prefixWord ++ tailWord_2665153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665153).length < 2 ^ (prefixWord ++ tailWord_2665153).sum := by decide
  have hdescent : baseEnd_2665153 < baseStart_2665153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665175 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 8]
def baseStart_2665175 : Nat := 118140960795 + 2665175 * 2 ^ 59
def prefixEnd_2665175 : Nat := 4983230072969 + 3 ^ 40 * 2665175 * 2
def baseEnd_2665175 : Nat := 152057311482968358250621

theorem tailTrace_2665175 : CollatzResearch.WordTrace tailWord_2665175 prefixEnd_2665175 152057311482968358250621 := by
  unfold tailWord_2665175
  simp only [CollatzResearch.WordTrace]
  refine ⟨97206918119533625496724979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64804612079689083664483319 97206918119533625496724979)
  ·
    refine ⟨145810377179300438245087469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97206918119533625496724979 145810377179300438245087469)
    ·
      refine ⟨54678891442237664341907801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145810377179300438245087469 54678891442237664341907801)
      ·
        refine ⟨41009168581678248256430851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54678891442237664341907801 41009168581678248256430851)
        ·
          refine ⟨61513752872517372384646277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41009168581678248256430851 61513752872517372384646277)
          ·
            refine ⟨11533828663597007322121177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61513752872517372384646277 11533828663597007322121177)
            ·
              refine ⟨8650371497697755491590883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11533828663597007322121177 8650371497697755491590883)
              ·
                refine ⟨12975557246546633237386325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8650371497697755491590883 12975557246546633237386325)
                ·
                  refine ⟨152057311482968358250621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12975557246546633237386325 152057311482968358250621)
                  ·
                    rfl

theorem cell23_2665175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 8].length) (baseStart_2665175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665175 prefixEnd_2665175 := by exact prefixLift 2665175
  have htrace : WordTrace (prefixWord ++ tailWord_2665175) baseStart_2665175 baseEnd_2665175 := by
    simpa [prefixWord, tailWord_2665175, baseEnd_2665175] using wordTrace_append hprefix tailTrace_2665175
  have hstable : (prefixWord ++ tailWord_2665175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665175).length < 2 ^ (prefixWord ++ tailWord_2665175).sum := by decide
  have hdescent : baseEnd_2665175 < baseStart_2665175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665235 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 3, 6]
def baseStart_2665235 : Nat := 118140960795 + 2665235 * 2 ^ 59
def prefixEnd_2665235 : Nat := 4983230072969 + 3 ^ 40 * 2665235 * 2
def baseEnd_2665235 : Nat := 456182204061994996501771

theorem tailTrace_2665235 : CollatzResearch.WordTrace tailWord_2665235 prefixEnd_2665235 456182204061994996501771 := by
  unfold tailWord_2665235
  simp only [CollatzResearch.WordTrace]
  refine ⟨97209106499316255743909159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64806070999544170495939439 97209106499316255743909159)
  ·
    refine ⟨145813659748974383615863739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97209106499316255743909159 145813659748974383615863739)
    ·
      refine ⟨218720489623461575423795609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145813659748974383615863739 218720489623461575423795609)
      ·
        refine ⟨164040367217596181567846707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218720489623461575423795609 164040367217596181567846707)
        ·
          refine ⟨246060550826394272351770061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164040367217596181567846707 246060550826394272351770061)
          ·
            refine ⟨92272706559897852131913773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246060550826394272351770061 92272706559897852131913773)
            ·
              refine ⟨34602264959961694549467665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92272706559897852131913773 34602264959961694549467665)
              ·
                refine ⟨25951698719971270912100749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34602264959961694549467665 25951698719971270912100749)
                ·
                  refine ⟨9731887019989226592037781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25951698719971270912100749 9731887019989226592037781)
                  ·
                    refine ⟨456182204061994996501771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9731887019989226592037781 456182204061994996501771)
                    ·
                      rfl

theorem cell23_2665235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 6].length) (baseStart_2665235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665235 prefixEnd_2665235 := by exact prefixLift 2665235
  have htrace : WordTrace (prefixWord ++ tailWord_2665235) baseStart_2665235 baseEnd_2665235 := by
    simpa [prefixWord, tailWord_2665235, baseEnd_2665235] using wordTrace_append hprefix tailTrace_2665235
  have hstable : (prefixWord ++ tailWord_2665235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665235).length < 2 ^ (prefixWord ++ tailWord_2665235).sum := by decide
  have hdescent : baseEnd_2665235 < baseStart_2665235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665242 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_2665242 : Nat := 118140960795 + 2665242 * 2 ^ 59
def prefixEnd_2665242 : Nat := 4983230072969 + 3 ^ 40 * 2665242 * 2
def baseEnd_2665242 : Nat := 1368550206550566462117781

theorem tailTrace_2665242 : CollatzResearch.WordTrace tailWord_2665242 prefixEnd_2665242 1368550206550566462117781 := by
  unfold tailWord_2665242
  simp only [CollatzResearch.WordTrace]
  refine ⟨24302340452572723984853495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64806241206860597292942653 24302340452572723984853495)
  ·
    refine ⟨36453510678859085977280243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24302340452572723984853495 36453510678859085977280243)
    ·
      refine ⟨54680266018288628965920365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36453510678859085977280243 54680266018288628965920365)
      ·
        refine ⟨20505099756858235862220137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54680266018288628965920365 20505099756858235862220137)
        ·
          refine ⟨15378824817643676896665103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20505099756858235862220137 15378824817643676896665103)
          ·
            refine ⟨23068237226465515344997655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15378824817643676896665103 23068237226465515344997655)
            ·
              refine ⟨34602355839698273017496483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23068237226465515344997655 34602355839698273017496483)
              ·
                refine ⟨51903533759547409526244725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34602355839698273017496483 51903533759547409526244725)
                ·
                  refine ⟨4865956289957569643085443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51903533759547409526244725 4865956289957569643085443)
                  ·
                    refine ⟨7298934434936354464628165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4865956289957569643085443 7298934434936354464628165)
                    ·
                      refine ⟨1368550206550566462117781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7298934434936354464628165 1368550206550566462117781)
                      ·
                        rfl

theorem cell23_2665242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_2665242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665242 prefixEnd_2665242 := by exact prefixLift 2665242
  have htrace : WordTrace (prefixWord ++ tailWord_2665242) baseStart_2665242 baseEnd_2665242 := by
    simpa [prefixWord, tailWord_2665242, baseEnd_2665242] using wordTrace_append hprefix tailTrace_2665242
  have hstable : (prefixWord ++ tailWord_2665242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665242).length < 2 ^ (prefixWord ++ tailWord_2665242).sum := by decide
  have hdescent : baseEnd_2665242 < baseStart_2665242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665259 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 5, 2, 2]
def baseStart_2665259 : Nat := 118140960795 + 2665259 * 2 ^ 59
def prefixEnd_2665259 : Nat := 4983230072969 + 3 ^ 40 * 2665259 * 2
def baseEnd_2665259 : Nat := 1368558935721692895605203

theorem tailTrace_2665259 : CollatzResearch.WordTrace tailWord_2665259 prefixEnd_2665259 1368558935721692895605203 := by
  unfold tailWord_2665259
  simp only [CollatzResearch.WordTrace]
  refine ⟨97209981851229307842782831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64806654567486205228521887 97209981851229307842782831)
  ·
    refine ⟨145814972776843961764174247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97209981851229307842782831 145814972776843961764174247)
    ·
      refine ⟨218722459165265942646261371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145814972776843961764174247 218722459165265942646261371)
      ·
        refine ⟨328083688747898913969392057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218722459165265942646261371 328083688747898913969392057)
        ·
          refine ⟨246062766560924185477044043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328083688747898913969392057 246062766560924185477044043)
          ·
            refine ⟨369094149841386278215566065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246062766560924185477044043 369094149841386278215566065)
            ·
              refine ⟨276820612381039708661674549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369094149841386278215566065 276820612381039708661674549)
              ·
                refine ⟨25951932410722472687031989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276820612381039708661674549 25951932410722472687031989)
                ·
                  refine ⟨2432993663505231814409249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25951932410722472687031989 2432993663505231814409249)
                  ·
                    refine ⟨1824745247628923860806937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2432993663505231814409249 1824745247628923860806937)
                    ·
                      refine ⟨1368558935721692895605203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824745247628923860806937 1368558935721692895605203)
                      ·
                        rfl

theorem cell23_2665259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 2, 2].length) (baseStart_2665259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665259 prefixEnd_2665259 := by exact prefixLift 2665259
  have htrace : WordTrace (prefixWord ++ tailWord_2665259) baseStart_2665259 baseEnd_2665259 := by
    simpa [prefixWord, tailWord_2665259, baseEnd_2665259] using wordTrace_append hprefix tailTrace_2665259
  have hstable : (prefixWord ++ tailWord_2665259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665259).length < 2 ^ (prefixWord ++ tailWord_2665259).sum := by decide
  have hdescent : baseEnd_2665259 < baseStart_2665259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665272 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_2665272 : Nat := 118140960795 + 2665272 * 2 ^ 59
def prefixEnd_2665272 : Nat := 4983230072969 + 3 ^ 40 * 2665272 * 2
def baseEnd_2665272 : Nat := 1368565610970201344742643

theorem tailTrace_2665272 : CollatzResearch.WordTrace tailWord_2665272 prefixEnd_2665272 1368565610970201344742643 := by
  unfold tailWord_2665272
  simp only [CollatzResearch.WordTrace]
  refine ⟨48605228000091105531503035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64806970666788140708670713 48605228000091105531503035)
  ·
    refine ⟨72907842000136658297254553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48605228000091105531503035 72907842000136658297254553)
    ·
      refine ⟨54680881500102493722940915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72907842000136658297254553 54680881500102493722940915)
      ·
        refine ⟨82021322250153740584411373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54680881500102493722940915 82021322250153740584411373)
        ·
          refine ⟨30757995843807652719154265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82021322250153740584411373 30757995843807652719154265)
          ·
            refine ⟨23068496882855739539365699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30757995843807652719154265 23068496882855739539365699)
            ·
              refine ⟨34602745324283609309048549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23068496882855739539365699 34602745324283609309048549)
              ·
                refine ⟨6488014748303176745446603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34602745324283609309048549 6488014748303176745446603)
                ·
                  refine ⟨9732022122454765118169905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488014748303176745446603 9732022122454765118169905)
                  ·
                    refine ⟨7299016591841073838627429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9732022122454765118169905 7299016591841073838627429)
                    ·
                      refine ⟨1368565610970201344742643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7299016591841073838627429 1368565610970201344742643)
                      ·
                        rfl

theorem cell23_2665272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_2665272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665272 prefixEnd_2665272 := by exact prefixLift 2665272
  have htrace : WordTrace (prefixWord ++ tailWord_2665272) baseStart_2665272 baseEnd_2665272 := by
    simpa [prefixWord, tailWord_2665272, baseEnd_2665272] using wordTrace_append hprefix tailTrace_2665272
  have hstable : (prefixWord ++ tailWord_2665272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665272).length < 2 ^ (prefixWord ++ tailWord_2665272).sum := by decide
  have hdescent : baseEnd_2665272 < baseStart_2665272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665370 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2]
def baseStart_2665370 : Nat := 118140960795 + 2665370 * 2 ^ 59
def prefixEnd_2665370 : Nat := 4983230072969 + 3 ^ 40 * 2665370 * 2
def baseEnd_2665370 : Nat := 1368615932074341961317193

theorem tailTrace_2665370 : CollatzResearch.WordTrace tailWord_2665370 prefixEnd_2665370 1368615932074341961317193 := by
  unfold tailWord_2665370
  simp only [CollatzResearch.WordTrace]
  refine ⟨24303507588456793450018391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64809353569218115866715709 24303507588456793450018391)
  ·
    refine ⟨36455261382685190175027587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24303507588456793450018391 36455261382685190175027587)
    ·
      refine ⟨54682892074027785262541381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36455261382685190175027587 54682892074027785262541381)
      ·
        refine ⟨10253042263880209736726509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54682892074027785262541381 10253042263880209736726509)
        ·
          refine ⟨3844890848955078651272441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10253042263880209736726509 3844890848955078651272441)
          ·
            refine ⟨2883668136716308988454331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3844890848955078651272441 2883668136716308988454331)
            ·
              refine ⟨4325502205074463482681497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883668136716308988454331 4325502205074463482681497)
              ·
                refine ⟨3244126653805847612011123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4325502205074463482681497 3244126653805847612011123)
                ·
                  refine ⟨4866189980708771418016685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244126653805847612011123 4866189980708771418016685)
                  ·
                    refine ⟨1824821242765789281756257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4866189980708771418016685 1824821242765789281756257)
                    ·
                      refine ⟨1368615932074341961317193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824821242765789281756257 1368615932074341961317193)
                      ·
                        rfl

theorem cell23_2665370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_2665370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665370 prefixEnd_2665370 := by exact prefixLift 2665370
  have htrace : WordTrace (prefixWord ++ tailWord_2665370) baseStart_2665370 baseEnd_2665370 := by
    simpa [prefixWord, tailWord_2665370, baseEnd_2665370] using wordTrace_append hprefix tailTrace_2665370
  have hstable : (prefixWord ++ tailWord_2665370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665370).length < 2 ^ (prefixWord ++ tailWord_2665370).sum := by decide
  have hdescent : baseEnd_2665370 < baseStart_2665370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665383 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_2665383 : Nat := 118140960795 + 2665383 * 2 ^ 59
def prefixEnd_2665383 : Nat := 4983230072969 + 3 ^ 40 * 2665383 * 2
def baseEnd_2665383 : Nat := 1368622607322850410454633

theorem tailTrace_2665383 : CollatzResearch.WordTrace tailWord_2665383 prefixEnd_2665383 1368622607322850410454633 := by
  unfold tailWord_2665383
  simp only [CollatzResearch.WordTrace]
  refine ⟨97214504502780077020296803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64809669668520051346864535 97214504502780077020296803)
  ·
    refine ⟨145821756754170115530445205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97214504502780077020296803 145821756754170115530445205)
    ·
      refine ⟨6835394847851724165489619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145821756754170115530445205 6835394847851724165489619)
      ·
        refine ⟨10253092271777586248234429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6835394847851724165489619 10253092271777586248234429)
        ·
          refine ⟨3844909601916594843087911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10253092271777586248234429 3844909601916594843087911)
          ·
            refine ⟨5767364402874892264631867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844909601916594843087911 5767364402874892264631867)
            ·
              refine ⟨8651046604312338396947801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767364402874892264631867 8651046604312338396947801)
              ·
                refine ⟨6488284953234253797710851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8651046604312338396947801 6488284953234253797710851)
                ·
                  refine ⟨9732427429851380696566277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488284953234253797710851 9732427429851380696566277)
                  ·
                    refine ⟨1824830143097133880606177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9732427429851380696566277 1824830143097133880606177)
                    ·
                      refine ⟨1368622607322850410454633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824830143097133880606177 1368622607322850410454633)
                      ·
                        rfl

theorem cell23_2665383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_2665383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665383 prefixEnd_2665383 := by exact prefixLift 2665383
  have htrace : WordTrace (prefixWord ++ tailWord_2665383) baseStart_2665383 baseEnd_2665383 := by
    simpa [prefixWord, tailWord_2665383, baseEnd_2665383] using wordTrace_append hprefix tailTrace_2665383
  have hstable : (prefixWord ++ tailWord_2665383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665383).length < 2 ^ (prefixWord ++ tailWord_2665383).sum := by decide
  have hdescent : baseEnd_2665383 < baseStart_2665383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665406 : List Nat := [4, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_2665406 : Nat := 118140960795 + 2665406 * 2 ^ 59
def prefixEnd_2665406 : Nat := 4983230072969 + 3 ^ 40 * 2665406 * 2
def baseEnd_2665406 : Nat := 152070490819767091163003

theorem tailTrace_2665406 : CollatzResearch.WordTrace tailWord_2665406 prefixEnd_2665406 152070490819767091163003 := by
  unfold tailWord_2665406
  simp only [CollatzResearch.WordTrace]
  refine ⟨12151917922712093993548009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64810228921131167965589381 12151917922712093993548009)
  ·
    refine ⟨9113938442034070495161007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12151917922712093993548009 9113938442034070495161007)
    ·
      refine ⟨13670907663051105742741511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9113938442034070495161007 13670907663051105742741511)
      ·
        refine ⟨20506361494576658614112267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13670907663051105742741511 20506361494576658614112267)
        ·
          refine ⟨30759542241864987921168401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20506361494576658614112267 30759542241864987921168401)
          ·
            refine ⟨23069656681398740940876301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30759542241864987921168401 23069656681398740940876301)
            ·
              refine ⟨8651121255524527852828613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23069656681398740940876301 8651121255524527852828613)
              ·
                refine ⟨1622085235410848972405365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8651121255524527852828613 1622085235410848972405365)
                ·
                  refine ⟨152070490819767091163003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1622085235410848972405365 152070490819767091163003)
                  ·
                    rfl

theorem cell23_2665406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_2665406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665406 prefixEnd_2665406 := by exact prefixLift 2665406
  have htrace : WordTrace (prefixWord ++ tailWord_2665406) baseStart_2665406 baseEnd_2665406 := by
    simpa [prefixWord, tailWord_2665406, baseEnd_2665406] using wordTrace_append hprefix tailTrace_2665406
  have hstable : (prefixWord ++ tailWord_2665406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665406).length < 2 ^ (prefixWord ++ tailWord_2665406).sum := by decide
  have hdescent : baseEnd_2665406 < baseStart_2665406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665416 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_2665416 : Nat := 118140960795 + 2665416 * 2 ^ 59
def prefixEnd_2665416 : Nat := 4983230072969 + 3 ^ 40 * 2665416 * 2
def baseEnd_2665416 : Nat := 1368639552184448781341981

theorem tailTrace_2665416 : CollatzResearch.WordTrace tailWord_2665416 prefixEnd_2665416 1368639552184448781341981 := by
  unfold tailWord_2665416
  simp only [CollatzResearch.WordTrace]
  refine ⟨48607854055830261828124051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64810472074440349104165401 48607854055830261828124051)
  ·
    refine ⟨72911781083745392742186077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48607854055830261828124051 72911781083745392742186077)
    ·
      refine ⟨27341917906404522278319779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72911781083745392742186077 27341917906404522278319779)
      ·
        refine ⟨41012876859606783417479669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27341917906404522278319779 41012876859606783417479669)
        ·
          refine ⟨3844957205588135945388719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41012876859606783417479669 3844957205588135945388719)
          ·
            refine ⟨5767435808382203918083079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844957205588135945388719 5767435808382203918083079)
            ·
              refine ⟨8651153712573305877124619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767435808382203918083079 8651153712573305877124619)
              ·
                refine ⟨12976730568859958815686929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8651153712573305877124619 12976730568859958815686929)
                ·
                  refine ⟨9732547926644969111765197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12976730568859958815686929 9732547926644969111765197)
                  ·
                    refine ⟨3649705472491863416911949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9732547926644969111765197 3649705472491863416911949)
                    ·
                      refine ⟨1368639552184448781341981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3649705472491863416911949 1368639552184448781341981)
                      ·
                        rfl

theorem cell23_2665416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_2665416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665416 prefixEnd_2665416 := by exact prefixLift 2665416
  have htrace : WordTrace (prefixWord ++ tailWord_2665416) baseStart_2665416 baseEnd_2665416 := by
    simpa [prefixWord, tailWord_2665416, baseEnd_2665416] using wordTrace_append hprefix tailTrace_2665416
  have hstable : (prefixWord ++ tailWord_2665416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665416).length < 2 ^ (prefixWord ++ tailWord_2665416).sum := by decide
  have hdescent : baseEnd_2665416 < baseStart_2665416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665472 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_2665472 : Nat := 118140960795 + 2665472 * 2 ^ 59
def prefixEnd_2665472 : Nat := 4983230072969 + 3 ^ 40 * 2665472 * 2
def baseEnd_2665472 : Nat := 1368668307101100562241723

theorem tailTrace_2665472 : CollatzResearch.WordTrace tailWord_2665472 prefixEnd_2665472 1368668307101100562241723 := by
  unfold tailWord_2665472
  simp only [CollatzResearch.WordTrace]
  refine ⟨48608875299728822610143335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64811833732971763480191113 48608875299728822610143335)
  ·
    refine ⟨72913312949593233915215003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48608875299728822610143335 72913312949593233915215003)
    ·
      refine ⟨109369969424389850872822505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72913312949593233915215003 109369969424389850872822505)
      ·
        refine ⟨82027477068292388154616879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109369969424389850872822505 82027477068292388154616879)
        ·
          refine ⟨123041215602438582231925319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82027477068292388154616879 123041215602438582231925319)
          ·
            refine ⟨184561823403657873347887979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123041215602438582231925319 184561823403657873347887979)
            ·
              refine ⟨276842735105486810021831969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184561823403657873347887979 276842735105486810021831969)
              ·
                refine ⟨207632051329115107516373977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276842735105486810021831969 207632051329115107516373977)
                ·
                  refine ⟨155724038496836330637280483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207632051329115107516373977 155724038496836330637280483)
                  ·
                    refine ⟨233586057745254495955920725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 155724038496836330637280483 233586057745254495955920725)
                    ·
                      refine ⟨1368668307101100562241723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 233586057745254495955920725 1368668307101100562241723)
                      ·
                        rfl

theorem cell23_2665472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_2665472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665472 prefixEnd_2665472 := by exact prefixLift 2665472
  have htrace : WordTrace (prefixWord ++ tailWord_2665472) baseStart_2665472 baseEnd_2665472 := by
    simpa [prefixWord, tailWord_2665472, baseEnd_2665472] using wordTrace_append hprefix tailTrace_2665472
  have hstable : (prefixWord ++ tailWord_2665472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665472).length < 2 ^ (prefixWord ++ tailWord_2665472).sum := by decide
  have hdescent : baseEnd_2665472 < baseStart_2665472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665539 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 1, 6]
def baseStart_2665539 : Nat := 118140960795 + 2665539 * 2 ^ 59
def prefixEnd_2665539 : Nat := 4983230072969 + 3 ^ 40 * 2665539 * 2
def baseEnd_2665539 : Nat := 456234236768317266701305

theorem tailTrace_2665539 : CollatzResearch.WordTrace tailWord_2665539 prefixEnd_2665539 456234236768317266701305 := by
  unfold tailWord_2665539
  simp only [CollatzResearch.WordTrace]
  refine ⟨97220194290214915662975671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64813462860143277108650447 97220194290214915662975671)
  ·
    refine ⟨145830291435322373494463507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97220194290214915662975671 145830291435322373494463507)
    ·
      refine ⟨218745437152983560241695261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145830291435322373494463507 218745437152983560241695261)
      ·
        refine ⟨82029538932368835090635723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218745437152983560241695261 82029538932368835090635723)
        ·
          refine ⟨123044308398553252635953585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82029538932368835090635723 123044308398553252635953585)
          ·
            refine ⟨92283231298914939476965189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123044308398553252635953585 92283231298914939476965189)
            ·
              refine ⟨17303105868546551151930973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92283231298914939476965189 17303105868546551151930973)
              ·
                refine ⟨6488664700704956681974115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17303105868546551151930973 6488664700704956681974115)
                ·
                  refine ⟨9732997051057435022961173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488664700704956681974115 9732997051057435022961173)
                  ·
                    refine ⟨456234236768317266701305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9732997051057435022961173 456234236768317266701305)
                    ·
                      rfl

theorem cell23_2665539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 6].length) (baseStart_2665539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665539 prefixEnd_2665539 := by exact prefixLift 2665539
  have htrace : WordTrace (prefixWord ++ tailWord_2665539) baseStart_2665539 baseEnd_2665539 := by
    simpa [prefixWord, tailWord_2665539, baseEnd_2665539] using wordTrace_append hprefix tailTrace_2665539
  have hstable : (prefixWord ++ tailWord_2665539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665539).length < 2 ^ (prefixWord ++ tailWord_2665539).sum := by decide
  have hdescent : baseEnd_2665539 < baseStart_2665539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665543 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 1, 5]
def baseStart_2665543 : Nat := 118140960795 + 2665543 * 2 ^ 59
def prefixEnd_2665543 : Nat := 4983230072969 + 3 ^ 40 * 2665543 * 2
def baseEnd_2665543 : Nat := 456234921409189928151299

theorem tailTrace_2665543 : CollatzResearch.WordTrace tailWord_2665543 prefixEnd_2665543 456234921409189928151299 := by
  unfold tailWord_2665543
  simp only [CollatzResearch.WordTrace]
  refine ⟨97220340182200424346121283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64813560121466949564080855 97220340182200424346121283)
  ·
    refine ⟨145830510273300636519181925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97220340182200424346121283 145830510273300636519181925)
    ·
      refine ⟨27343220676243869347346611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145830510273300636519181925 27343220676243869347346611)
      ·
        refine ⟨41014831014365804021019917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27343220676243869347346611 41014831014365804021019917)
        ·
          refine ⟨15380561630387176507882469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41014831014365804021019917 15380561630387176507882469)
          ·
            refine ⟨2883855305697595595227963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15380561630387176507882469 2883855305697595595227963)
            ·
              refine ⟨4325782958546393392841945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883855305697595595227963 4325782958546393392841945)
              ·
                refine ⟨3244337218909795044631459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4325782958546393392841945 3244337218909795044631459)
                ·
                  refine ⟨4866505828364692566947189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244337218909795044631459 4866505828364692566947189)
                  ·
                    refine ⟨456234921409189928151299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4866505828364692566947189 456234921409189928151299)
                    ·
                      rfl

theorem cell23_2665543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_2665543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665543 prefixEnd_2665543 := by exact prefixLift 2665543
  have htrace : WordTrace (prefixWord ++ tailWord_2665543) baseStart_2665543 baseEnd_2665543 := by
    simpa [prefixWord, tailWord_2665543, baseEnd_2665543] using wordTrace_append hprefix tailTrace_2665543
  have hstable : (prefixWord ++ tailWord_2665543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665543).length < 2 ^ (prefixWord ++ tailWord_2665543).sum := by decide
  have hdescent : baseEnd_2665543 < baseStart_2665543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665546 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2]
def baseStart_2665546 : Nat := 118140960795 + 2665546 * 2 ^ 59
def prefixEnd_2665546 : Nat := 4983230072969 + 3 ^ 40 * 2665546 * 2
def baseEnd_2665546 : Nat := 1368706304669533272716383

theorem tailTrace_2665546 : CollatzResearch.WordTrace tailWord_2665546 prefixEnd_2665546 1368706304669533272716383 := by
  unfold tailWord_2665546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24305112400297388964620123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64813633067459703905653661 24305112400297388964620123)
  ·
    refine ⟨36457668600446083446930185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24305112400297388964620123 36457668600446083446930185)
    ·
      refine ⟨27343251450334562585197639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36457668600446083446930185 27343251450334562585197639)
      ·
        refine ⟨41014877175501843877796459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27343251450334562585197639 41014877175501843877796459)
        ·
          refine ⟨61522315763252765816694689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41014877175501843877796459 61522315763252765816694689)
          ·
            refine ⟨46141736822439574362521017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61522315763252765816694689 46141736822439574362521017)
            ·
              refine ⟨34606302616829680771890763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46141736822439574362521017 34606302616829680771890763)
              ·
                refine ⟨51909453925244521157836145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34606302616829680771890763 51909453925244521157836145)
                ·
                  refine ⟨38932090443933390868377109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51909453925244521157836145 38932090443933390868377109)
                  ·
                    refine ⟨1824941739559377696955177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38932090443933390868377109 1824941739559377696955177)
                    ·
                      refine ⟨1368706304669533272716383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824941739559377696955177 1368706304669533272716383)
                      ·
                        rfl

theorem cell23_2665546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_2665546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665546 prefixEnd_2665546 := by exact prefixLift 2665546
  have htrace : WordTrace (prefixWord ++ tailWord_2665546) baseStart_2665546 baseEnd_2665546 := by
    simpa [prefixWord, tailWord_2665546, baseEnd_2665546] using wordTrace_append hprefix tailTrace_2665546
  have hstable : (prefixWord ++ tailWord_2665546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665546).length < 2 ^ (prefixWord ++ tailWord_2665546).sum := by decide
  have hdescent : baseEnd_2665546 < baseStart_2665546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665556 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_2665556 : Nat := 118140960795 + 2665556 * 2 ^ 59
def prefixEnd_2665556 : Nat := 4983230072969 + 3 ^ 40 * 2665556 * 2
def baseEnd_2665556 : Nat := 456237146492026077863779

theorem tailTrace_2665556 : CollatzResearch.WordTrace tailWord_2665556 prefixEnd_2665556 456237146492026077863779 := by
  unfold tailWord_2665556
  simp only [CollatzResearch.WordTrace]
  refine ⟨48610407165576663783172261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64813876220768885044229681 48610407165576663783172261)
  ·
    refine ⟨9114451343545624459344799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48610407165576663783172261 9114451343545624459344799)
    ·
      refine ⟨13671677015318436689017199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9114451343545624459344799 13671677015318436689017199)
      ·
        refine ⟨20507515522977655033525799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13671677015318436689017199 20507515522977655033525799)
        ·
          refine ⟨30761273284466482550288699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20507515522977655033525799 30761273284466482550288699)
          ·
            refine ⟨46141909926699723825433049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30761273284466482550288699 46141909926699723825433049)
            ·
              refine ⟨34606432445024792869074787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46141909926699723825433049 34606432445024792869074787)
              ·
                refine ⟨51909648667537189303612181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34606432445024792869074787 51909648667537189303612181)
                ·
                  refine ⟨2433264781290805748606821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51909648667537189303612181 2433264781290805748606821)
                  ·
                    refine ⟨456237146492026077863779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433264781290805748606821 456237146492026077863779)
                    ·
                      rfl

theorem cell23_2665556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_2665556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665556 prefixEnd_2665556 := by exact prefixLift 2665556
  have htrace : WordTrace (prefixWord ++ tailWord_2665556) baseStart_2665556 baseEnd_2665556 := by
    simpa [prefixWord, tailWord_2665556, baseEnd_2665556] using wordTrace_append hprefix tailTrace_2665556
  have hstable : (prefixWord ++ tailWord_2665556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665556).length < 2 ^ (prefixWord ++ tailWord_2665556).sum := by decide
  have hdescent : baseEnd_2665556 < baseStart_2665556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665573 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_2665573 : Nat := 118140960795 + 2665573 * 2 ^ 59
def prefixEnd_2665573 : Nat := 4983230072969 + 3 ^ 40 * 2665573 * 2
def baseEnd_2665573 : Nat := 456240056215734889026253

theorem tailTrace_2665573 : CollatzResearch.WordTrace tailWord_2665573 prefixEnd_2665573 456240056215734889026253 := by
  unfold tailWord_2665573
  simp only [CollatzResearch.WordTrace]
  refine ⟨97221434372091739469713373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64814289581394492979808915 97221434372091739469713373)
  ·
    refine ⟨36458037889534402301142515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97221434372091739469713373 36458037889534402301142515)
    ·
      refine ⟨54687056834301603451713773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36458037889534402301142515 54687056834301603451713773)
      ·
        refine ⟨20507646312863101294392665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54687056834301603451713773 20507646312863101294392665)
        ·
          refine ⟨15380734734647325970794499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20507646312863101294392665 15380734734647325970794499)
          ·
            refine ⟨23071102101970988956191749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15380734734647325970794499 23071102101970988956191749)
            ·
              refine ⟨4325831644119560429285953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23071102101970988956191749 4325831644119560429285953)
              ·
                refine ⟨3244373733089670321964465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4325831644119560429285953 3244373733089670321964465)
                ·
                  refine ⟨2433280299817252741473349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3244373733089670321964465 2433280299817252741473349)
                  ·
                    refine ⟨456240056215734889026253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433280299817252741473349 456240056215734889026253)
                    ·
                      rfl

theorem cell23_2665573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_2665573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665573 prefixEnd_2665573 := by exact prefixLift 2665573
  have htrace : WordTrace (prefixWord ++ tailWord_2665573) baseStart_2665573 baseEnd_2665573 := by
    simpa [prefixWord, tailWord_2665573, baseEnd_2665573] using wordTrace_append hprefix tailTrace_2665573
  have hstable : (prefixWord ++ tailWord_2665573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665573).length < 2 ^ (prefixWord ++ tailWord_2665573).sum := by decide
  have hdescent : baseEnd_2665573 < baseStart_2665573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665593 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 4]
def baseStart_2665593 : Nat := 118140960795 + 2665593 * 2 ^ 59
def prefixEnd_2665593 : Nat := 4983230072969 + 3 ^ 40 * 2665593 * 2
def baseEnd_2665593 : Nat := 1368730438260294588828667

theorem tailTrace_2665593 : CollatzResearch.WordTrace tailWord_2665593 prefixEnd_2665593 1368730438260294588828667 := by
  unfold tailWord_2665593
  simp only [CollatzResearch.WordTrace]
  refine ⟨97222163832019282885441433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64814775888012855256960955 97222163832019282885441433)
  ·
    refine ⟨72916622874014462164081075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97222163832019282885441433 72916622874014462164081075)
    ·
      refine ⟨109374934311021693246121613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72916622874014462164081075 109374934311021693246121613)
      ·
        refine ⟨41015600366633134967295605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109374934311021693246121613 41015600366633134967295605)
        ·
          refine ⟨3845212534371856403183963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41015600366633134967295605 3845212534371856403183963)
          ·
            refine ⟨5767818801557784604775945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3845212534371856403183963 5767818801557784604775945)
            ·
              refine ⟨4325864101168338453581959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5767818801557784604775945 4325864101168338453581959)
              ·
                refine ⟨6488796151752507680372939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4325864101168338453581959 6488796151752507680372939)
                ·
                  refine ⟨9733194227628761520559409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488796151752507680372939 9733194227628761520559409)
                  ·
                    refine ⟨7299895670721571140419557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9733194227628761520559409 7299895670721571140419557)
                    ·
                      refine ⟨1368730438260294588828667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7299895670721571140419557 1368730438260294588828667)
                      ·
                        rfl

theorem cell23_2665593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_2665593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665593 prefixEnd_2665593 := by exact prefixLift 2665593
  have htrace : WordTrace (prefixWord ++ tailWord_2665593) baseStart_2665593 baseEnd_2665593 := by
    simpa [prefixWord, tailWord_2665593, baseEnd_2665593] using wordTrace_append hprefix tailTrace_2665593
  have hstable : (prefixWord ++ tailWord_2665593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665593).length < 2 ^ (prefixWord ++ tailWord_2665593).sum := by decide
  have hdescent : baseEnd_2665593 < baseStart_2665593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665614 : List Nat := [4, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2]
def baseStart_2665614 : Nat := 118140960795 + 2665614 * 2 ^ 59
def prefixEnd_2665614 : Nat := 4983230072969 + 3 ^ 40 * 2665614 * 2
def baseEnd_2665614 : Nat := 1368741221354039006666071

theorem tailTrace_2665614 : CollatzResearch.WordTrace tailWord_2665614 prefixEnd_2665614 1368741221354039006666071 := by
  unfold tailWord_2665614
  simp only [CollatzResearch.WordTrace]
  refine ⟨12152866220617900433994487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64815286509962135647970597 12152866220617900433994487)
  ·
    refine ⟨18229299330926850650991731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12152866220617900433994487 18229299330926850650991731)
    ·
      refine ⟨27343948996390275976487597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18229299330926850650991731 27343948996390275976487597)
      ·
        refine ⟨10253980873646353491182849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27343948996390275976487597 10253980873646353491182849)
        ·
          refine ⟨7690485655234765118387137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10253980873646353491182849 7690485655234765118387137)
          ·
            refine ⟨5767864241426073838790353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7690485655234765118387137 5767864241426073838790353)
            ·
              refine ⟨4325898181069555379092765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5767864241426073838790353 4325898181069555379092765)
              ·
                refine ⟨1622211817901083267159787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4325898181069555379092765 1622211817901083267159787)
                ·
                  refine ⟨2433317726851624900739681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622211817901083267159787 2433317726851624900739681)
                  ·
                    refine ⟨1824988295138718675554761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2433317726851624900739681 1824988295138718675554761)
                    ·
                      refine ⟨1368741221354039006666071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1824988295138718675554761 1368741221354039006666071)
                      ·
                        rfl

theorem cell23_2665614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_2665614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665614 prefixEnd_2665614 := by exact prefixLift 2665614
  have htrace : WordTrace (prefixWord ++ tailWord_2665614) baseStart_2665614 baseEnd_2665614 := by
    simpa [prefixWord, tailWord_2665614, baseEnd_2665614] using wordTrace_append hprefix tailTrace_2665614
  have hstable : (prefixWord ++ tailWord_2665614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665614).length < 2 ^ (prefixWord ++ tailWord_2665614).sum := by decide
  have hdescent : baseEnd_2665614 < baseStart_2665614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665654 : List Nat := [5, 1, 3, 2, 2, 1, 2, 7]
def baseStart_2665654 : Nat := 118140960795 + 2665654 * 2 ^ 59
def prefixEnd_2665654 : Nat := 4983230072969 + 3 ^ 40 * 2665654 * 2
def baseEnd_2665654 : Nat := 50694880021489587043181

theorem tailTrace_2665654 : CollatzResearch.WordTrace tailWord_2665654 prefixEnd_2665654 50694880021489587043181 := by
  unfold tailWord_2665654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6076524292799893143963251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64816259123198860202274677 6076524292799893143963251)
  ·
    refine ⟨9114786439199839715944877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6076524292799893143963251 9114786439199839715944877)
    ·
      refine ⟨3418044914699939893479329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9114786439199839715944877 3418044914699939893479329)
      ·
        refine ⟨2563533686024954920109497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3418044914699939893479329 2563533686024954920109497)
        ·
          refine ⟨1922650264518716190082123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2563533686024954920109497 1922650264518716190082123)
          ·
            refine ⟨2883975396778074285123185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922650264518716190082123 2883975396778074285123185)
            ·
              refine ⟨2162981547583555713842389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2883975396778074285123185 2162981547583555713842389)
              ·
                refine ⟨50694880021489587043181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2162981547583555713842389 50694880021489587043181)
                ·
                  rfl

theorem cell23_2665654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_2665654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665654 prefixEnd_2665654 := by exact prefixLift 2665654
  have htrace : WordTrace (prefixWord ++ tailWord_2665654) baseStart_2665654 baseEnd_2665654 := by
    simpa [prefixWord, tailWord_2665654, baseEnd_2665654] using wordTrace_append hprefix tailTrace_2665654
  have hstable : (prefixWord ++ tailWord_2665654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665654).length < 2 ^ (prefixWord ++ tailWord_2665654).sum := by decide
  have hdescent : baseEnd_2665654 < baseStart_2665654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665659 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 9]
def baseStart_2665659 : Nat := 118140960795 + 2665659 * 2 ^ 59
def prefixEnd_2665659 : Nat := 4983230072969 + 3 ^ 40 * 2665659 * 2
def baseEnd_2665659 : Nat := 152084925331499036733707

theorem tailTrace_2665659 : CollatzResearch.WordTrace tailWord_2665659 prefixEnd_2665659 152084925331499036733707 := by
  unfold tailWord_2665659
  simp only [CollatzResearch.WordTrace]
  refine ⟨97224571049780176157344031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64816380699853450771562687 97224571049780176157344031)
  ·
    refine ⟨145836856574670264236016047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97224571049780176157344031 145836856574670264236016047)
    ·
      refine ⟨218755284862005396354024071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145836856574670264236016047 218755284862005396354024071)
      ·
        refine ⟨328132927293008094531036107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218755284862005396354024071 328132927293008094531036107)
        ·
          refine ⟨492199390939512141796554161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328132927293008094531036107 492199390939512141796554161)
          ·
            refine ⟨369149543204634106347415621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492199390939512141796554161 369149543204634106347415621)
            ·
              refine ⟨69215539350868894940140429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 369149543204634106347415621 69215539350868894940140429)
              ·
                refine ⟨25955827256575835602552661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69215539350868894940140429 25955827256575835602552661)
                ·
                  refine ⟨152084925331499036733707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25955827256575835602552661 152084925331499036733707)
                  ·
                    rfl

theorem cell23_2665659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 9].length) (baseStart_2665659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665659 prefixEnd_2665659 := by exact prefixLift 2665659
  have htrace : WordTrace (prefixWord ++ tailWord_2665659) baseStart_2665659 baseEnd_2665659 := by
    simpa [prefixWord, tailWord_2665659, baseEnd_2665659] using wordTrace_append hprefix tailTrace_2665659
  have hstable : (prefixWord ++ tailWord_2665659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665659).length < 2 ^ (prefixWord ++ tailWord_2665659).sum := by decide
  have hdescent : baseEnd_2665659 < baseStart_2665659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665770 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_2665770 : Nat := 118140960795 + 2665770 * 2 ^ 59
def prefixEnd_2665770 : Nat := 4983230072969 + 3 ^ 40 * 2665770 * 2
def baseEnd_2665770 : Nat := 456273774778713465438451

theorem tailTrace_2665770 : CollatzResearch.WordTrace tailWord_2665770 prefixEnd_2665770 456273774778713465438451 := by
  unfold tailWord_2665770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24307154888094510528658691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64819079701585361409756509 24307154888094510528658691)
  ·
    refine ⟨36460732332141765792988037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24307154888094510528658691 36460732332141765792988037)
    ·
      refine ⟨6836387312276581086185257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36460732332141765792988037 6836387312276581086185257)
      ·
        refine ⟨5127290484207435814638943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6836387312276581086185257 5127290484207435814638943)
        ·
          refine ⟨7690935726311153721958415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5127290484207435814638943 7690935726311153721958415)
          ·
            refine ⟨11536403589466730582937623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7690935726311153721958415 11536403589466730582937623)
            ·
              refine ⟨17304605384200095874406435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11536403589466730582937623 17304605384200095874406435)
              ·
                refine ⟨25956908076300143811609653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17304605384200095874406435 25956908076300143811609653)
                ·
                  refine ⟨2433460132153138482338405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25956908076300143811609653 2433460132153138482338405)
                  ·
                    refine ⟨456273774778713465438451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433460132153138482338405 456273774778713465438451)
                    ·
                      rfl

theorem cell23_2665770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_2665770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665770 prefixEnd_2665770 := by exact prefixLift 2665770
  have htrace : WordTrace (prefixWord ++ tailWord_2665770) baseStart_2665770 baseEnd_2665770 := by
    simpa [prefixWord, tailWord_2665770, baseEnd_2665770] using wordTrace_append hprefix tailTrace_2665770
  have hstable : (prefixWord ++ tailWord_2665770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665770).length < 2 ^ (prefixWord ++ tailWord_2665770).sum := by decide
  have hdescent : baseEnd_2665770 < baseStart_2665770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665780 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2665780 : Nat := 118140960795 + 2665780 * 2 ^ 59
def prefixEnd_2665780 : Nat := 4983230072969 + 3 ^ 40 * 2665780 * 2
def baseEnd_2665780 : Nat := 1368826459142685357190307

theorem tailTrace_2665780 : CollatzResearch.WordTrace tailWord_2665780 prefixEnd_2665780 1368826459142685357190307 := by
  unfold tailWord_2665780
  simp only [CollatzResearch.WordTrace]
  refine ⟨48614492141170906911249397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64819322854894542548332529 48614492141170906911249397)
  ·
    refine ⟨4557608638234772522929631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48614492141170906911249397 4557608638234772522929631)
    ·
      refine ⟨6836412957352158784394447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4557608638234772522929631 6836412957352158784394447)
      ·
        refine ⟨10254619436028238176591671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6836412957352158784394447 10254619436028238176591671)
        ·
          refine ⟨15381929154042357264887507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10254619436028238176591671 15381929154042357264887507)
          ·
            refine ⟨23072893731063535897331261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15381929154042357264887507 23072893731063535897331261)
            ·
              refine ⟨8652335149148825961499223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23072893731063535897331261 8652335149148825961499223)
              ·
                refine ⟨12978502723723238942248835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8652335149148825961499223 12978502723723238942248835)
                ·
                  refine ⟨19467754085584858413373253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12978502723723238942248835 19467754085584858413373253)
                  ·
                    refine ⟨3650203891047160952507485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19467754085584858413373253 3650203891047160952507485)
                    ·
                      refine ⟨1368826459142685357190307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3650203891047160952507485 1368826459142685357190307)
                      ·
                        rfl

theorem cell23_2665780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2665780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665780 prefixEnd_2665780 := by exact prefixLift 2665780
  have htrace : WordTrace (prefixWord ++ tailWord_2665780) baseStart_2665780 baseEnd_2665780 := by
    simpa [prefixWord, tailWord_2665780, baseEnd_2665780] using wordTrace_append hprefix tailTrace_2665780
  have hstable : (prefixWord ++ tailWord_2665780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665780).length < 2 ^ (prefixWord ++ tailWord_2665780).sum := by decide
  have hdescent : baseEnd_2665780 < baseStart_2665780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665838 : List Nat := [4, 1, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_2665838 : Nat := 118140960795 + 2665838 * 2 ^ 59
def prefixEnd_2665838 : Nat := 4983230072969 + 3 ^ 40 * 2665838 * 2
def baseEnd_2665838 : Nat := 456285413673548710088347

theorem tailTrace_2665838 : CollatzResearch.WordTrace tailWord_2665838 prefixEnd_2665838 456285413673548710088347 := by
  unfold tailWord_2665838
  simp only [CollatzResearch.WordTrace]
  refine ⟨12153887464516461216013771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64820733144087793152073445 12153887464516461216013771)
  ·
    refine ⟨18230831196774691824020657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12153887464516461216013771 18230831196774691824020657)
    ·
      refine ⟨13673123397581018868015493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18230831196774691824020657 13673123397581018868015493)
      ·
        refine ⟨2563710637046441037752905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13673123397581018868015493 2563710637046441037752905)
        ·
          refine ⟨1922782977784830778314679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2563710637046441037752905 1922782977784830778314679)
          ·
            refine ⟨2884174466677246167472019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922782977784830778314679 2884174466677246167472019)
            ·
              refine ⟨4326261700015869251208029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2884174466677246167472019 4326261700015869251208029)
              ·
                refine ⟨1622348137505950969203011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4326261700015869251208029 1622348137505950969203011)
                ·
                  refine ⟨2433522206258926453804517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622348137505950969203011 2433522206258926453804517)
                  ·
                    refine ⟨456285413673548710088347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433522206258926453804517 456285413673548710088347)
                    ·
                      rfl

theorem cell23_2665838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_2665838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665838 prefixEnd_2665838 := by exact prefixLift 2665838
  have htrace : WordTrace (prefixWord ++ tailWord_2665838) baseStart_2665838 baseEnd_2665838 := by
    simpa [prefixWord, tailWord_2665838, baseEnd_2665838] using wordTrace_append hprefix tailTrace_2665838
  have hstable : (prefixWord ++ tailWord_2665838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665838).length < 2 ^ (prefixWord ++ tailWord_2665838).sum := by decide
  have hdescent : baseEnd_2665838 < baseStart_2665838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665860 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_2665860 : Nat := 118140960795 + 2665860 * 2 ^ 59
def prefixEnd_2665860 : Nat := 4983230072969 + 3 ^ 40 * 2665860 * 2
def baseEnd_2665860 : Nat := 456289179198348348063313

theorem tailTrace_2665860 : CollatzResearch.WordTrace tailWord_2665860 prefixEnd_2665860 456289179198348348063313 := by
  unfold tailWord_2665860
  simp only [CollatzResearch.WordTrace]
  refine ⟨48615951061025993742705517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64821268081367991656940689 48615951061025993742705517)
  ·
    refine ⟨18230981647884747653514569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48615951061025993742705517 18230981647884747653514569)
    ·
      refine ⟨13673236235913560740135927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18230981647884747653514569 13673236235913560740135927)
      ·
        refine ⟨20509854353870341110203891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13673236235913560740135927 20509854353870341110203891)
        ·
          refine ⟨30764781530805511665305837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20509854353870341110203891 30764781530805511665305837)
          ·
            refine ⟨11536793074052066874489689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30764781530805511665305837 11536793074052066874489689)
            ·
              refine ⟨8652594805539050155867267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11536793074052066874489689 8652594805539050155867267)
              ·
                refine ⟨12978892208308575233800901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8652594805539050155867267 12978892208308575233800901)
                ·
                  refine ⟨2433542289057857856337669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12978892208308575233800901 2433542289057857856337669)
                  ·
                    refine ⟨456289179198348348063313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433542289057857856337669 456289179198348348063313)
                    ·
                      rfl

theorem cell23_2665860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_2665860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665860 prefixEnd_2665860 := by exact prefixLift 2665860
  have htrace : WordTrace (prefixWord ++ tailWord_2665860) baseStart_2665860 baseEnd_2665860 := by
    simpa [prefixWord, tailWord_2665860, baseEnd_2665860] using wordTrace_append hprefix tailTrace_2665860
  have hstable : (prefixWord ++ tailWord_2665860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665860).length < 2 ^ (prefixWord ++ tailWord_2665860).sum := by decide
  have hdescent : baseEnd_2665860 < baseStart_2665860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665863 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_2665863 : Nat := 118140960795 + 2665863 * 2 ^ 59
def prefixEnd_2665863 : Nat := 4983230072969 + 3 ^ 40 * 2665863 * 2
def baseEnd_2665863 : Nat := 1368869078037008532452425

theorem tailTrace_2665863 : CollatzResearch.WordTrace tailWord_2665863 prefixEnd_2665863 1368869078037008532452425 := by
  unfold tailWord_2665863
  simp only [CollatzResearch.WordTrace]
  refine ⟨97232011541041118997770243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64821341027360745998513495 97232011541041118997770243)
  ·
    refine ⟨145848017311561678496655365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97232011541041118997770243 145848017311561678496655365)
    ·
      refine ⟨27346503245917814718122881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145848017311561678496655365 27346503245917814718122881)
      ·
        refine ⟨20509877434438361038592161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27346503245917814718122881 20509877434438361038592161)
        ·
          refine ⟨15382408075828770778944121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20509877434438361038592161 15382408075828770778944121)
          ·
            refine ⟨11536806056871578084208091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15382408075828770778944121 11536806056871578084208091)
            ·
              refine ⟨17305209085307367126312137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11536806056871578084208091 17305209085307367126312137)
              ·
                refine ⟨12978906813980525344734103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17305209085307367126312137 12978906813980525344734103)
                ·
                  refine ⟨19468360220970788017101155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12978906813980525344734103 19468360220970788017101155)
                  ·
                    refine ⟨29202540331456182025651733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19468360220970788017101155 29202540331456182025651733)
                    ·
                      refine ⟨1368869078037008532452425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29202540331456182025651733 1368869078037008532452425)
                      ·
                        rfl

theorem cell23_2665863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_2665863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665863 prefixEnd_2665863 := by exact prefixLift 2665863
  have htrace : WordTrace (prefixWord ++ tailWord_2665863) baseStart_2665863 baseEnd_2665863 := by
    simpa [prefixWord, tailWord_2665863, baseEnd_2665863] using wordTrace_append hprefix tailTrace_2665863
  have hstable : (prefixWord ++ tailWord_2665863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665863).length < 2 ^ (prefixWord ++ tailWord_2665863).sum := by decide
  have hdescent : baseEnd_2665863 < baseStart_2665863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665877 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 2, 4]
def baseStart_2665877 : Nat := 118140960795 + 2665877 * 2 ^ 59
def prefixEnd_2665877 : Nat := 4983230072969 + 3 ^ 40 * 2665877 * 2
def baseEnd_2665877 : Nat := 456292088922057159225787

theorem tailTrace_2665877 : CollatzResearch.WordTrace tailWord_2665877 prefixEnd_2665877 456292088922057159225787 := by
  unfold tailWord_2665877
  simp only [CollatzResearch.WordTrace]
  refine ⟨97232522162990399388779885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64821681441993599592519923 97232522162990399388779885)
  ·
    refine ⟨36462195811121399770792457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97232522162990399388779885 36462195811121399770792457)
    ·
      refine ⟨27346646858341049828094343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36462195811121399770792457 27346646858341049828094343)
      ·
        refine ⟨41019970287511574742141515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27346646858341049828094343 41019970287511574742141515)
        ·
          refine ⟨61529955431267362113212273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41019970287511574742141515 61529955431267362113212273)
          ·
            refine ⟨46147466573450521584909205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61529955431267362113212273 46147466573450521584909205)
            ·
              refine ⟨2163162495630493199292619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46147466573450521584909205 2163162495630493199292619)
              ·
                refine ⟨3244743743445739798938929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163162495630493199292619 3244743743445739798938929)
                ·
                  refine ⟨2433557807584304849204197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3244743743445739798938929 2433557807584304849204197)
                  ·
                    refine ⟨456292088922057159225787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433557807584304849204197 456292088922057159225787)
                    ·
                      rfl

theorem cell23_2665877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_2665877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665877 prefixEnd_2665877 := by exact prefixLift 2665877
  have htrace : WordTrace (prefixWord ++ tailWord_2665877) baseStart_2665877 baseEnd_2665877 := by
    simpa [prefixWord, tailWord_2665877, baseEnd_2665877] using wordTrace_append hprefix tailTrace_2665877
  have hstable : (prefixWord ++ tailWord_2665877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665877).length < 2 ^ (prefixWord ++ tailWord_2665877).sum := by decide
  have hdescent : baseEnd_2665877 < baseStart_2665877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665887 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 1, 2, 3]
def baseStart_2665887 : Nat := 118140960795 + 2665887 * 2 ^ 59
def prefixEnd_2665887 : Nat := 4983230072969 + 3 ^ 40 * 2665887 * 2
def baseEnd_2665887 : Nat := 1368881401572716438552315

theorem tailTrace_2665887 : CollatzResearch.WordTrace tailWord_2665887 prefixEnd_2665887 1368881401572716438552315 := by
  unfold tailWord_2665887
  simp only [CollatzResearch.WordTrace]
  refine ⟨97232886892954171096643915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64821924595302780731095943 97232886892954171096643915)
  ·
    refine ⟨145849330339431256644965873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97232886892954171096643915 145849330339431256644965873)
    ·
      refine ⟨109386997754573442483724405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145849330339431256644965873 109386997754573442483724405)
      ·
        refine ⟨10255031039491260232849163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109386997754573442483724405 10255031039491260232849163)
        ·
          refine ⟨15382546559236890349273745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10255031039491260232849163 15382546559236890349273745)
          ·
            refine ⟨11536909919427667761955309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15382546559236890349273745 11536909919427667761955309)
            ·
              refine ⟨4326341219785375410733241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11536909919427667761955309 4326341219785375410733241)
              ·
                refine ⟨3244755914839031558049931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4326341219785375410733241 3244755914839031558049931)
                ·
                  refine ⟨4867133872258547337074897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244755914839031558049931 4867133872258547337074897)
                  ·
                    refine ⟨3650350404193910502806173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4867133872258547337074897 3650350404193910502806173)
                    ·
                      refine ⟨1368881401572716438552315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3650350404193910502806173 1368881401572716438552315)
                      ·
                        rfl

theorem cell23_2665887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_2665887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665887 prefixEnd_2665887 := by exact prefixLift 2665887
  have htrace : WordTrace (prefixWord ++ tailWord_2665887) baseStart_2665887 baseEnd_2665887 := by
    simpa [prefixWord, tailWord_2665887, baseEnd_2665887] using wordTrace_append hprefix tailTrace_2665887
  have hstable : (prefixWord ++ tailWord_2665887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665887).length < 2 ^ (prefixWord ++ tailWord_2665887).sum := by decide
  have hdescent : baseEnd_2665887 < baseStart_2665887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665900 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 3]
def baseStart_2665900 : Nat := 118140960795 + 2665900 * 2 ^ 59
def prefixEnd_2665900 : Nat := 4983230072969 + 3 ^ 40 * 2665900 * 2
def baseEnd_2665900 : Nat := 1368888076821224887689755

theorem tailTrace_2665900 : CollatzResearch.WordTrace tailWord_2665900 prefixEnd_2665900 1368888076821224887689755 := by
  unfold tailWord_2665900
  simp only [CollatzResearch.WordTrace]
  refine ⟨48616680520953537158433577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64822240694604716211244769 48616680520953537158433577)
  ·
    refine ⟨36462510390715152868825183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48616680520953537158433577 36462510390715152868825183)
    ·
      refine ⟨54693765586072729303237775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36462510390715152868825183 54693765586072729303237775)
      ·
        refine ⟨82040648379109093954856663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54693765586072729303237775 82040648379109093954856663)
        ·
          refine ⟨123060972568663640932284995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82040648379109093954856663 123060972568663640932284995)
          ·
            refine ⟨184591458852995461398427493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123060972568663640932284995 184591458852995461398427493)
            ·
              refine ⟨34610898534936649012205155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184591458852995461398427493 34610898534936649012205155)
              ·
                refine ⟨51916347802404973518307733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34610898534936649012205155 51916347802404973518307733)
                ·
                  refine ⟨2433578803237733133670675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51916347802404973518307733 2433578803237733133670675)
                  ·
                    refine ⟨3650368204856599700506013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2433578803237733133670675 3650368204856599700506013)
                    ·
                      refine ⟨1368888076821224887689755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3650368204856599700506013 1368888076821224887689755)
                      ·
                        rfl

theorem cell23_2665900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_2665900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665900 prefixEnd_2665900 := by exact prefixLift 2665900
  have htrace : WordTrace (prefixWord ++ tailWord_2665900) baseStart_2665900 baseEnd_2665900 := by
    simpa [prefixWord, tailWord_2665900, baseEnd_2665900] using wordTrace_append hprefix tailTrace_2665900
  have hstable : (prefixWord ++ tailWord_2665900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665900).length < 2 ^ (prefixWord ++ tailWord_2665900).sum := by decide
  have hdescent : baseEnd_2665900 < baseStart_2665900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665923 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 4]
def baseStart_2665923 : Nat := 118140960795 + 2665923 * 2 ^ 59
def prefixEnd_2665923 : Nat := 4983230072969 + 3 ^ 40 * 2665923 * 2
def baseEnd_2665923 : Nat := 1368899886876278297702149

theorem tailTrace_2665923 : CollatzResearch.WordTrace tailWord_2665923 prefixEnd_2665923 1368899886876278297702149 := by
  unfold tailWord_2665923
  simp only [CollatzResearch.WordTrace]
  refine ⟨97234199920823749244954423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64822799947215832829969615 97234199920823749244954423)
  ·
    refine ⟨145851299881235623867431635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97234199920823749244954423 145851299881235623867431635)
    ·
      refine ⟨218776949821853435801147453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145851299881235623867431635 218776949821853435801147453)
      ·
        refine ⟨82041356183195038425430295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218776949821853435801147453 82041356183195038425430295)
        ·
          refine ⟨123062034274792557638145443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82041356183195038425430295 123062034274792557638145443)
          ·
            refine ⟨184593051412188836457218165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123062034274792557638145443 184593051412188836457218165)
            ·
              refine ⟨17305598569892703417864203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184593051412188836457218165 17305598569892703417864203)
              ·
                refine ⟨25958397854839055126796305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17305598569892703417864203 25958397854839055126796305)
                ·
                  refine ⟨19468798391129291345097229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25958397854839055126796305 19468798391129291345097229)
                  ·
                    refine ⟨7300799396673484254411461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19468798391129291345097229 7300799396673484254411461)
                    ·
                      refine ⟨1368899886876278297702149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7300799396673484254411461 1368899886876278297702149)
                      ·
                        rfl

theorem cell23_2665923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_2665923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665923 prefixEnd_2665923 := by exact prefixLift 2665923
  have htrace : WordTrace (prefixWord ++ tailWord_2665923) baseStart_2665923 baseEnd_2665923 := by
    simpa [prefixWord, tailWord_2665923, baseEnd_2665923] using wordTrace_append hprefix tailTrace_2665923
  have hstable : (prefixWord ++ tailWord_2665923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665923).length < 2 ^ (prefixWord ++ tailWord_2665923).sum := by decide
  have hdescent : baseEnd_2665923 < baseStart_2665923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665943 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_2665943 : Nat := 118140960795 + 2665943 * 2 ^ 59
def prefixEnd_2665943 : Nat := 4983230072969 + 3 ^ 40 * 2665943 * 2
def baseEnd_2665943 : Nat := 1368910156489368219452057

theorem tailTrace_2665943 : CollatzResearch.WordTrace tailWord_2665943 prefixEnd_2665943 1368910156489368219452057 := by
  unfold tailWord_2665943
  simp only [CollatzResearch.WordTrace]
  refine ⟨97234929380751292660682483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64823286253834195107121655 97234929380751292660682483)
  ·
    refine ⟨145852394071126938991023725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97234929380751292660682483 145852394071126938991023725)
    ·
      refine ⟨54694647776672602121633897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145852394071126938991023725 54694647776672602121633897)
      ·
        refine ⟨41020985832504451591225423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54694647776672602121633897 41020985832504451591225423)
        ·
          refine ⟨61531478748756677386838135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41020985832504451591225423 61531478748756677386838135)
          ·
            refine ⟨92297218123135016080257203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61531478748756677386838135 92297218123135016080257203)
            ·
              refine ⟨138445827184702524120385805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92297218123135016080257203 138445827184702524120385805)
              ·
                refine ⟨51917185194263446545144677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138445827184702524120385805 51917185194263446545144677)
                ·
                  refine ⟨9734472223924396227214627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51917185194263446545144677 9734472223924396227214627)
                  ·
                    refine ⟨14601708335886594340821941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9734472223924396227214627 14601708335886594340821941)
                    ·
                      refine ⟨1368910156489368219452057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14601708335886594340821941 1368910156489368219452057)
                      ·
                        rfl

theorem cell23_2665943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_2665943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665943 prefixEnd_2665943 := by exact prefixLift 2665943
  have htrace : WordTrace (prefixWord ++ tailWord_2665943) baseStart_2665943 baseEnd_2665943 := by
    simpa [prefixWord, tailWord_2665943, baseEnd_2665943] using wordTrace_append hprefix tailTrace_2665943
  have hstable : (prefixWord ++ tailWord_2665943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665943).length < 2 ^ (prefixWord ++ tailWord_2665943).sum := by decide
  have hdescent : baseEnd_2665943 < baseStart_2665943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2665993 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 3, 7]
def baseStart_2665993 : Nat := 118140960795 + 2665993 * 2 ^ 59
def prefixEnd_2665993 : Nat := 4983230072969 + 3 ^ 40 * 2665993 * 2
def baseEnd_2665993 : Nat := 456311943507364341275609

theorem tailTrace_2665993 : CollatzResearch.WordTrace tailWord_2665993 prefixEnd_2665993 456311943507364341275609 := by
  unfold tailWord_2665993
  simp only [CollatzResearch.WordTrace]
  refine ⟨97236753030570151200002633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64824502020380100800001755 97236753030570151200002633)
  ·
    refine ⟨72927564772927613400001975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97236753030570151200002633 72927564772927613400001975)
    ·
      refine ⟨109391347159391420100002963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72927564772927613400001975 109391347159391420100002963)
      ·
        refine ⟨164087020739087130150004445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109391347159391420100002963 164087020739087130150004445)
        ·
          refine ⟨61532632777157673806251667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164087020739087130150004445 61532632777157673806251667)
          ·
            refine ⟨92298949165736510709377501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61532632777157673806251667 92298949165736510709377501)
            ·
              refine ⟨34612105937151191516016563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92298949165736510709377501 34612105937151191516016563)
              ·
                refine ⟨51918158905726787274024845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34612105937151191516016563 51918158905726787274024845)
                ·
                  refine ⟨19469309589647545227759317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51918158905726787274024845 19469309589647545227759317)
                  ·
                    refine ⟨456311943507364341275609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19469309589647545227759317 456311943507364341275609)
                    ·
                      rfl

theorem cell23_2665993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_2665993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2665993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2665993 prefixEnd_2665993 := by exact prefixLift 2665993
  have htrace : WordTrace (prefixWord ++ tailWord_2665993) baseStart_2665993 baseEnd_2665993 := by
    simpa [prefixWord, tailWord_2665993, baseEnd_2665993] using wordTrace_append hprefix tailTrace_2665993
  have hstable : (prefixWord ++ tailWord_2665993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2665993).length < 2 ^ (prefixWord ++ tailWord_2665993).sum := by decide
  have hdescent : baseEnd_2665993 < baseStart_2665993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2665993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666010 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_2666010 : Nat := 118140960795 + 2666010 * 2 ^ 59
def prefixEnd_2666010 : Nat := 4983230072969 + 3 ^ 40 * 2666010 * 2
def baseEnd_2666010 : Nat := 456314853231073152438083

theorem tailTrace_2666010 : CollatzResearch.WordTrace tailWord_2666010 prefixEnd_2666010 456314853231073152438083 := by
  unfold tailWord_2666010
  simp only [CollatzResearch.WordTrace]
  refine ⟨24309343267877140775842871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64824915381005708735580989 24309343267877140775842871)
  ·
    refine ⟨36464014901815711163764307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24309343267877140775842871 36464014901815711163764307)
    ·
      refine ⟨54696022352723566745646461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36464014901815711163764307 54696022352723566745646461)
      ·
        refine ⟨20511008382271337529617423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54696022352723566745646461 20511008382271337529617423)
        ·
          refine ⟨30766512573407006294426135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20511008382271337529617423 30766512573407006294426135)
          ·
            refine ⟨46149768860110509441639203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30766512573407006294426135 46149768860110509441639203)
            ·
              refine ⟨69224653290165764162458805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46149768860110509441639203 69224653290165764162458805)
              ·
                refine ⟨6489811245953040390230513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69224653290165764162458805 6489811245953040390230513)
                ·
                  refine ⟨4867358434464780292672885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6489811245953040390230513 4867358434464780292672885)
                  ·
                    refine ⟨456314853231073152438083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4867358434464780292672885 456314853231073152438083)
                    ·
                      rfl

theorem cell23_2666010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_2666010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666010 prefixEnd_2666010 := by exact prefixLift 2666010
  have htrace : WordTrace (prefixWord ++ tailWord_2666010) baseStart_2666010 baseEnd_2666010 := by
    simpa [prefixWord, tailWord_2666010, baseEnd_2666010] using wordTrace_append hprefix tailTrace_2666010
  have hstable : (prefixWord ++ tailWord_2666010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666010).length < 2 ^ (prefixWord ++ tailWord_2666010).sum := by decide
  have hdescent : baseEnd_2666010 < baseStart_2666010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666097 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 7, 1, 3]
def baseStart_2666097 : Nat := 118140960795 + 2666097 * 2 ^ 59
def prefixEnd_2666097 : Nat := 4983230072969 + 3 ^ 40 * 2666097 * 2
def baseEnd_2666097 : Nat := 1368989232510160616926349

theorem tailTrace_2666097 : CollatzResearch.WordTrace tailWord_2666097 prefixEnd_2666097 1368989232510160616926349 := by
  unfold tailWord_2666097
  simp only [CollatzResearch.WordTrace]
  refine ⟨97240546222193376961788545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64827030814795584641192363 97240546222193376961788545)
  ·
    refine ⟨72930409666645032721341409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97240546222193376961788545 72930409666645032721341409)
    ·
      refine ⟨54697807249983774541006057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72930409666645032721341409 54697807249983774541006057)
      ·
        refine ⟨41023355437487830905754543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54697807249983774541006057 41023355437487830905754543)
        ·
          refine ⟨61535033156231746358631815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41023355437487830905754543 61535033156231746358631815)
          ·
            refine ⟨92302549734347619537947723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61535033156231746358631815 92302549734347619537947723)
            ·
              refine ⟨138453824601521429306921585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92302549734347619537947723 138453824601521429306921585)
              ·
                refine ⟨103840368451141071980191189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138453824601521429306921585 103840368451141071980191189)
                ·
                  refine ⟨2433758635573618874535731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 103840368451141071980191189 2433758635573618874535731)
                  ·
                    refine ⟨3650637953360428311803597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2433758635573618874535731 3650637953360428311803597)
                    ·
                      refine ⟨1368989232510160616926349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3650637953360428311803597 1368989232510160616926349)
                      ·
                        rfl

theorem cell23_2666097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_2666097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666097 prefixEnd_2666097 := by exact prefixLift 2666097
  have htrace : WordTrace (prefixWord ++ tailWord_2666097) baseStart_2666097 baseEnd_2666097 := by
    simpa [prefixWord, tailWord_2666097, baseEnd_2666097] using wordTrace_append hprefix tailTrace_2666097
  have hstable : (prefixWord ++ tailWord_2666097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666097).length < 2 ^ (prefixWord ++ tailWord_2666097).sum := by decide
  have hdescent : baseEnd_2666097 < baseStart_2666097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666107 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 1, 5, 2]
def baseStart_2666107 : Nat := 118140960795 + 2666107 * 2 ^ 59
def prefixEnd_2666107 : Nat := 4983230072969 + 3 ^ 40 * 2666107 * 2
def baseEnd_2666107 : Nat := 1368994367316705577801303

theorem tailTrace_2666107 : CollatzResearch.WordTrace tailWord_2666107 prefixEnd_2666107 1368994367316705577801303 := by
  unfold tailWord_2666107
  simp only [CollatzResearch.WordTrace]
  refine ⟨97240910952157148669652575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64827273968104765779768383 97240910952157148669652575)
  ·
    refine ⟨145861366428235723004478863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97240910952157148669652575 145861366428235723004478863)
    ·
      refine ⟨218792049642353584506718295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145861366428235723004478863 218792049642353584506718295)
      ·
        refine ⟨328188074463530376760077443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218792049642353584506718295 328188074463530376760077443)
        ·
          refine ⟨492282111695295565140116165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328188074463530376760077443 492282111695295565140116165)
          ·
            refine ⟨92302895942867918463771781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 492282111695295565140116165 92302895942867918463771781)
            ·
              refine ⟨17306792989287734711957209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92302895942867918463771781 17306792989287734711957209)
              ·
                refine ⟨12980094741965801033967907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17306792989287734711957209 12980094741965801033967907)
                ·
                  refine ⟨19470142112948701550951861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12980094741965801033967907 19470142112948701550951861)
                  ·
                    refine ⟨1825325823088940770401737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19470142112948701550951861 1825325823088940770401737)
                    ·
                      refine ⟨1368994367316705577801303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1825325823088940770401737 1368994367316705577801303)
                      ·
                        rfl

theorem cell23_2666107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 5, 2].length) (baseStart_2666107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666107 prefixEnd_2666107 := by exact prefixLift 2666107
  have htrace : WordTrace (prefixWord ++ tailWord_2666107) baseStart_2666107 baseEnd_2666107 := by
    simpa [prefixWord, tailWord_2666107, baseEnd_2666107] using wordTrace_append hprefix tailTrace_2666107
  have hstable : (prefixWord ++ tailWord_2666107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666107).length < 2 ^ (prefixWord ++ tailWord_2666107).sum := by decide
  have hdescent : baseEnd_2666107 < baseStart_2666107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666117 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_2666117 : Nat := 118140960795 + 2666117 * 2 ^ 59
def prefixEnd_2666117 : Nat := 4983230072969 + 3 ^ 40 * 2666117 * 2
def baseEnd_2666117 : Nat := 456333167374416846225419

theorem tailTrace_2666117 : CollatzResearch.WordTrace tailWord_2666117 prefixEnd_2666117 456333167374416846225419 := by
  unfold tailWord_2666117
  simp only [CollatzResearch.WordTrace]
  refine ⟨97241275682120920377516605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64827517121413946918344403 97241275682120920377516605)
  ·
    refine ⟨36465478380795345141568727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97241275682120920377516605 36465478380795345141568727)
    ·
      refine ⟨54698217571193017712353091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36465478380795345141568727 54698217571193017712353091)
      ·
        refine ⟨82047326356789526568529637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54698217571193017712353091 82047326356789526568529637)
        ·
          refine ⟨15383873691898036231599307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82047326356789526568529637 15383873691898036231599307)
          ·
            refine ⟨23075810537847054347398961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15383873691898036231599307 23075810537847054347398961)
            ·
              refine ⟨17306857903385290760549221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23075810537847054347398961 17306857903385290760549221)
              ·
                refine ⟨3245035856884742017602979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17306857903385290760549221 3245035856884742017602979)
                ·
                  refine ⟨4867553785327113026404469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3245035856884742017602979 4867553785327113026404469)
                  ·
                    refine ⟨456333167374416846225419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4867553785327113026404469 456333167374416846225419)
                    ·
                      rfl

theorem cell23_2666117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_2666117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666117 prefixEnd_2666117 := by exact prefixLift 2666117
  have htrace : WordTrace (prefixWord ++ tailWord_2666117) baseStart_2666117 baseEnd_2666117 := by
    simpa [prefixWord, tailWord_2666117, baseEnd_2666117] using wordTrace_append hprefix tailTrace_2666117
  have hstable : (prefixWord ++ tailWord_2666117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666117).length < 2 ^ (prefixWord ++ tailWord_2666117).sum := by decide
  have hdescent : baseEnd_2666117 < baseStart_2666117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666147 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 4, 4]
def baseStart_2666147 : Nat := 118140960795 + 2666147 * 2 ^ 59
def prefixEnd_2666147 : Nat := 4983230072969 + 3 ^ 40 * 2666147 * 2
def baseEnd_2666147 : Nat := 456338302180961807100373

theorem tailTrace_2666147 : CollatzResearch.WordTrace tailWord_2666147 prefixEnd_2666147 456338302180961807100373 := by
  unfold tailWord_2666147
  simp only [CollatzResearch.WordTrace]
  refine ⟨97242369872012235501108695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64828246581341490334072463 97242369872012235501108695)
  ·
    refine ⟨145863554808018353251663043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97242369872012235501108695 145863554808018353251663043)
    ·
      refine ⟨218795332212027529877494565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145863554808018353251663043 218795332212027529877494565)
      ·
        refine ⟨41024124789755161852030231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218795332212027529877494565 41024124789755161852030231)
        ·
          refine ⟨61536187184632742778045347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41024124789755161852030231 61536187184632742778045347)
          ·
            refine ⟨92304280776949114167068021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61536187184632742778045347 92304280776949114167068021)
            ·
              refine ⟨8653526322838979453162627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92304280776949114167068021 8653526322838979453162627)
              ·
                refine ⟨12980289484258469179743941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8653526322838979453162627 12980289484258469179743941)
                ·
                  refine ⟨2433804278298462971201989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12980289484258469179743941 2433804278298462971201989)
                  ·
                    refine ⟨456338302180961807100373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433804278298462971201989 456338302180961807100373)
                    ·
                      rfl

theorem cell23_2666147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 4].length) (baseStart_2666147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666147 prefixEnd_2666147 := by exact prefixLift 2666147
  have htrace : WordTrace (prefixWord ++ tailWord_2666147) baseStart_2666147 baseEnd_2666147 := by
    simpa [prefixWord, tailWord_2666147, baseEnd_2666147] using wordTrace_append hprefix tailTrace_2666147
  have hstable : (prefixWord ++ tailWord_2666147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666147).length < 2 ^ (prefixWord ++ tailWord_2666147).sum := by decide
  have hdescent : baseEnd_2666147 < baseStart_2666147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666167 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_2666167 : Nat := 118140960795 + 2666167 * 2 ^ 59
def prefixEnd_2666167 : Nat := 4983230072969 + 3 ^ 40 * 2666167 * 2
def baseEnd_2666167 : Nat := 1369025176155975343051027

theorem tailTrace_2666167 : CollatzResearch.WordTrace tailWord_2666167 prefixEnd_2666167 1369025176155975343051027 := by
  unfold tailWord_2666167
  simp only [CollatzResearch.WordTrace]
  refine ⟨97243099331939778916836755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64828732887959852611224503 97243099331939778916836755)
  ·
    refine ⟨145864648997909668375255133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97243099331939778916836755 145864648997909668375255133)
    ·
      refine ⟨54699243374216125640720675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145864648997909668375255133 54699243374216125640720675)
      ·
        refine ⟨82048865061324188461081013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54699243374216125640720675 82048865061324188461081013)
        ·
          refine ⟨7692081099499142668226345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82048865061324188461081013 7692081099499142668226345)
          ·
            refine ⟨5769060824624357001169759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7692081099499142668226345 5769060824624357001169759)
            ·
              refine ⟨8653591236936535501754639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5769060824624357001169759 8653591236936535501754639)
              ·
                refine ⟨12980386855404803252631959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8653591236936535501754639 12980386855404803252631959)
                ·
                  refine ⟨19470580283107204878947939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12980386855404803252631959 19470580283107204878947939)
                  ·
                    refine ⟨29205870424660807318421909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19470580283107204878947939 29205870424660807318421909)
                    ·
                      refine ⟨1369025176155975343051027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29205870424660807318421909 1369025176155975343051027)
                      ·
                        rfl

theorem cell23_2666167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_2666167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666167 prefixEnd_2666167 := by exact prefixLift 2666167
  have htrace : WordTrace (prefixWord ++ tailWord_2666167) baseStart_2666167 baseEnd_2666167 := by
    simpa [prefixWord, tailWord_2666167, baseEnd_2666167] using wordTrace_append hprefix tailTrace_2666167
  have hstable : (prefixWord ++ tailWord_2666167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666167).length < 2 ^ (prefixWord ++ tailWord_2666167).sum := by decide
  have hdescent : baseEnd_2666167 < baseStart_2666167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666182 : List Nat := [6, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_2666182 : Nat := 118140960795 + 2666182 * 2 ^ 59
def prefixEnd_2666182 : Nat := 4983230072969 + 3 ^ 40 * 2666182 * 2
def baseEnd_2666182 : Nat := 1369032878365792784363459

theorem tailTrace_2666182 : CollatzResearch.WordTrace tailWord_2666182 prefixEnd_2666182 1369032878365792784363459 := by
  unfold tailWord_2666182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3038863950840169889957275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64829097617923624319088533 3038863950840169889957275)
  ·
    refine ⟨4558295926260254834935913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3038863950840169889957275 4558295926260254834935913)
    ·
      refine ⟨3418721944695191126201935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4558295926260254834935913 3418721944695191126201935)
      ·
        refine ⟨5128082917042786689302903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3418721944695191126201935 5128082917042786689302903)
        ·
          refine ⟨7692124375564180033954355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5128082917042786689302903 7692124375564180033954355)
          ·
            refine ⟨11538186563346270050931533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7692124375564180033954355 11538186563346270050931533)
            ·
              refine ⟨4326819961254851269099325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11538186563346270050931533 4326819961254851269099325)
              ·
                refine ⟨1622557485470569225912247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4326819961254851269099325 1622557485470569225912247)
                ·
                  refine ⟨2433836228205853838868371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622557485470569225912247 2433836228205853838868371)
                  ·
                    refine ⟨3650754342308780758302557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2433836228205853838868371 3650754342308780758302557)
                    ·
                      refine ⟨1369032878365792784363459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3650754342308780758302557 1369032878365792784363459)
                      ·
                        rfl

theorem cell23_2666182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_2666182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666182 prefixEnd_2666182 := by exact prefixLift 2666182
  have htrace : WordTrace (prefixWord ++ tailWord_2666182) baseStart_2666182 baseEnd_2666182 := by
    simpa [prefixWord, tailWord_2666182, baseEnd_2666182] using wordTrace_append hprefix tailTrace_2666182
  have hstable : (prefixWord ++ tailWord_2666182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666182).length < 2 ^ (prefixWord ++ tailWord_2666182).sum := by decide
  have hdescent : baseEnd_2666182 < baseStart_2666182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666187 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 3]
def baseStart_2666187 : Nat := 118140960795 + 2666187 * 2 ^ 59
def prefixEnd_2666187 : Nat := 4983230072969 + 3 ^ 40 * 2666187 * 2
def baseEnd_2666187 : Nat := 1369035445769065264800935

theorem tailTrace_2666187 : CollatzResearch.WordTrace tailWord_2666187 prefixEnd_2666187 1369035445769065264800935 := by
  unfold tailWord_2666187
  simp only [CollatzResearch.WordTrace]
  refine ⟨97243828791867322332564815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64829219194578214888376543 97243828791867322332564815)
  ·
    refine ⟨145865743187800983498847223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97243828791867322332564815 145865743187800983498847223)
    ·
      refine ⟨218798614781701475248270835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145865743187800983498847223 218798614781701475248270835)
      ·
        refine ⟨328197922172552212872406253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218798614781701475248270835 328197922172552212872406253)
        ·
          refine ⟨123074220814707079827152345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328197922172552212872406253 123074220814707079827152345)
          ·
            refine ⟨92305665611030309870364259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123074220814707079827152345 92305665611030309870364259)
            ·
              refine ⟨138458498416545464805546389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92305665611030309870364259 138458498416545464805546389)
              ·
                refine ⟨6490242113275568662759987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138458498416545464805546389 6490242113275568662759987)
                ·
                  refine ⟨9735363169913352994139981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6490242113275568662759987 9735363169913352994139981)
                  ·
                    refine ⟨3650761188717507372802493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9735363169913352994139981 3650761188717507372802493)
                    ·
                      refine ⟨1369035445769065264800935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3650761188717507372802493 1369035445769065264800935)
                      ·
                        rfl

theorem cell23_2666187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 3].length) (baseStart_2666187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666187 prefixEnd_2666187 := by exact prefixLift 2666187
  have htrace : WordTrace (prefixWord ++ tailWord_2666187) baseStart_2666187 baseEnd_2666187 := by
    simpa [prefixWord, tailWord_2666187, baseEnd_2666187] using wordTrace_append hprefix tailTrace_2666187
  have hstable : (prefixWord ++ tailWord_2666187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666187).length < 2 ^ (prefixWord ++ tailWord_2666187).sum := by decide
  have hdescent : baseEnd_2666187 < baseStart_2666187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666215 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 2, 4]
def baseStart_2666215 : Nat := 118140960795 + 2666215 * 2 ^ 59
def prefixEnd_2666215 : Nat := 4983230072969 + 3 ^ 40 * 2666215 * 2
def baseEnd_2666215 : Nat := 456349941075797051750269

theorem tailTrace_2666215 : CollatzResearch.WordTrace tailWord_2666215 prefixEnd_2666215 456349941075797051750269 := by
  unfold tailWord_2666215
  simp only [CollatzResearch.WordTrace]
  refine ⟨97244850035765883114584099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64829900023843922076389399 97244850035765883114584099)
  ·
    refine ⟨145867275053648824671876149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97244850035765883114584099 145867275053648824671876149)
    ·
      refine ⟨13675057036279577312988389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145867275053648824671876149 13675057036279577312988389)
      ·
        refine ⟨2564073194302420746185323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13675057036279577312988389 2564073194302420746185323)
        ·
          refine ⟨3846109791453631119277985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564073194302420746185323 3846109791453631119277985)
          ·
            refine ⟨2884582343590223339458489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3846109791453631119277985 2884582343590223339458489)
            ·
              refine ⟨2163436757692667504593867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2884582343590223339458489 2163436757692667504593867)
              ·
                refine ⟨3245155136539001256890801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163436757692667504593867 3245155136539001256890801)
                ·
                  refine ⟨2433866352404250942668101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3245155136539001256890801 2433866352404250942668101)
                  ·
                    refine ⟨456349941075797051750269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433866352404250942668101 456349941075797051750269)
                    ·
                      rfl

theorem cell23_2666215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_2666215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666215 prefixEnd_2666215 := by exact prefixLift 2666215
  have htrace : WordTrace (prefixWord ++ tailWord_2666215) baseStart_2666215 baseEnd_2666215 := by
    simpa [prefixWord, tailWord_2666215, baseEnd_2666215] using wordTrace_append hprefix tailTrace_2666215
  have hstable : (prefixWord ++ tailWord_2666215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666215).length < 2 ^ (prefixWord ++ tailWord_2666215).sum := by decide
  have hdescent : baseEnd_2666215 < baseStart_2666215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666231 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 1, 3, 2]
def baseStart_2666231 : Nat := 118140960795 + 2666231 * 2 ^ 59
def prefixEnd_2666231 : Nat := 4983230072969 + 3 ^ 40 * 2666231 * 2
def baseEnd_2666231 : Nat := 1369058038917863092650733

theorem tailTrace_2666231 : CollatzResearch.WordTrace tailWord_2666231 prefixEnd_2666231 1369058038917863092650733 := by
  unfold tailWord_2666231
  simp only [CollatzResearch.WordTrace]
  refine ⟨97245433603707917847166547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64830289069138611898111031 97245433603707917847166547)
  ·
    refine ⟨145868150405561876770749821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97245433603707917847166547 145868150405561876770749821)
    ·
      refine ⟨54700556402085703789031183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145868150405561876770749821 54700556402085703789031183)
      ·
        refine ⟨82050834603128555683546775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54700556402085703789031183 82050834603128555683546775)
        ·
          refine ⟨123076251904692833525320163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82050834603128555683546775 123076251904692833525320163)
          ·
            refine ⟨184614377857039250287980245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123076251904692833525320163 184614377857039250287980245)
            ·
              refine ⟨4326899481024357428624537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 184614377857039250287980245 4326899481024357428624537)
              ·
                refine ⟨3245174610768268071468403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4326899481024357428624537 3245174610768268071468403)
                ·
                  refine ⟨4867761916152402107202605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3245174610768268071468403 4867761916152402107202605)
                  ·
                    refine ⟨1825410718557150790200977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4867761916152402107202605 1825410718557150790200977)
                    ·
                      refine ⟨1369058038917863092650733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1825410718557150790200977 1369058038917863092650733)
                      ·
                        rfl

theorem cell23_2666231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_2666231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666231 prefixEnd_2666231 := by exact prefixLift 2666231
  have htrace : WordTrace (prefixWord ++ tailWord_2666231) baseStart_2666231 baseEnd_2666231 := by
    simpa [prefixWord, tailWord_2666231, baseEnd_2666231] using wordTrace_append hprefix tailTrace_2666231
  have hstable : (prefixWord ++ tailWord_2666231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666231).length < 2 ^ (prefixWord ++ tailWord_2666231).sum := by decide
  have hdescent : baseEnd_2666231 < baseStart_2666231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666248 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 1, 3, 2]
def baseStart_2666248 : Nat := 118140960795 + 2666248 * 2 ^ 59
def prefixEnd_2666248 : Nat := 4983230072969 + 3 ^ 40 * 2666248 * 2
def baseEnd_2666248 : Nat := 1369066768088989526138155

theorem tailTrace_2666248 : CollatzResearch.WordTrace tailWord_2666248 prefixEnd_2666248 1369066768088989526138155 := by
  unfold tailWord_2666248
  simp only [CollatzResearch.WordTrace]
  refine ⟨48623026822323164875267699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64830702429764219833690265 48623026822323164875267699)
  ·
    refine ⟨72934540233484747312901549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48623026822323164875267699 72934540233484747312901549)
    ·
      refine ⟨27350452587556780242338081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72934540233484747312901549 27350452587556780242338081)
      ·
        refine ⟨20512839440667585181753561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27350452587556780242338081 20512839440667585181753561)
        ·
          refine ⟨15384629580500688886315171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20512839440667585181753561 15384629580500688886315171)
          ·
            refine ⟨23076944370751033329472757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15384629580500688886315171 23076944370751033329472757)
            ·
              refine ⟨2163463534757909374638071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23076944370751033329472757 2163463534757909374638071)
              ·
                refine ⟨3245195302136864061957107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163463534757909374638071 3245195302136864061957107)
                ·
                  refine ⟨4867792953205296092935661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3245195302136864061957107 4867792953205296092935661)
                  ·
                    refine ⟨1825422357451986034850873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4867792953205296092935661 1825422357451986034850873)
                    ·
                      refine ⟨1369066768088989526138155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1825422357451986034850873 1369066768088989526138155)
                      ·
                        rfl

theorem cell23_2666248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_2666248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666248 prefixEnd_2666248 := by exact prefixLift 2666248
  have htrace : WordTrace (prefixWord ++ tailWord_2666248) baseStart_2666248 baseEnd_2666248 := by
    simpa [prefixWord, tailWord_2666248, baseEnd_2666248] using wordTrace_append hprefix tailTrace_2666248
  have hstable : (prefixWord ++ tailWord_2666248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666248).length < 2 ^ (prefixWord ++ tailWord_2666248).sum := by decide
  have hdescent : baseEnd_2666248 < baseStart_2666248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666257 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_2666257 : Nat := 118140960795 + 2666257 * 2 ^ 59
def prefixEnd_2666257 : Nat := 4983230072969 + 3 ^ 40 * 2666257 * 2
def baseEnd_2666257 : Nat := 1369071389414879990925613

theorem tailTrace_2666257 : CollatzResearch.WordTrace tailWord_2666257 prefixEnd_2666257 1369071389414879990925613 := by
  unfold tailWord_2666257
  simp only [CollatzResearch.WordTrace]
  refine ⟨97246381901613724287613025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64830921267742482858408683 97246381901613724287613025)
  ·
    refine ⟨72934786426210293215709769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97246381901613724287613025 72934786426210293215709769)
    ·
      refine ⟨54701089819657719911782327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72934786426210293215709769 54701089819657719911782327)
      ·
        refine ⟨82051634729486579867673491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54701089819657719911782327 82051634729486579867673491)
        ·
          refine ⟨123077452094229869801510237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82051634729486579867673491 123077452094229869801510237)
          ·
            refine ⟨46154044535336201175566339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123077452094229869801510237 46154044535336201175566339)
            ·
              refine ⟨69231066803004301763349509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46154044535336201175566339 69231066803004301763349509)
              ·
                refine ⟨12980825025563306580628033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69231066803004301763349509 12980825025563306580628033)
                ·
                  refine ⟨9735618769172479935471025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12980825025563306580628033 9735618769172479935471025)
                  ·
                    refine ⟨7301714076879359951603269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9735618769172479935471025 7301714076879359951603269)
                    ·
                      refine ⟨1369071389414879990925613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7301714076879359951603269 1369071389414879990925613)
                      ·
                        rfl

theorem cell23_2666257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_2666257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666257 prefixEnd_2666257 := by exact prefixLift 2666257
  have htrace : WordTrace (prefixWord ++ tailWord_2666257) baseStart_2666257 baseEnd_2666257 := by
    simpa [prefixWord, tailWord_2666257, baseEnd_2666257] using wordTrace_append hprefix tailTrace_2666257
  have hstable : (prefixWord ++ tailWord_2666257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666257).length < 2 ^ (prefixWord ++ tailWord_2666257).sum := by decide
  have hdescent : baseEnd_2666257 < baseStart_2666257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666274 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_2666274 : Nat := 118140960795 + 2666274 * 2 ^ 59
def prefixEnd_2666274 : Nat := 4983230072969 + 3 ^ 40 * 2666274 * 2
def baseEnd_2666274 : Nat := 1369080118586006424413035

theorem tailTrace_2666274 : CollatzResearch.WordTrace tailWord_2666274 prefixEnd_2666274 1369080118586006424413035 := by
  unfold tailWord_2666274
  simp only [CollatzResearch.WordTrace]
  refine ⟨24311750485638034047745469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64831334628368090793987917 24311750485638034047745469)
  ·
    refine ⟨9116906432114262767904551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24311750485638034047745469 9116906432114262767904551)
    ·
      refine ⟨13675359648171394151856827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9116906432114262767904551 13675359648171394151856827)
      ·
        refine ⟨20513039472257091227785241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13675359648171394151856827 20513039472257091227785241)
        ·
          refine ⟨15384779604192818420838931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20513039472257091227785241 15384779604192818420838931)
          ·
            refine ⟨23077169406289227631258397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15384779604192818420838931 23077169406289227631258397)
            ·
              refine ⟨8653938527358460361721899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23077169406289227631258397 8653938527358460361721899)
              ·
                refine ⟨12980907791037690542582849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8653938527358460361721899 12980907791037690542582849)
                ·
                  refine ⟨9735680843278267906937137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12980907791037690542582849 9735680843278267906937137)
                  ·
                    refine ⟨7301760632458700930202853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9735680843278267906937137 7301760632458700930202853)
                    ·
                      refine ⟨1369080118586006424413035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7301760632458700930202853 1369080118586006424413035)
                      ·
                        rfl

theorem cell23_2666274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_2666274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666274 prefixEnd_2666274 := by exact prefixLift 2666274
  have htrace : WordTrace (prefixWord ++ tailWord_2666274) baseStart_2666274 baseEnd_2666274 := by
    simpa [prefixWord, tailWord_2666274, baseEnd_2666274] using wordTrace_append hprefix tailTrace_2666274
  have hstable : (prefixWord ++ tailWord_2666274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666274).length < 2 ^ (prefixWord ++ tailWord_2666274).sum := by decide
  have hdescent : baseEnd_2666274 < baseStart_2666274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666301 : List Nat := [1, 4, 1, 4, 1, 1, 1, 5, 5]
def baseStart_2666301 : Nat := 118140960795 + 2666301 * 2 ^ 59
def prefixEnd_2666301 : Nat := 4983230072969 + 3 ^ 40 * 2666301 * 2
def baseEnd_2666301 : Nat := 152121553618186424308379

theorem tailTrace_2666301 : CollatzResearch.WordTrace tailWord_2666301 prefixEnd_2666301 152121553618186424308379 := by
  unfold tailWord_2666301
  simp only [CollatzResearch.WordTrace]
  refine ⟨97247986713454319802214757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64831991142302879868143171 97247986713454319802214757)
  ·
    refine ⟨18233997508772684962915267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97247986713454319802214757 18233997508772684962915267)
    ·
      refine ⟨27350996263159027444372901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18233997508772684962915267 27350996263159027444372901)
      ·
        refine ⟨5128311799342317645819919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27350996263159027444372901 5128311799342317645819919)
        ·
          refine ⟨7692467699013476468729879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5128311799342317645819919 7692467699013476468729879)
          ·
            refine ⟨11538701548520214703094819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7692467699013476468729879 11538701548520214703094819)
            ·
              refine ⟨17308052322780322054642229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11538701548520214703094819 17308052322780322054642229)
              ·
                refine ⟨1622629905260655192622709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17308052322780322054642229 1622629905260655192622709)
                ·
                  refine ⟨152121553618186424308379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1622629905260655192622709 152121553618186424308379)
                  ·
                    rfl

theorem cell23_2666301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_2666301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666301 prefixEnd_2666301 := by exact prefixLift 2666301
  have htrace : WordTrace (prefixWord ++ tailWord_2666301) baseStart_2666301 baseEnd_2666301 := by
    simpa [prefixWord, tailWord_2666301, baseEnd_2666301] using wordTrace_append hprefix tailTrace_2666301
  have hstable : (prefixWord ++ tailWord_2666301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666301).length < 2 ^ (prefixWord ++ tailWord_2666301).sum := by decide
  have hdescent : baseEnd_2666301 < baseStart_2666301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666347 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 4]
def baseStart_2666347 : Nat := 118140960795 + 2666347 * 2 ^ 59
def prefixEnd_2666347 : Nat := 4983230072969 + 3 ^ 40 * 2666347 * 2
def baseEnd_2666347 : Nat := 1369117602673784638800199

theorem tailTrace_2666347 : CollatzResearch.WordTrace tailWord_2666347 prefixEnd_2666347 1369117602673784638800199 := by
  unfold tailWord_2666347
  simp only [CollatzResearch.WordTrace]
  refine ⟨97249664471287669658389295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64833109647525113105592863 97249664471287669658389295)
  ·
    refine ⟨145874496706931504487583943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97249664471287669658389295 145874496706931504487583943)
    ·
      refine ⟨218811745060397256731375915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145874496706931504487583943 218811745060397256731375915)
      ·
        refine ⟨328217617590595885097063873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218811745060397256731375915 328217617590595885097063873)
        ·
          refine ⟨246163213192946913822797905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328217617590595885097063873 246163213192946913822797905)
          ·
            refine ⟨184622409894710185367098429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246163213192946913822797905 184622409894710185367098429)
            ·
              refine ⟨69233403710516319512661911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184622409894710185367098429 69233403710516319512661911)
              ·
                refine ⟨103850105565774479268992867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69233403710516319512661911 103850105565774479268992867)
                ·
                  refine ⟨155775158348661718903489301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103850105565774479268992867 155775158348661718903489301)
                  ·
                    refine ⟨7301960547593518073601061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 155775158348661718903489301 7301960547593518073601061)
                    ·
                      refine ⟨1369117602673784638800199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7301960547593518073601061 1369117602673784638800199)
                      ·
                        rfl

theorem cell23_2666347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 4].length) (baseStart_2666347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666347 prefixEnd_2666347 := by exact prefixLift 2666347
  have htrace : WordTrace (prefixWord ++ tailWord_2666347) baseStart_2666347 baseEnd_2666347 := by
    simpa [prefixWord, tailWord_2666347, baseEnd_2666347] using wordTrace_append hprefix tailTrace_2666347
  have hstable : (prefixWord ++ tailWord_2666347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666347).length < 2 ^ (prefixWord ++ tailWord_2666347).sum := by decide
  have hdescent : baseEnd_2666347 < baseStart_2666347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666371 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 3]
def baseStart_2666371 : Nat := 118140960795 + 2666371 * 2 ^ 59
def prefixEnd_2666371 : Nat := 4983230072969 + 3 ^ 40 * 2666371 * 2
def baseEnd_2666371 : Nat := 1369129926209492544900089

theorem tailTrace_2666371 : CollatzResearch.WordTrace tailWord_2666371 prefixEnd_2666371 1369129926209492544900089 := by
  unfold tailWord_2666371
  simp only [CollatzResearch.WordTrace]
  refine ⟨97250539823200721757262967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64833693215467147838175311 97250539823200721757262967)
  ·
    refine ⟨145875809734801082635894451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97250539823200721757262967 145875809734801082635894451)
    ·
      refine ⟨218813714602201623953841677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145875809734801082635894451 218813714602201623953841677)
      ·
        refine ⟨82055142975825608982690629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218813714602201623953841677 82055142975825608982690629)
        ·
          refine ⟨15385339307967301684254493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82055142975825608982690629 15385339307967301684254493)
          ·
            refine ⟨5769502240487738131595435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15385339307967301684254493 5769502240487738131595435)
            ·
              refine ⟨8654253360731607197393153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5769502240487738131595435 8654253360731607197393153)
              ·
                refine ⟨6490690020548705398044865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8654253360731607197393153 6490690020548705398044865)
                ·
                  refine ⟨4868017515411529048533649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6490690020548705398044865 4868017515411529048533649)
                  ·
                    refine ⟨3651013136558646786400237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4868017515411529048533649 3651013136558646786400237)
                    ·
                      refine ⟨1369129926209492544900089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3651013136558646786400237 1369129926209492544900089)
                      ·
                        rfl

theorem cell23_2666371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_2666371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666371 prefixEnd_2666371 := by exact prefixLift 2666371
  have htrace : WordTrace (prefixWord ++ tailWord_2666371) baseStart_2666371 baseEnd_2666371 := by
    simpa [prefixWord, tailWord_2666371, baseEnd_2666371] using wordTrace_append hprefix tailTrace_2666371
  have hstable : (prefixWord ++ tailWord_2666371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666371).length < 2 ^ (prefixWord ++ tailWord_2666371).sum := by decide
  have hdescent : baseEnd_2666371 < baseStart_2666371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666391 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 6]
def baseStart_2666391 : Nat := 118140960795 + 2666391 * 2 ^ 59
def prefixEnd_2666391 : Nat := 4983230072969 + 3 ^ 40 * 2666391 * 2
def baseEnd_2666391 : Nat := 152126688424731385183333

theorem tailTrace_2666391 : CollatzResearch.WordTrace tailWord_2666391 prefixEnd_2666391 152126688424731385183333 := by
  unfold tailWord_2666391
  simp only [CollatzResearch.WordTrace]
  refine ⟨97251269283128265172991027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64834179522085510115327351 97251269283128265172991027)
  ·
    refine ⟨145876903924692397759486541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97251269283128265172991027 145876903924692397759486541)
    ·
      refine ⟨54703838971759649159807453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145876903924692397759486541 54703838971759649159807453)
      ·
        refine ⟨20513939614409868434927795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54703838971759649159807453 20513939614409868434927795)
        ·
          refine ⟨30770909421614802652391693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20513939614409868434927795 30770909421614802652391693)
          ·
            refine ⟨11539091033105550994646885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30770909421614802652391693 11539091033105550994646885)
            ·
              refine ⟨2163579568707290811496291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11539091033105550994646885 2163579568707290811496291)
              ·
                refine ⟨3245369353060936217244437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163579568707290811496291 3245369353060936217244437)
                ·
                  refine ⟨152126688424731385183333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3245369353060936217244437 152126688424731385183333)
                  ·
                    rfl

theorem cell23_2666391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 6].length) (baseStart_2666391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666391 prefixEnd_2666391 := by exact prefixLift 2666391
  have htrace : WordTrace (prefixWord ++ tailWord_2666391) baseStart_2666391 baseEnd_2666391 := by
    simpa [prefixWord, tailWord_2666391, baseEnd_2666391] using wordTrace_append hprefix tailTrace_2666391
  have hstable : (prefixWord ++ tailWord_2666391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666391).length < 2 ^ (prefixWord ++ tailWord_2666391).sum := by decide
  have hdescent : baseEnd_2666391 < baseStart_2666391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666509 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2666509 : Nat := 118140960795 + 2666509 * 2 ^ 59
def prefixEnd_2666509 : Nat := 4983230072969 + 3 ^ 40 * 2666509 * 2
def baseEnd_2666509 : Nat := 1369200786539813004974455

theorem tailTrace_2666509 : CollatzResearch.WordTrace tailWord_2666509 prefixEnd_2666509 1369200786539813004974455 := by
  unfold tailWord_2666509
  simp only [CollatzResearch.WordTrace]
  refine ⟨97255573096700771325786581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64837048731133847550524387 97255573096700771325786581)
  ·
    refine ⟨2279427494453924327948123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 97255573096700771325786581 2279427494453924327948123)
    ·
      refine ⟨3419141241680886491922185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2279427494453924327948123 3419141241680886491922185)
      ·
        refine ⟨2564355931260664868941639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3419141241680886491922185 2564355931260664868941639)
        ·
          refine ⟨3846533896890997303412459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564355931260664868941639 3846533896890997303412459)
          ·
            refine ⟨5769800845336495955118689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846533896890997303412459 5769800845336495955118689)
            ·
              refine ⟨4327350634002371966339017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5769800845336495955118689 4327350634002371966339017)
              ·
                refine ⟨3245512975501778974754263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4327350634002371966339017 3245512975501778974754263)
                ·
                  refine ⟨4868269463252668462131395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3245512975501778974754263 4868269463252668462131395)
                  ·
                    refine ⟨7302404194879002693197093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4868269463252668462131395 7302404194879002693197093)
                    ·
                      refine ⟨1369200786539813004974455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7302404194879002693197093 1369200786539813004974455)
                      ·
                        rfl

theorem cell23_2666509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2666509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666509 prefixEnd_2666509 := by exact prefixLift 2666509
  have htrace : WordTrace (prefixWord ++ tailWord_2666509) baseStart_2666509 baseEnd_2666509 := by
    simpa [prefixWord, tailWord_2666509, baseEnd_2666509] using wordTrace_append hprefix tailTrace_2666509
  have hstable : (prefixWord ++ tailWord_2666509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666509).length < 2 ^ (prefixWord ++ tailWord_2666509).sum := by decide
  have hdescent : baseEnd_2666509 < baseStart_2666509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666582 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_2666582 : Nat := 118140960795 + 2666582 * 2 ^ 59
def prefixEnd_2666582 : Nat := 4983230072969 + 3 ^ 40 * 2666582 * 2
def baseEnd_2666582 : Nat := 1369238270627591219361619

theorem tailTrace_2666582 : CollatzResearch.WordTrace tailWord_2666582 prefixEnd_2666582 1369238270627591219361619 := by
  unfold tailWord_2666582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6078639726589769049574625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64838823750290869862129333 6078639726589769049574625)
  ·
    refine ⟨4558979794942326787180969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6078639726589769049574625 4558979794942326787180969)
    ·
      refine ⟨3419234846206745090385727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4558979794942326787180969 3419234846206745090385727)
      ·
        refine ⟨5128852269310117635578591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3419234846206745090385727 5128852269310117635578591)
        ·
          refine ⟨7693278403965176453367887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5128852269310117635578591 7693278403965176453367887)
          ·
            refine ⟨11539917605947764680051831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7693278403965176453367887 11539917605947764680051831)
            ·
              refine ⟨17309876408921647020077747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11539917605947764680051831 17309876408921647020077747)
              ·
                refine ⟨25964814613382470530116621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17309876408921647020077747 25964814613382470530116621)
                ·
                  refine ⟨9736805480018426448793733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25964814613382470530116621 9736805480018426448793733)
                  ·
                    refine ⟨1825651027503454959148825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9736805480018426448793733 1825651027503454959148825)
                    ·
                      refine ⟨1369238270627591219361619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1825651027503454959148825 1369238270627591219361619)
                      ·
                        rfl

theorem cell23_2666582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_2666582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666582 prefixEnd_2666582 := by exact prefixLift 2666582
  have htrace : WordTrace (prefixWord ++ tailWord_2666582) baseStart_2666582 baseEnd_2666582 := by
    simpa [prefixWord, tailWord_2666582, baseEnd_2666582] using wordTrace_append hprefix tailTrace_2666582
  have hstable : (prefixWord ++ tailWord_2666582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666582).length < 2 ^ (prefixWord ++ tailWord_2666582).sum := by decide
  have hdescent : baseEnd_2666582 < baseStart_2666582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666601 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 2, 5]
def baseStart_2666601 : Nat := 118140960795 + 2666601 * 2 ^ 59
def prefixEnd_2666601 : Nat := 4983230072969 + 3 ^ 40 * 2666601 * 2
def baseEnd_2666601 : Nat := 456416008920008881674677

theorem tailTrace_2666601 : CollatzResearch.WordTrace tailWord_2666601 prefixEnd_2666601 456416008920008881674677 := by
  unfold tailWord_2666601
  simp only [CollatzResearch.WordTrace]
  refine ⟨97258928612367471038135657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64839285741578314025423771 97258928612367471038135657)
  ·
    refine ⟨72944196459275603278601743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97258928612367471038135657 72944196459275603278601743)
    ·
      refine ⟨109416294688913404917902615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72944196459275603278601743 109416294688913404917902615)
      ·
        refine ⟨164124442033370107376853923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109416294688913404917902615 164124442033370107376853923)
        ·
          refine ⟨246186663050055161065280885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164124442033370107376853923 246186663050055161065280885)
          ·
            refine ⟨23079999660942671349870083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246186663050055161065280885 23079999660942671349870083)
            ·
              refine ⟨34619999491414007024805125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23079999660942671349870083 34619999491414007024805125)
              ·
                refine ⟨6491249904640126317150961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34619999491414007024805125 6491249904640126317150961)
                ·
                  refine ⟨4868437428480094737863221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6491249904640126317150961 4868437428480094737863221)
                  ·
                    refine ⟨456416008920008881674677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4868437428480094737863221 456416008920008881674677)
                    ·
                      rfl

theorem cell23_2666601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_2666601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666601 prefixEnd_2666601 := by exact prefixLift 2666601
  have htrace : WordTrace (prefixWord ++ tailWord_2666601) baseStart_2666601 baseEnd_2666601 := by
    simpa [prefixWord, tailWord_2666601, baseEnd_2666601] using wordTrace_append hprefix tailTrace_2666601
  have hstable : (prefixWord ++ tailWord_2666601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666601).length < 2 ^ (prefixWord ++ tailWord_2666601).sum := by decide
  have hdescent : baseEnd_2666601 < baseStart_2666601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666608 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 2, 5, 2]
def baseStart_2666608 : Nat := 118140960795 + 2666608 * 2 ^ 59
def prefixEnd_2666608 : Nat := 4983230072969 + 3 ^ 40 * 2666608 * 2
def baseEnd_2666608 : Nat := 1369251621124608117636499

theorem tailTrace_2666608 : CollatzResearch.WordTrace tailWord_2666608 prefixEnd_2666608 1369251621124608117636499 := by
  unfold tailWord_2666608
  simp only [CollatzResearch.WordTrace]
  refine ⟨48629591961671055616820239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64839455948894740822426985 48629591961671055616820239)
  ·
    refine ⟨72944387942506583425230359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48629591961671055616820239 72944387942506583425230359)
    ·
      refine ⟨109416581913759875137845539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72944387942506583425230359 109416581913759875137845539)
      ·
        refine ⟨164124872870639812706768309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109416581913759875137845539 164124872870639812706768309)
        ·
          refine ⟨15386706831622482441259529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164124872870639812706768309 15386706831622482441259529)
          ·
            refine ⟨11540030123716861830944647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15386706831622482441259529 11540030123716861830944647)
            ·
              refine ⟨17310045185575292746416971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11540030123716861830944647 17310045185575292746416971)
              ·
                refine ⟨25965067778362939119625457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17310045185575292746416971 25965067778362939119625457)
                ·
                  refine ⟨19473800833772204339719093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25965067778362939119625457 19473800833772204339719093)
                  ·
                    refine ⟨1825668828166144156848665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19473800833772204339719093 1825668828166144156848665)
                    ·
                      refine ⟨1369251621124608117636499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1825668828166144156848665 1369251621124608117636499)
                      ·
                        rfl

theorem cell23_2666608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 5, 2].length) (baseStart_2666608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666608 prefixEnd_2666608 := by exact prefixLift 2666608
  have htrace : WordTrace (prefixWord ++ tailWord_2666608) baseStart_2666608 baseEnd_2666608 := by
    simpa [prefixWord, tailWord_2666608, baseEnd_2666608] using wordTrace_append hprefix tailTrace_2666608
  have hstable : (prefixWord ++ tailWord_2666608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666608).length < 2 ^ (prefixWord ++ tailWord_2666608).sum := by decide
  have hdescent : baseEnd_2666608 < baseStart_2666608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666655 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 2, 4, 2]
def baseStart_2666655 : Nat := 118140960795 + 2666655 * 2 ^ 59
def prefixEnd_2666655 : Nat := 4983230072969 + 3 ^ 40 * 2666655 * 2
def baseEnd_2666655 : Nat := 1369275754715369433748783

theorem tailTrace_2666655 : CollatzResearch.WordTrace tailWord_2666655 prefixEnd_2666655 1369275754715369433748783 := by
  unfold tailWord_2666655
  simp only [CollatzResearch.WordTrace]
  refine ⟨97260898154171838260601419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64840598769447892173734279 97260898154171838260601419)
  ·
    refine ⟨145891347231257757390902129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97260898154171838260601419 145891347231257757390902129)
    ·
      refine ⟨109418510423443318043176597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145891347231257757390902129 109418510423443318043176597)
      ·
        refine ⟨5128992676098905533273903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109418510423443318043176597 5128992676098905533273903)
        ·
          refine ⟨7693489014148358299910855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5128992676098905533273903 7693489014148358299910855)
          ·
            refine ⟨11540233521222537449866283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7693489014148358299910855 11540233521222537449866283)
            ·
              refine ⟨17310350281833806174799425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11540233521222537449866283 17310350281833806174799425)
              ·
                refine ⟨12982762711375354631099569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17310350281833806174799425 12982762711375354631099569)
                ·
                  refine ⟨9737072033531515973324677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12982762711375354631099569 9737072033531515973324677)
                  ·
                    refine ⟨1825701006287159244998377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9737072033531515973324677 1825701006287159244998377)
                    ·
                      refine ⟨1369275754715369433748783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1825701006287159244998377 1369275754715369433748783)
                      ·
                        rfl

theorem cell23_2666655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_2666655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666655 prefixEnd_2666655 := by exact prefixLift 2666655
  have htrace : WordTrace (prefixWord ++ tailWord_2666655) baseStart_2666655 baseEnd_2666655 := by
    simpa [prefixWord, tailWord_2666655, baseEnd_2666655] using wordTrace_append hprefix tailTrace_2666655
  have hstable : (prefixWord ++ tailWord_2666655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666655).length < 2 ^ (prefixWord ++ tailWord_2666655).sum := by decide
  have hdescent : baseEnd_2666655 < baseStart_2666655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666661 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 8]
def baseStart_2666661 : Nat := 118140960795 + 2666661 * 2 ^ 59
def prefixEnd_2666661 : Nat := 4983230072969 + 3 ^ 40 * 2666661 * 2
def baseEnd_2666661 : Nat := 152142092844366267808195

theorem tailTrace_2666661 : CollatzResearch.WordTrace tailWord_2666661 prefixEnd_2666661 152142092844366267808195 := by
  unfold tailWord_2666661
  simp only [CollatzResearch.WordTrace]
  refine ⟨97261116992150101285319837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64840744661433400856879891 97261116992150101285319837)
  ·
    refine ⟨36472918872056287981994939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97261116992150101285319837 36472918872056287981994939)
    ·
      refine ⟨54709378308084431972992409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36472918872056287981994939 54709378308084431972992409)
      ·
        refine ⟨41032033731063323979744307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54709378308084431972992409 41032033731063323979744307)
        ·
          refine ⟨61548050596594985969616461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41032033731063323979744307 61548050596594985969616461)
          ·
            refine ⟨23080518973723119738606173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61548050596594985969616461 23080518973723119738606173)
            ·
              refine ⟨8655194615146169901977315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23080518973723119738606173 8655194615146169901977315)
              ·
                refine ⟨12982791922719254852965973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8655194615146169901977315 12982791922719254852965973)
                ·
                  refine ⟨152142092844366267808195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12982791922719254852965973 152142092844366267808195)
                  ·
                    rfl

theorem cell23_2666661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_2666661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666661 prefixEnd_2666661 := by exact prefixLift 2666661
  have htrace : WordTrace (prefixWord ++ tailWord_2666661) baseStart_2666661 baseEnd_2666661 := by
    simpa [prefixWord, tailWord_2666661, baseEnd_2666661] using wordTrace_append hprefix tailTrace_2666661
  have hstable : (prefixWord ++ tailWord_2666661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666661).length < 2 ^ (prefixWord ++ tailWord_2666661).sum := by decide
  have hdescent : baseEnd_2666661 < baseStart_2666661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666681 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2666681 : Nat := 118140960795 + 2666681 * 2 ^ 59
def prefixEnd_2666681 : Nat := 4983230072969 + 3 ^ 40 * 2666681 * 2
def baseEnd_2666681 : Nat := 1369289105212386332023663

theorem tailTrace_2666681 : CollatzResearch.WordTrace tailWord_2666681 prefixEnd_2666681 1369289105212386332023663 := by
  unfold tailWord_2666681
  simp only [CollatzResearch.WordTrace]
  refine ⟨97261846452077644701047897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64841230968051763134031931 97261846452077644701047897)
  ·
    refine ⟨72946384839058233525785923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97261846452077644701047897 72946384839058233525785923)
    ·
      refine ⟨109419577258587350288678885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72946384839058233525785923 109419577258587350288678885)
      ·
        refine ⟨20516170735985128179127291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109419577258587350288678885 20516170735985128179127291)
        ·
          refine ⟨30774256103977692268690937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20516170735985128179127291 30774256103977692268690937)
          ·
            refine ⟨23080692077983269201518203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30774256103977692268690937 23080692077983269201518203)
            ·
              refine ⟨34621038116974903802277305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23080692077983269201518203 34621038116974903802277305)
              ·
                refine ⟨25965778587731177851707979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34621038116974903802277305 25965778587731177851707979)
                ·
                  refine ⟨38948667881596766777561969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25965778587731177851707979 38948667881596766777561969)
                  ·
                    refine ⟨29211500911197575083171477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38948667881596766777561969 29211500911197575083171477)
                    ·
                      refine ⟨1369289105212386332023663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29211500911197575083171477 1369289105212386332023663)
                      ·
                        rfl

theorem cell23_2666681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2666681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666681 prefixEnd_2666681 := by exact prefixLift 2666681
  have htrace : WordTrace (prefixWord ++ tailWord_2666681) baseStart_2666681 baseEnd_2666681 := by
    simpa [prefixWord, tailWord_2666681, baseEnd_2666681] using wordTrace_append hprefix tailTrace_2666681
  have hstable : (prefixWord ++ tailWord_2666681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666681).length < 2 ^ (prefixWord ++ tailWord_2666681).sum := by decide
  have hdescent : baseEnd_2666681 < baseStart_2666681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666691 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 7, 5]
def baseStart_2666691 : Nat := 118140960795 + 2666691 * 2 ^ 59
def prefixEnd_2666691 : Nat := 4983230072969 + 3 ^ 40 * 2666691 * 2
def baseEnd_2666691 : Nat := 456431413339643764299539

theorem tailTrace_2666691 : CollatzResearch.WordTrace tailWord_2666691 prefixEnd_2666691 456431413339643764299539 := by
  unfold tailWord_2666691
  simp only [CollatzResearch.WordTrace]
  refine ⟨97262211182041416408911927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64841474121360944272607951 97262211182041416408911927)
  ·
    refine ⟨145893316773062124613367891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97262211182041416408911927 145893316773062124613367891)
    ·
      refine ⟨218839975159593186920051837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145893316773062124613367891 218839975159593186920051837)
      ·
        refine ⟨82064990684847445095019439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218839975159593186920051837 82064990684847445095019439)
        ·
          refine ⟨123097486027271167642529159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82064990684847445095019439 123097486027271167642529159)
          ·
            refine ⟨184646229040906751463793739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123097486027271167642529159 184646229040906751463793739)
            ·
              refine ⟨276969343561360127195690609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184646229040906751463793739 276969343561360127195690609)
              ·
                refine ⟨207727007671020095396767957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276969343561360127195690609 207727007671020095396767957)
                ·
                  refine ⟨4868601742289533485861749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 207727007671020095396767957 4868601742289533485861749)
                  ·
                    refine ⟨456431413339643764299539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4868601742289533485861749 456431413339643764299539)
                    ·
                      rfl

theorem cell23_2666691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 5].length) (baseStart_2666691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666691 prefixEnd_2666691 := by exact prefixLift 2666691
  have htrace : WordTrace (prefixWord ++ tailWord_2666691) baseStart_2666691 baseEnd_2666691 := by
    simpa [prefixWord, tailWord_2666691, baseEnd_2666691] using wordTrace_append hprefix tailTrace_2666691
  have hstable : (prefixWord ++ tailWord_2666691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666691).length < 2 ^ (prefixWord ++ tailWord_2666691).sum := by decide
  have hdescent : baseEnd_2666691 < baseStart_2666691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666716 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2666716 : Nat := 118140960795 + 2666716 * 2 ^ 59
def prefixEnd_2666716 : Nat := 4983230072969 + 3 ^ 40 * 2666716 * 2
def baseEnd_2666716 : Nat := 456435692345097898362001

theorem tailTrace_2666716 : CollatzResearch.WordTrace tailWord_2666716 prefixEnd_2666716 456435692345097898362001 := by
  unfold tailWord_2666716
  simp only [CollatzResearch.WordTrace]
  refine ⟨48631561503475422839286001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64842082004633897119048001 48631561503475422839286001)
  ·
    refine ⟨36473671127606567129464501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48631561503475422839286001 36473671127606567129464501)
    ·
      refine ⟨3419406668213115668387297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36473671127606567129464501 3419406668213115668387297)
      ·
        refine ⟨2564555001159836751290473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3419406668213115668387297 2564555001159836751290473)
        ·
          refine ⟨1923416250869877563467855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2564555001159836751290473 1923416250869877563467855)
          ·
            refine ⟨2885124376304816345201783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923416250869877563467855 2885124376304816345201783)
            ·
              refine ⟨4327686564457224517802675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885124376304816345201783 4327686564457224517802675)
              ·
                refine ⟨6491529846685836776704013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327686564457224517802675 6491529846685836776704013)
                ·
                  refine ⟨2434323692507188791264005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6491529846685836776704013 2434323692507188791264005)
                  ·
                    refine ⟨456435692345097898362001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2434323692507188791264005 456435692345097898362001)
                    ·
                      rfl

theorem cell23_2666716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2666716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666716 prefixEnd_2666716 := by exact prefixLift 2666716
  have htrace : WordTrace (prefixWord ++ tailWord_2666716) baseStart_2666716 baseEnd_2666716 := by
    simpa [prefixWord, tailWord_2666716, baseEnd_2666716] using wordTrace_append hprefix tailTrace_2666716
  have hstable : (prefixWord ++ tailWord_2666716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666716).length < 2 ^ (prefixWord ++ tailWord_2666716).sum := by decide
  have hdescent : baseEnd_2666716 < baseStart_2666716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666751 : List Nat := [1, 1, 2, 2, 1, 4, 1, 11]
def baseStart_2666751 : Nat := 118140960795 + 2666751 * 2 ^ 59
def prefixEnd_2666751 : Nat := 4983230072969 + 3 ^ 40 * 2666751 * 2
def baseEnd_2666751 : Nat := 50715742550303742894383

theorem tailTrace_2666751 : CollatzResearch.WordTrace tailWord_2666751 prefixEnd_2666751 50715742550303742894383 := by
  unfold tailWord_2666751
  simp only [CollatzResearch.WordTrace]
  refine ⟨97264399561824046656096107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64842933041216031104064071 97264399561824046656096107)
  ·
    refine ⟨145896599342736069984144161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97264399561824046656096107 145896599342736069984144161)
    ·
      refine ⟨109422449507052052488108121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145896599342736069984144161 109422449507052052488108121)
      ·
        refine ⟨82066837130289039366081091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109422449507052052488108121 82066837130289039366081091)
        ·
          refine ⟨123100255695433559049121637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82066837130289039366081091 123100255695433559049121637)
          ·
            refine ⟨23081297942893792321710307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123100255695433559049121637 23081297942893792321710307)
            ·
              refine ⟨34621946914340688482565461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23081297942893792321710307 34621946914340688482565461)
              ·
                refine ⟨50715742550303742894383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 34621946914340688482565461 50715742550303742894383)
                ·
                  rfl

theorem cell23_2666751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 11].length) (baseStart_2666751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666751 prefixEnd_2666751 := by exact prefixLift 2666751
  have htrace : WordTrace (prefixWord ++ tailWord_2666751) baseStart_2666751 baseEnd_2666751 := by
    simpa [prefixWord, tailWord_2666751, baseEnd_2666751] using wordTrace_append hprefix tailTrace_2666751
  have hstable : (prefixWord ++ tailWord_2666751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666751).length < 2 ^ (prefixWord ++ tailWord_2666751).sum := by decide
  have hdescent : baseEnd_2666751 < baseStart_2666751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666759 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 1, 5]
def baseStart_2666759 : Nat := 118140960795 + 2666759 * 2 ^ 59
def prefixEnd_2666759 : Nat := 4983230072969 + 3 ^ 40 * 2666759 * 2
def baseEnd_2666759 : Nat := 456443052234479008949435

theorem tailTrace_2666759 : CollatzResearch.WordTrace tailWord_2666759 prefixEnd_2666759 456443052234479008949435 := by
  unfold tailWord_2666759
  simp only [CollatzResearch.WordTrace]
  refine ⟨97264691345795064022387331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64843127563863376014924887 97264691345795064022387331)
  ·
    refine ⟨145897037018692596033580997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97264691345795064022387331 145897037018692596033580997)
    ·
      refine ⟨27355694441004861756296437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145897037018692596033580997 27355694441004861756296437)
      ·
        refine ⟨2564596353844205789652791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27355694441004861756296437 2564596353844205789652791)
        ·
          refine ⟨3846894530766308684479187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564596353844205789652791 3846894530766308684479187)
          ·
            refine ⟨5770341796149463026718781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846894530766308684479187 5770341796149463026718781)
            ·
              refine ⟨2163878173556048635019543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5770341796149463026718781 2163878173556048635019543)
              ·
                refine ⟨3245817260334072952529315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163878173556048635019543 3245817260334072952529315)
                ·
                  refine ⟨4868725890501109428793973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3245817260334072952529315 4868725890501109428793973)
                  ·
                    refine ⟨456443052234479008949435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4868725890501109428793973 456443052234479008949435)
                    ·
                      rfl

theorem cell23_2666759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_2666759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666759 prefixEnd_2666759 := by exact prefixLift 2666759
  have htrace : WordTrace (prefixWord ++ tailWord_2666759) baseStart_2666759 baseEnd_2666759 := by
    simpa [prefixWord, tailWord_2666759, baseEnd_2666759] using wordTrace_append hprefix tailTrace_2666759
  have hstable : (prefixWord ++ tailWord_2666759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666759).length < 2 ^ (prefixWord ++ tailWord_2666759).sum := by decide
  have hdescent : baseEnd_2666759 < baseStart_2666759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666792 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2666792 : Nat := 118140960795 + 2666792 * 2 ^ 59
def prefixEnd_2666792 : Nat := 4983230072969 + 3 ^ 40 * 2666792 * 2
def baseEnd_2666792 : Nat := 1369346101565035397735653

theorem tailTrace_2666792 : CollatzResearch.WordTrace tailWord_2666792 prefixEnd_2666792 1369346101565035397735653 := by
  unfold tailWord_2666792
  simp only [CollatzResearch.WordTrace]
  refine ⟨48632947477337755329169315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64843929969783673772225753 48632947477337755329169315)
  ·
    refine ⟨72949421216006632993753973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48632947477337755329169315 72949421216006632993753973)
    ·
      refine ⟨6839008239000621843164435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72949421216006632993753973 6839008239000621843164435)
      ·
        refine ⟨10258512358500932764746653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6839008239000621843164435 10258512358500932764746653)
        ·
          refine ⟨3846942134437849786779995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10258512358500932764746653 3846942134437849786779995)
          ·
            refine ⟨5770413201656774680169993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846942134437849786779995 5770413201656774680169993)
            ·
              refine ⟨4327809901242581010127495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5770413201656774680169993 4327809901242581010127495)
              ·
                refine ⟨6491714851863871515191243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327809901242581010127495 6491714851863871515191243)
                ·
                  refine ⟨9737572277795807272786865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6491714851863871515191243 9737572277795807272786865)
                  ·
                    refine ⟨7303179208346855454590149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9737572277795807272786865 7303179208346855454590149)
                    ·
                      refine ⟨1369346101565035397735653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7303179208346855454590149 1369346101565035397735653)
                      ·
                        rfl

theorem cell23_2666792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2666792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666792 prefixEnd_2666792 := by exact prefixLift 2666792
  have htrace : WordTrace (prefixWord ++ tailWord_2666792) baseStart_2666792 baseEnd_2666792 := by
    simpa [prefixWord, tailWord_2666792, baseEnd_2666792] using wordTrace_append hprefix tailTrace_2666792
  have hstable : (prefixWord ++ tailWord_2666792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666792).length < 2 ^ (prefixWord ++ tailWord_2666792).sum := by decide
  have hdescent : baseEnd_2666792 < baseStart_2666792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666828 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_2666828 : Nat := 118140960795 + 2666828 * 2 ^ 59
def prefixEnd_2666828 : Nat := 4983230072969 + 3 ^ 40 * 2666828 * 2
def baseEnd_2666828 : Nat := 456454862289532418961829

theorem tailTrace_2666828 : CollatzResearch.WordTrace tailWord_2666828 prefixEnd_2666828 456454862289532418961829 := by
  unfold tailWord_2666828
  simp only [CollatzResearch.WordTrace]
  refine ⟨48633603991272544403324569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64844805321696725871099425 48633603991272544403324569)
  ·
    refine ⟨36475202993454408302493427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48633603991272544403324569 36475202993454408302493427)
    ·
      refine ⟨54712804490181612453740141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36475202993454408302493427 54712804490181612453740141)
      ·
        refine ⟨20517301683818104670152553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54712804490181612453740141 20517301683818104670152553)
        ·
          refine ⟨15387976262863578502614415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20517301683818104670152553 15387976262863578502614415)
          ·
            refine ⟨23081964394295367753921623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15387976262863578502614415 23081964394295367753921623)
            ·
              refine ⟨34622946591443051630882435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23081964394295367753921623 34622946591443051630882435)
              ·
                refine ⟨51934419887164577446323653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34622946591443051630882435 51934419887164577446323653)
                ·
                  refine ⟨9737703728843358271185685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51934419887164577446323653 9737703728843358271185685)
                  ·
                    refine ⟨456454862289532418961829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9737703728843358271185685 456454862289532418961829)
                    ·
                      rfl

theorem cell23_2666828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_2666828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666828 prefixEnd_2666828 := by exact prefixLift 2666828
  have htrace : WordTrace (prefixWord ++ tailWord_2666828) baseStart_2666828 baseEnd_2666828 := by
    simpa [prefixWord, tailWord_2666828, baseEnd_2666828] using wordTrace_append hprefix tailTrace_2666828
  have hstable : (prefixWord ++ tailWord_2666828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666828).length < 2 ^ (prefixWord ++ tailWord_2666828).sum := by decide
  have hdescent : baseEnd_2666828 < baseStart_2666828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666869 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_2666869 : Nat := 118140960795 + 2666869 * 2 ^ 59
def prefixEnd_2666869 : Nat := 4983230072969 + 3 ^ 40 * 2666869 * 2
def baseEnd_2666869 : Nat := 1369385639575431596472799

theorem tailTrace_2666869 : CollatzResearch.WordTrace tailWord_2666869 prefixEnd_2666869 1369385639575431596472799 := by
  unfold tailWord_2666869
  simp only [CollatzResearch.WordTrace]
  refine ⟨97268703375396552808891661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64845802250264368539261107 97268703375396552808891661)
  ·
    refine ⟨36475763765773707303334373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97268703375396552808891661 36475763765773707303334373)
    ·
      refine ⟨6839205706082570119375195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36475763765773707303334373 6839205706082570119375195)
      ·
        refine ⟨10258808559123855179062793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6839205706082570119375195 10258808559123855179062793)
        ·
          refine ⟨7694106419342891384297095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10258808559123855179062793 7694106419342891384297095)
          ·
            refine ⟨11541159629014337076445643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7694106419342891384297095 11541159629014337076445643)
            ·
              refine ⟨17311739443521505614668465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11541159629014337076445643 17311739443521505614668465)
              ·
                refine ⟨12983804582641129211001349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17311739443521505614668465 12983804582641129211001349)
                ·
                  refine ⟨2434463359245211727062753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12983804582641129211001349 2434463359245211727062753)
                  ·
                    refine ⟨1825847519433908795297065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2434463359245211727062753 1825847519433908795297065)
                    ·
                      refine ⟨1369385639575431596472799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1825847519433908795297065 1369385639575431596472799)
                      ·
                        rfl

theorem cell23_2666869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_2666869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666869 prefixEnd_2666869 := by exact prefixLift 2666869
  have htrace : WordTrace (prefixWord ++ tailWord_2666869) baseStart_2666869 baseEnd_2666869 := by
    simpa [prefixWord, tailWord_2666869, baseEnd_2666869] using wordTrace_append hprefix tailTrace_2666869
  have hstable : (prefixWord ++ tailWord_2666869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666869).length < 2 ^ (prefixWord ++ tailWord_2666869).sum := by decide
  have hdescent : baseEnd_2666869 < baseStart_2666869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666942 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_2666942 : Nat := 118140960795 + 2666942 * 2 ^ 59
def prefixEnd_2666942 : Nat := 4983230072969 + 3 ^ 40 * 2666942 * 2
def baseEnd_2666942 : Nat := 1369423123663209810859963

theorem tailTrace_2666942 : CollatzResearch.WordTrace tailWord_2666942 prefixEnd_2666942 1369423123663209810859963 := by
  unfold tailWord_2666942
  simp only [CollatzResearch.WordTrace]
  refine ⟨12158920738016510784537385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64847577269421390850866053 12158920738016510784537385)
  ·
    refine ⟨9119190553512383088403039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12158920738016510784537385 9119190553512383088403039)
    ·
      refine ⟨13678785830268574632604559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9119190553512383088403039 13678785830268574632604559)
      ·
        refine ⟨20518178745402861948906839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13678785830268574632604559 20518178745402861948906839)
        ·
          refine ⟨30777268118104292923360259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20518178745402861948906839 30777268118104292923360259)
          ·
            refine ⟨46165902177156439385040389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30777268118104292923360259 46165902177156439385040389)
            ·
              refine ⟨8656106658216832384695073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46165902177156439385040389 8656106658216832384695073)
              ·
                refine ⟨6492079993662624288521305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8656106658216832384695073 6492079993662624288521305)
                ·
                  refine ⟨4869059995246968216390979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6492079993662624288521305 4869059995246968216390979)
                  ·
                    refine ⟨7303589992870452324586469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4869059995246968216390979 7303589992870452324586469)
                    ·
                      refine ⟨1369423123663209810859963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7303589992870452324586469 1369423123663209810859963)
                      ·
                        rfl

theorem cell23_2666942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_2666942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666942 prefixEnd_2666942 := by exact prefixLift 2666942
  have htrace : WordTrace (prefixWord ++ tailWord_2666942) baseStart_2666942 baseEnd_2666942 := by
    simpa [prefixWord, tailWord_2666942, baseEnd_2666942] using wordTrace_append hprefix tailTrace_2666942
  have hstable : (prefixWord ++ tailWord_2666942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666942).length < 2 ^ (prefixWord ++ tailWord_2666942).sum := by decide
  have hdescent : baseEnd_2666942 < baseStart_2666942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666986 : List Nat := [3, 1, 3, 1, 3, 2, 2, 3, 1, 4]
def baseStart_2666986 : Nat := 118140960795 + 2666986 * 2 ^ 59
def prefixEnd_2666986 : Nat := 4983230072969 + 3 ^ 40 * 2666986 * 2
def baseEnd_2666986 : Nat := 456481905604002546236587

theorem tailTrace_2666986 : CollatzResearch.WordTrace tailWord_2666986 prefixEnd_2666986 456481905604002546236587 := by
  unfold tailWord_2666986
  simp only [CollatzResearch.WordTrace]
  refine ⟨24318242678993170447725203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64848647143981787860600541 24318242678993170447725203)
  ·
    refine ⟨36477364018489755671587805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24318242678993170447725203 36477364018489755671587805)
    ·
      refine ⟨13679011506933658376845427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36477364018489755671587805 13679011506933658376845427)
      ·
        refine ⟨20518517260400487565268141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13679011506933658376845427 20518517260400487565268141)
        ·
          refine ⟨7694443972650182836975553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20518517260400487565268141 7694443972650182836975553)
          ·
            refine ⟨5770832979487637127731665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7694443972650182836975553 5770832979487637127731665)
            ·
              refine ⟨4328124734615727845798749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5770832979487637127731665 4328124734615727845798749)
              ·
                refine ⟨1623046775480897942174531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4328124734615727845798749 1623046775480897942174531)
                ·
                  refine ⟨2434570163221346913261797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623046775480897942174531 2434570163221346913261797)
                  ·
                    refine ⟨456481905604002546236587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2434570163221346913261797 456481905604002546236587)
                    ·
                      rfl

theorem cell23_2666986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_2666986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666986 prefixEnd_2666986 := by exact prefixLift 2666986
  have htrace : WordTrace (prefixWord ++ tailWord_2666986) baseStart_2666986 baseEnd_2666986 := by
    simpa [prefixWord, tailWord_2666986, baseEnd_2666986] using wordTrace_append hprefix tailTrace_2666986
  have hstable : (prefixWord ++ tailWord_2666986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666986).length < 2 ^ (prefixWord ++ tailWord_2666986).sum := by decide
  have hdescent : baseEnd_2666986 < baseStart_2666986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2666992 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 5, 1, 3]
def baseStart_2666992 : Nat := 118140960795 + 2666992 * 2 ^ 59
def prefixEnd_2666992 : Nat := 4983230072969 + 3 ^ 40 * 2666992 * 2
def baseEnd_2666992 : Nat := 1369448797695934615234733

theorem tailTrace_2666992 : CollatzResearch.WordTrace tailWord_2666992 prefixEnd_2666992 1369448797695934615234733 := by
  unfold tailWord_2666992
  simp only [CollatzResearch.WordTrace]
  refine ⟨48636594776975472407809615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64848793035967296543746153 48636594776975472407809615)
  ·
    refine ⟨72954892165463208611714423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48636594776975472407809615 72954892165463208611714423)
    ·
      refine ⟨109432338248194812917571635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72954892165463208611714423 109432338248194812917571635)
      ·
        refine ⟨164148507372292219376357453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109432338248194812917571635 164148507372292219376357453)
        ·
          refine ⟨61555690264609582266134045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164148507372292219376357453 61555690264609582266134045)
          ·
            refine ⟨23083383849228593349800267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61555690264609582266134045 23083383849228593349800267)
            ·
              refine ⟨34625075773842890024700401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23083383849228593349800267 34625075773842890024700401)
              ·
                refine ⟨25968806830382167518525301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34625075773842890024700401 25968806830382167518525301)
                ·
                  refine ⟨2434575640348328204861747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25968806830382167518525301 2434575640348328204861747)
                  ·
                    refine ⟨3651863460522492307292621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2434575640348328204861747 3651863460522492307292621)
                    ·
                      refine ⟨1369448797695934615234733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3651863460522492307292621 1369448797695934615234733)
                      ·
                        rfl

theorem cell23_2666992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5, 1, 3].length) (baseStart_2666992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2666992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2666992 prefixEnd_2666992 := by exact prefixLift 2666992
  have htrace : WordTrace (prefixWord ++ tailWord_2666992) baseStart_2666992 baseEnd_2666992 := by
    simpa [prefixWord, tailWord_2666992, baseEnd_2666992] using wordTrace_append hprefix tailTrace_2666992
  have hstable : (prefixWord ++ tailWord_2666992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2666992).length < 2 ^ (prefixWord ++ tailWord_2666992).sum := by decide
  have hdescent : baseEnd_2666992 < baseStart_2666992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2666992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667009 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_2667009 : Nat := 118140960795 + 2667009 * 2 ^ 59
def prefixEnd_2667009 : Nat := 4983230072969 + 3 ^ 40 * 2667009 * 2
def baseEnd_2667009 : Nat := 1369457526867061048722155

theorem tailTrace_2667009 : CollatzResearch.WordTrace tailWord_2667009 prefixEnd_2667009 1369457526867061048722155 := by
  unfold tailWord_2667009
  simp only [CollatzResearch.WordTrace]
  refine ⟨97273809594889356718988081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64849206396592904479325387 97273809594889356718988081)
  ·
    refine ⟨72955357196167017539241061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97273809594889356718988081 72955357196167017539241061)
    ·
      refine ⟨13679129474281315788607699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72955357196167017539241061 13679129474281315788607699)
      ·
        refine ⟨20518694211421973682911549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13679129474281315788607699 20518694211421973682911549)
        ·
          refine ⟨7694510329283240131091831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20518694211421973682911549 7694510329283240131091831)
          ·
            refine ⟨11541765493924860196637747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7694510329283240131091831 11541765493924860196637747)
            ·
              refine ⟨17312648240887290294956621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11541765493924860196637747 17312648240887290294956621)
              ·
                refine ⟨6492243090332733860608733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17312648240887290294956621 6492243090332733860608733)
                ·
                  refine ⟨2434591158874775197728275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6492243090332733860608733 2434591158874775197728275)
                  ·
                    refine ⟨3651886738312162796592413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2434591158874775197728275 3651886738312162796592413)
                    ·
                      refine ⟨1369457526867061048722155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3651886738312162796592413 1369457526867061048722155)
                      ·
                        rfl

theorem cell23_2667009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_2667009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667009 prefixEnd_2667009 := by exact prefixLift 2667009
  have htrace : WordTrace (prefixWord ++ tailWord_2667009) baseStart_2667009 baseEnd_2667009 := by
    simpa [prefixWord, tailWord_2667009, baseEnd_2667009] using wordTrace_append hprefix tailTrace_2667009
  have hstable : (prefixWord ++ tailWord_2667009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667009).length < 2 ^ (prefixWord ++ tailWord_2667009).sum := by decide
  have hdescent : baseEnd_2667009 < baseStart_2667009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667025 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 1, 6]
def baseStart_2667025 : Nat := 118140960795 + 2667025 * 2 ^ 59
def prefixEnd_2667025 : Nat := 4983230072969 + 3 ^ 40 * 2667025 * 2
def baseEnd_2667025 : Nat := 456488580852510995374027

theorem tailTrace_2667025 : CollatzResearch.WordTrace tailWord_2667025 prefixEnd_2667025 456488580852510995374027 := by
  unfold tailWord_2667025
  simp only [CollatzResearch.WordTrace]
  refine ⟨97274393162831391451570529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64849595441887594301047019 97274393162831391451570529)
  ·
    refine ⟨72955794872123543588677897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97274393162831391451570529 72955794872123543588677897)
    ·
      refine ⟨54716846154092657691508423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72955794872123543588677897 54716846154092657691508423)
      ·
        refine ⟨82075269231138986537262635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54716846154092657691508423 82075269231138986537262635)
        ·
          refine ⟨123112903846708479805893953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82075269231138986537262635 123112903846708479805893953)
          ·
            refine ⟨92334677885031359854420465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123112903846708479805893953 92334677885031359854420465)
            ·
              refine ⟨69251008413773519890815349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92334677885031359854420465 69251008413773519890815349)
              ·
                refine ⟨6492282038791267489763939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69251008413773519890815349 6492282038791267489763939)
                ·
                  refine ⟨9738423058186901234645909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6492282038791267489763939 9738423058186901234645909)
                  ·
                    refine ⟨456488580852510995374027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9738423058186901234645909 456488580852510995374027)
                    ·
                      rfl

theorem cell23_2667025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_2667025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667025 prefixEnd_2667025 := by exact prefixLift 2667025
  have htrace : WordTrace (prefixWord ++ tailWord_2667025) baseStart_2667025 baseEnd_2667025 := by
    simpa [prefixWord, tailWord_2667025, baseEnd_2667025] using wordTrace_append hprefix tailTrace_2667025
  have hstable : (prefixWord ++ tailWord_2667025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667025).length < 2 ^ (prefixWord ++ tailWord_2667025).sum := by decide
  have hdescent : baseEnd_2667025 < baseStart_2667025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667035 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 3]
def baseStart_2667035 : Nat := 118140960795 + 2667035 * 2 ^ 59
def prefixEnd_2667035 : Nat := 4983230072969 + 3 ^ 40 * 2667035 * 2
def baseEnd_2667035 : Nat := 1369470877364077946997035

theorem tailTrace_2667035 : CollatzResearch.WordTrace tailWord_2667035 prefixEnd_2667035 1369470877364077946997035 := by
  unfold tailWord_2667035
  simp only [CollatzResearch.WordTrace]
  refine ⟨97274757892795163159434559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64849838595196775439623039 97274757892795163159434559)
  ·
    refine ⟨145912136839192744739151839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97274757892795163159434559 145912136839192744739151839)
    ·
      refine ⟨218868205258789117108727759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145912136839192744739151839 218868205258789117108727759)
      ·
        refine ⟨328302307888183675663091639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218868205258789117108727759 328302307888183675663091639)
        ·
          refine ⟨492453461832275513494637459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328302307888183675663091639 492453461832275513494637459)
          ·
            refine ⟨738680192748413270241956189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492453461832275513494637459 738680192748413270241956189)
            ·
              refine ⟨277005072280654976340733571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 738680192748413270241956189 277005072280654976340733571)
              ·
                refine ⟨415507608420982464511100357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277005072280654976340733571 415507608420982464511100357)
                ·
                  refine ⟨77907676578934212095831317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415507608420982464511100357 77907676578934212095831317)
                  ·
                    refine ⟨3651922339637541191992093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77907676578934212095831317 3651922339637541191992093)
                    ·
                      refine ⟨1369470877364077946997035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3651922339637541191992093 1369470877364077946997035)
                      ·
                        rfl

theorem cell23_2667035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 3].length) (baseStart_2667035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667035 prefixEnd_2667035 := by exact prefixLift 2667035
  have htrace : WordTrace (prefixWord ++ tailWord_2667035) baseStart_2667035 baseEnd_2667035 := by
    simpa [prefixWord, tailWord_2667035, baseEnd_2667035] using wordTrace_append hprefix tailTrace_2667035
  have hstable : (prefixWord ++ tailWord_2667035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667035).length < 2 ^ (prefixWord ++ tailWord_2667035).sum := by decide
  have hdescent : baseEnd_2667035 < baseStart_2667035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667043 : List Nat := [1, 1, 1, 4, 4, 3, 1, 3, 1, 1, 3]
def baseStart_2667043 : Nat := 118140960795 + 2667043 * 2 ^ 59
def prefixEnd_2667043 : Nat := 4983230072969 + 3 ^ 40 * 2667043 * 2
def baseEnd_2667043 : Nat := 1369474985209313915696999

theorem tailTrace_2667043 : CollatzResearch.WordTrace tailWord_2667043 prefixEnd_2667043 1369474985209313915696999 := by
  unfold tailWord_2667043
  simp only [CollatzResearch.WordTrace]
  refine ⟨97275049676766180525725783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64850033117844120350483855 97275049676766180525725783)
  ·
    refine ⟨145912574515149270788588675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97275049676766180525725783 145912574515149270788588675)
    ·
      refine ⟨218868861772723906182883013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145912574515149270788588675 218868861772723906182883013)
      ·
        refine ⟨41037911582385732409290565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218868861772723906182883013 41037911582385732409290565)
        ·
          refine ⟨7694608421697324826741981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41037911582385732409290565 7694608421697324826741981)
          ·
            refine ⟨2885478158136496810028243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7694608421697324826741981 2885478158136496810028243)
            ·
              refine ⟨4328217237204745215042365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885478158136496810028243 4328217237204745215042365)
              ·
                refine ⟨1623081463951779455640887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4328217237204745215042365 1623081463951779455640887)
                ·
                  refine ⟨2434622195927669183461331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623081463951779455640887 2434622195927669183461331)
                  ·
                    refine ⟨3651933293891503775191997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2434622195927669183461331 3651933293891503775191997)
                    ·
                      refine ⟨1369474985209313915696999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3651933293891503775191997 1369474985209313915696999)
                      ·
                        rfl

theorem cell23_2667043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_2667043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667043 prefixEnd_2667043 := by exact prefixLift 2667043
  have htrace : WordTrace (prefixWord ++ tailWord_2667043) baseStart_2667043 baseEnd_2667043 := by
    simpa [prefixWord, tailWord_2667043, baseEnd_2667043] using wordTrace_append hprefix tailTrace_2667043
  have hstable : (prefixWord ++ tailWord_2667043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667043).length < 2 ^ (prefixWord ++ tailWord_2667043).sum := by decide
  have hdescent : baseEnd_2667043 < baseStart_2667043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667060 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2667060 : Nat := 118140960795 + 2667060 * 2 ^ 59
def prefixEnd_2667060 : Nat := 4983230072969 + 3 ^ 40 * 2667060 * 2
def baseEnd_2667060 : Nat := 1369483714380440349184421

theorem tailTrace_2667060 : CollatzResearch.WordTrace tailWord_2667060 prefixEnd_2667060 1369483714380440349184421 := by
  unfold tailWord_2667060
  simp only [CollatzResearch.WordTrace]
  refine ⟨48637834858852296214547317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64850446478469728286063089 48637834858852296214547317)
  ·
    refine ⟨4559797018017402770113811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48637834858852296214547317 4559797018017402770113811)
    ·
      refine ⟨6839695527026104155170717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4559797018017402770113811 6839695527026104155170717)
      ·
        refine ⟨2564885822634789058189019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6839695527026104155170717 2564885822634789058189019)
        ·
          refine ⟨3847328733952183587283529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564885822634789058189019 3847328733952183587283529)
          ·
            refine ⟨2885496550464137690462647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3847328733952183587283529 2885496550464137690462647)
            ·
              refine ⟨4328244825696206535693971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885496550464137690462647 4328244825696206535693971)
              ·
                refine ⟨6492367238544309803540957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328244825696206535693971 6492367238544309803540957)
                ·
                  refine ⟨2434637714454116176327859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6492367238544309803540957 2434637714454116176327859)
                  ·
                    refine ⟨3651956571681174264491789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2434637714454116176327859 3651956571681174264491789)
                    ·
                      refine ⟨1369483714380440349184421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3651956571681174264491789 1369483714380440349184421)
                      ·
                        rfl

theorem cell23_2667060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2667060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667060 prefixEnd_2667060 := by exact prefixLift 2667060
  have htrace : WordTrace (prefixWord ++ tailWord_2667060) baseStart_2667060 baseEnd_2667060 := by
    simpa [prefixWord, tailWord_2667060, baseEnd_2667060] using wordTrace_append hprefix tailTrace_2667060
  have hstable : (prefixWord ++ tailWord_2667060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667060).length < 2 ^ (prefixWord ++ tailWord_2667060).sum := by decide
  have hdescent : baseEnd_2667060 < baseStart_2667060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667066 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2]
def baseStart_2667066 : Nat := 118140960795 + 2667066 * 2 ^ 59
def prefixEnd_2667066 : Nat := 4983230072969 + 3 ^ 40 * 2667066 * 2
def baseEnd_2667066 : Nat := 1369486795264367325709393

theorem tailTrace_2667066 : CollatzResearch.WordTrace tailWord_2667066 prefixEnd_2667066 1369486795264367325709393 := by
  unfold tailWord_2667066
  simp only [CollatzResearch.WordTrace]
  refine ⟨24318972138920713863453263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64850592370455236969208701 24318972138920713863453263)
  ·
    refine ⟨36478458208381070795179895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24318972138920713863453263 36478458208381070795179895)
    ·
      refine ⟨54717687312571606192769843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36478458208381070795179895 54717687312571606192769843)
      ·
        refine ⟨82076530968857409289154765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54717687312571606192769843 82076530968857409289154765)
        ·
          refine ⟨30778699113321528483433037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82076530968857409289154765 30778699113321528483433037)
          ·
            refine ⟨11542012167495573181287389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30778699113321528483433037 11542012167495573181287389)
            ·
              refine ⟨4328254562810839942982771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11542012167495573181287389 4328254562810839942982771)
              ·
                refine ⟨6492381844216259914474157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328254562810839942982771 6492381844216259914474157)
                ·
                  refine ⟨2434643191581097467927809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6492381844216259914474157 2434643191581097467927809)
                  ·
                    refine ⟨1825982393685823100945857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2434643191581097467927809 1825982393685823100945857)
                    ·
                      refine ⟨1369486795264367325709393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1825982393685823100945857 1369486795264367325709393)
                      ·
                        rfl

theorem cell23_2667066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_2667066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667066 prefixEnd_2667066 := by exact prefixLift 2667066
  have htrace : WordTrace (prefixWord ++ tailWord_2667066) baseStart_2667066 baseEnd_2667066 := by
    simpa [prefixWord, tailWord_2667066, baseEnd_2667066] using wordTrace_append hprefix tailTrace_2667066
  have hstable : (prefixWord ++ tailWord_2667066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667066).length < 2 ^ (prefixWord ++ tailWord_2667066).sum := by decide
  have hdescent : baseEnd_2667066 < baseStart_2667066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667117 : List Nat := [1, 5, 1, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_2667117 : Nat := 118140960795 + 2667117 * 2 ^ 59
def prefixEnd_2667117 : Nat := 4983230072969 + 3 ^ 40 * 2667117 * 2
def baseEnd_2667117 : Nat := 1369512982777746626171659

theorem tailTrace_2667117 : CollatzResearch.WordTrace tailWord_2667117 prefixEnd_2667117 1369512982777746626171659 := by
  unfold tailWord_2667117
  simp only [CollatzResearch.WordTrace]
  refine ⟨97277748678498091163919605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64851832452332060775946403 97277748678498091163919605)
  ·
    refine ⟨9119788938609196046617463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97277748678498091163919605 9119788938609196046617463)
    ·
      refine ⟨13679683407913794069926195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9119788938609196046617463 13679683407913794069926195)
      ·
        refine ⟨20519525111870691104889293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13679683407913794069926195 20519525111870691104889293)
        ·
          refine ⟨7694821916951509164333485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20519525111870691104889293 7694821916951509164333485)
          ·
            refine ⟨2885558218856815936625057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7694821916951509164333485 2885558218856815936625057)
            ·
              refine ⟨2164168664142611952468793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2885558218856815936625057 2164168664142611952468793)
              ·
                refine ⟨1623126498106958964351595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2164168664142611952468793 1623126498106958964351595)
                ·
                  refine ⟨2434689747160438446527393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623126498106958964351595 2434689747160438446527393)
                  ·
                    refine ⟨1826017310370328834895545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2434689747160438446527393 1826017310370328834895545)
                    ·
                      refine ⟨1369512982777746626171659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826017310370328834895545 1369512982777746626171659)
                      ·
                        rfl

theorem cell23_2667117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_2667117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667117 prefixEnd_2667117 := by exact prefixLift 2667117
  have htrace : WordTrace (prefixWord ++ tailWord_2667117) baseStart_2667117 baseEnd_2667117 := by
    simpa [prefixWord, tailWord_2667117, baseEnd_2667117] using wordTrace_append hprefix tailTrace_2667117
  have hstable : (prefixWord ++ tailWord_2667117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667117).length < 2 ^ (prefixWord ++ tailWord_2667117).sum := by decide
  have hdescent : baseEnd_2667117 < baseStart_2667117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667139 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 1, 4, 2]
def baseStart_2667139 : Nat := 118140960795 + 2667139 * 2 ^ 59
def prefixEnd_2667139 : Nat := 4983230072969 + 3 ^ 40 * 2667139 * 2
def baseEnd_2667139 : Nat := 1369524279352145540096557

theorem tailTrace_2667139 : CollatzResearch.WordTrace tailWord_2667139 prefixEnd_2667139 1369524279352145540096557 := by
  unfold tailWord_2667139
  simp only [CollatzResearch.WordTrace]
  refine ⟨97278551084418388921220471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64852367389612259280813647 97278551084418388921220471)
  ·
    refine ⟨145917826626627583381830707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97278551084418388921220471 145917826626627583381830707)
    ·
      refine ⟨218876739939941375072746061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145917826626627583381830707 218876739939941375072746061)
      ·
        refine ⟨82078777477478015652279773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218876739939941375072746061 82078777477478015652279773)
        ·
          refine ⟨30779541554054255869604915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82078777477478015652279773 30779541554054255869604915)
          ·
            refine ⟨46169312331081383804407373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30779541554054255869604915 46169312331081383804407373)
            ·
              refine ⟨17313492124155518926652765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46169312331081383804407373 17313492124155518926652765)
              ·
                refine ⟨6492559546558319597494787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17313492124155518926652765 6492559546558319597494787)
                ·
                  refine ⟨9738839319837479396242181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6492559546558319597494787 9738839319837479396242181)
                  ·
                    refine ⟨1826032372469527386795409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9738839319837479396242181 1826032372469527386795409)
                    ·
                      refine ⟨1369524279352145540096557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826032372469527386795409 1369524279352145540096557)
                      ·
                        rfl

theorem cell23_2667139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_2667139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667139 prefixEnd_2667139 := by exact prefixLift 2667139
  have htrace : WordTrace (prefixWord ++ tailWord_2667139) baseStart_2667139 baseEnd_2667139 := by
    simpa [prefixWord, tailWord_2667139, baseEnd_2667139] using wordTrace_append hprefix tailTrace_2667139
  have hstable : (prefixWord ++ tailWord_2667139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667139).length < 2 ^ (prefixWord ++ tailWord_2667139).sum := by decide
  have hdescent : baseEnd_2667139 < baseStart_2667139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667249 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 4, 2, 3]
def baseStart_2667249 : Nat := 118140960795 + 2667249 * 2 ^ 59
def prefixEnd_2667249 : Nat := 4983230072969 + 3 ^ 40 * 2667249 * 2
def baseEnd_2667249 : Nat := 1369580762224140109721051

theorem tailTrace_2667249 : CollatzResearch.WordTrace tailWord_2667249 prefixEnd_2667249 1369580762224140109721051 := by
  unfold tailWord_2667249
  simp only [CollatzResearch.WordTrace]
  refine ⟨97282563114019877707724801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64855042076013251805149867 97282563114019877707724801)
  ·
    refine ⟨72961922335514908280793601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97282563114019877707724801 72961922335514908280793601)
    ·
      refine ⟨54721441751636181210595201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72961922335514908280793601 54721441751636181210595201)
      ·
        refine ⟨41041081313727135907946401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54721441751636181210595201 41041081313727135907946401)
        ·
          refine ⟨30780810985295351930959801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41041081313727135907946401 30780810985295351930959801)
          ·
            refine ⟨23085608238971513948219851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30780810985295351930959801 23085608238971513948219851)
            ·
              refine ⟨34628412358457270922329777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23085608238971513948219851 34628412358457270922329777)
              ·
                refine ⟨25971309268842953191747333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34628412358457270922329777 25971309268842953191747333)
                ·
                  refine ⟨4869620487908053723452625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25971309268842953191747333 4869620487908053723452625)
                  ·
                    refine ⟨3652215365931040292589469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4869620487908053723452625 3652215365931040292589469)
                    ·
                      refine ⟨1369580762224140109721051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3652215365931040292589469 1369580762224140109721051)
                      ·
                        rfl

theorem cell23_2667249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_2667249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667249 prefixEnd_2667249 := by exact prefixLift 2667249
  have htrace : WordTrace (prefixWord ++ tailWord_2667249) baseStart_2667249 baseEnd_2667249 := by
    simpa [prefixWord, tailWord_2667249, baseEnd_2667249] using wordTrace_append hprefix tailTrace_2667249
  have hstable : (prefixWord ++ tailWord_2667249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667249).length < 2 ^ (prefixWord ++ tailWord_2667249).sum := by decide
  have hdescent : baseEnd_2667249 < baseStart_2667249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
